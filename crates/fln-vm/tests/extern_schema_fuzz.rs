//! Seeded adversarial fuzz over the W5 extern row contract schema (bead
//! `franken_lean-pw6t`). The laws under test:
//!
//! 1. `load::parse` / `load::load` on malformed, truncated, binary, and mutated
//!    inputs never panic; every refusal is a typed [`ContractError`] with a
//!    non-empty message.
//! 2. The percent codec is an exact identity on its corpus (unicode included)
//!    and refuses every non-canonical spelling.
//! 3. `parse_row` under field-level mutation never panics, and any mutation
//!    that changes a decoded field value fails the schema laws or the row-root
//!    recompute — drift is a named refusal, never a pass.
//!
//! Deterministic: every case derives from one inline xorshift64 PRNG with a
//! fixed seed. No external crates; fln-vm is std-only.

#![forbid(unsafe_code)]

use fln_vm::extern_row::{
    Binder, CONTRACT_ROOT_DOMAIN, ContractError, EffectClass, ExternKind, ExternRow, ModeSupport,
    Ownership, PartitionClass, ROW_FIELD_ORDER, SafetyClass, framed_hash, parse_fields, parse_row,
    percent_decode, percent_encode, render_row,
};
use fln_vm::load;

const SYNTHETIC_MUTATION_CASES: u32 = 900;
const EMBEDDED_MUTATION_CASES: u32 = 450;
const BINARY_CASES: u32 = 300;
const CODEC_CASES: u32 = 400;
const CODEC_MUTATION_ATTEMPTS: u32 = 400;
const ROW_MUTATION_CASES: u32 = 800;
const TOTAL_SEEDED_CASES: u32 = SYNTHETIC_MUTATION_CASES
    + EMBEDDED_MUTATION_CASES
    + BINARY_CASES
    + CODEC_CASES
    + CODEC_MUTATION_ATTEMPTS
    + ROW_MUTATION_CASES;

/// xorshift64 with a forced-nonzero state: tiny, deterministic, dependency-free.
struct XorShift64(u64);

impl XorShift64 {
    fn new(seed: u64) -> Self {
        Self(seed | 1)
    }

    fn next_u64(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    /// Uniform-ish index in `0..n`; `n == 0` yields 0 (callers guard).
    fn below(&mut self, n: usize) -> usize {
        if n == 0 {
            return 0;
        }
        (self.next_u64() % n as u64) as usize
    }

    fn chance(&mut self, percent: u8) -> bool {
        (self.next_u64() % 100) < u64::from(percent)
    }
}

/// Every refusal on every path is a typed `ContractError` carrying a message;
/// a panic anywhere fails the test on its own.
fn expect_typed<T>(result: &Result<T, ContractError>, context: &str) {
    if let Err(error) = result {
        assert!(
            !error.message().is_empty(),
            "empty ContractError message for {context}"
        );
        assert!(!error.to_string().is_empty(), "empty Display for {context}");
        let _: &dyn std::error::Error = error;
    }
}

// ---------------------------------------------------------------------------
// A small synthetic contract in the exact ExternRowContractV1 shape. Row roots
// and the contract root are computed through the crate's own framing — nothing
// is hand-written.
// ---------------------------------------------------------------------------

const PROJECTION_PLACEHOLDER: &str = "projection kind=rust \
     path=crates/fln-vm/src/extern_table_generated.rs \
     template-root=fnv1a64:EXTERN_ROW_CONTRACT_ROOT";

fn binder(name: &str, info: &str, type_hash: &str) -> Binder {
    Binder {
        name: name.to_string(),
        info: info.to_string(),
        type_hash: type_hash.to_string(),
    }
}

#[allow(clippy::too_many_arguments)]
fn make_row(
    name: &str,
    kind: ExternKind,
    module: &str,
    levels: u32,
    arity: u32,
    telescope: Vec<Binder>,
    value_hash: &str,
    safety: SafetyClass,
    effect: EffectClass,
    partition: PartitionClass,
    ownership: Ownership,
    mode: ModeSupport,
    symbol: &str,
) -> ExternRow {
    let mut row = ExternRow {
        id: format!("extern:{name}"),
        name: name.to_string(),
        kind,
        module: module.to_string(),
        levels,
        arity,
        telescope,
        type_hash: "mix256:1:2:3:4".to_string(),
        value_hash: value_hash.to_string(),
        safety,
        attributes: "extern;reducibility=Lean.ReducibilityStatus.semireducible".to_string(),
        entry_class: "standard".to_string(),
        entry_scope: "all".to_string(),
        symbol: symbol.to_string(),
        effect,
        partition,
        ownership,
        mode,
        profile: "faithful,sound".to_string(),
        row_root: String::new(),
    };
    row.row_root = row.compute_row_root();
    row
}

fn synthetic_rows() -> Vec<ExternRow> {
    vec![
        make_row(
            "Fuzz.alpha",
            ExternKind::Defn,
            "Fuzz.Mod",
            1,
            2,
            vec![
                binder("a", "implicit", "mix256:10:20:30:40"),
                binder("x", "explicit", "mix256:50:60:70:80"),
            ],
            "mix256:5:6:7:8",
            SafetyClass::Safe,
            EffectClass::Pure,
            PartitionClass::ToolchainApi,
            Ownership::AbiSignature("(a: value) -> value".to_string()),
            ModeSupport::All,
            "lean_fuzz_alpha",
        ),
        make_row(
            "Fuzz.beta",
            ExternKind::Ctor,
            "Fuzz.Mod",
            0,
            1,
            vec![binder("self", "explicit", "mix256:11:22:33:44")],
            "mix256:9:10:11:12",
            SafetyClass::Partial,
            EffectClass::Io,
            PartitionClass::ToolchainApi,
            Ownership::DefaultRuleOwnedResult,
            ModeSupport::All,
            "lean_fuzz_beta",
        ),
        make_row(
            "Fuzz.gamma",
            ExternKind::Opaque,
            "Fuzz.Other",
            0,
            1,
            vec![binder("g", "explicit", "mix256:1:1:1:1")],
            "-",
            SafetyClass::Unsafe,
            EffectClass::Task,
            PartitionClass::LibraryCode,
            Ownership::ScalarRule,
            ModeSupport::Frontier,
            "lean_fuzz_gamma",
        ),
    ]
}

/// The synthetic contract text plus its rows. The header carries the exact
/// indexed lines `load::parse` inspects (schema, contract, reference,
/// observation-platform, row-count); the root is recomputed over the same
/// placeholder-projection body the real generator publishes under.
fn synthetic_contract() -> (String, Vec<ExternRow>) {
    let rows = synthetic_rows();
    let mut root_lines: Vec<String> = vec![
        "schema fln-extern-row-contract/1".to_string(),
        "contract ExternRowContractV1".to_string(),
        "hash fnv1a64-noncryptographic framing=u64le-length-prefixed".to_string(),
        "semantic-schema fln.extern-rows.semantic/1".to_string(),
        "telemetry-schema fln.extern-rows.telemetry/1".to_string(),
        "reference repo=fuzz/synthetic tag=v0.0.0".to_string(),
        "observation-platform linux-x86_64".to_string(),
        "row-count 3".to_string(),
        "symbol-count 3".to_string(),
        "input-root-fuzz=sha256:00".to_string(),
    ];
    root_lines.push("rows-begin".to_string());
    for row in &rows {
        root_lines.push(format!("row {}", render_row(row)));
    }
    root_lines.push("rows-end".to_string());
    root_lines.push(PROJECTION_PLACEHOLDER.to_string());
    let root = framed_hash(CONTRACT_ROOT_DOMAIN, root_lines.iter().map(String::as_str));
    let mut text = root_lines.join("\n");
    text.push('\n');
    text.push_str(&format!("contract-root {root}\n"));
    (text, rows)
}

// ---------------------------------------------------------------------------
// The mutation engine: byte flips, replacements, truncations, line drops/dups/
// swaps, escape mangling, random insertions/deletions, final-newline drops,
// and junk appends. Everything funnels through `from_utf8_lossy`, so the
// engine itself can never panic or produce non-&str input.
// ---------------------------------------------------------------------------

const JUNK: &[&str] = &[
    "%zz",
    "%2f",
    "%",
    "\u{0}",
    "key=",
    "=value",
    "row ",
    "contract-root fnv1a64:0000000000000000",
    "☃",
    "extern:",
    "  ",
    "\t",
    "rows-end",
    "mix256:",
];

fn mutate(text: &str, rng: &mut XorShift64) -> String {
    mutate_within(text, text.len(), rng)
}

/// The mutation engine with a byte limit: position-based operations land
/// strictly inside `text[..limit]`, so callers can confine drift to the
/// hashed region of a contract (everything through `rows-end`).
fn mutate_within(text: &str, limit: usize, rng: &mut XorShift64) -> String {
    let limit = limit.min(text.len());
    match rng.below(10) {
        0 => {
            // Flip one byte inside the limit.
            let mut bytes = text.as_bytes().to_vec();
            if limit == 0 {
                return text.to_string();
            }
            let pos = rng.below(limit);
            bytes[pos] ^= (rng.below(255) + 1) as u8;
            String::from_utf8_lossy(&bytes).into_owned()
        }
        1 => {
            // Replace one byte inside the limit (may be a no-op ~1/256).
            let mut bytes = text.as_bytes().to_vec();
            if limit == 0 {
                return text.to_string();
            }
            let pos = rng.below(limit);
            bytes[pos] = rng.below(256) as u8;
            String::from_utf8_lossy(&bytes).into_owned()
        }
        2 => {
            // Truncate at an arbitrary byte boundary.
            let mut bytes = text.as_bytes().to_vec();
            bytes.truncate(rng.below(bytes.len() + 1));
            String::from_utf8_lossy(&bytes).into_owned()
        }
        3 => {
            // Drop one line inside the limit.
            let mut lines: Vec<&str> = text[..limit].split_inclusive('\n').collect();
            if lines.is_empty() {
                return text.to_string();
            }
            lines.remove(rng.below(lines.len()));
            format!("{}{}", lines.concat(), &text[limit..])
        }
        4 => {
            // Duplicate one line inside the limit.
            let mut lines: Vec<&str> = text[..limit].split_inclusive('\n').collect();
            if lines.is_empty() {
                return text.to_string();
            }
            let at = rng.below(lines.len());
            let copy = lines[at];
            lines.insert(at, copy);
            format!("{}{}", lines.concat(), &text[limit..])
        }
        5 => {
            // Swap two lines inside the limit.
            let mut lines: Vec<&str> = text[..limit].split_inclusive('\n').collect();
            if lines.len() < 2 {
                return text.to_string();
            }
            let a = rng.below(lines.len());
            let b = rng.below(lines.len());
            lines.swap(a, b);
            format!("{}{}", lines.concat(), &text[limit..])
        }
        6 => {
            // Escape mangle: splice a junk escape token inside the limit.
            let mut bytes = text.as_bytes().to_vec();
            let pos = rng.below(limit.max(1));
            let junk = JUNK[rng.below(JUNK.len())].as_bytes();
            bytes.splice(pos..pos, junk.iter().copied());
            String::from_utf8_lossy(&bytes).into_owned()
        }
        7 => {
            // Insert 1..=8 random bytes inside the limit.
            let mut bytes = text.as_bytes().to_vec();
            let count = 1 + rng.below(8);
            for _ in 0..count {
                let pos = rng.below(limit.max(1).min(bytes.len() + 1));
                bytes.insert(pos, rng.below(256) as u8);
            }
            String::from_utf8_lossy(&bytes).into_owned()
        }
        8 => {
            // Delete 1..=16 bytes starting inside the limit.
            let mut bytes = text.as_bytes().to_vec();
            if limit == 0 {
                return text.to_string();
            }
            let start = rng.below(limit);
            let end = (start + 1 + rng.below(16)).min(bytes.len());
            bytes.drain(start..end);
            String::from_utf8_lossy(&bytes).into_owned()
        }
        _ => {
            // Drop the final newline, or append junk after it.
            if rng.chance(50) {
                text.trim_end_matches('\n').to_string()
            } else {
                format!("{text}{}", JUNK[rng.below(JUNK.len())])
            }
        }
    }
}

// ---------------------------------------------------------------------------
// 1. The synthetic contract: well-formed up to the population law (a 3-row
//    contract can never satisfy DECLARED_ROW_COUNT — that law is a schema
//    revision guard, and it is a typed refusal like every other).
// ---------------------------------------------------------------------------

#[test]
fn synthetic_contract_shape_and_population_law() {
    let (text, rows) = synthetic_contract();

    // Rows are self-certifying: render → parse is the identity.
    for row in &rows {
        assert_eq!(row.compute_row_root(), row.row_root);
        let parsed = parse_row(&render_row(row)).expect("synthetic row must parse");
        assert_eq!(&parsed, row);
    }

    // The contract root recomputes over the placeholder-projection body.
    let lines: Vec<&str> = text.split_terminator('\n').collect();
    let declared = lines
        .last()
        .and_then(|line| line.strip_prefix("contract-root "))
        .expect("synthetic contract ends with its contract-root");
    let recomputed = framed_hash(
        CONTRACT_ROOT_DOMAIN,
        lines[..lines.len() - 1].iter().copied(),
    );
    assert_eq!(declared, recomputed, "synthetic contract-root drifted");

    // The population law is the only thing between this text and a full parse:
    // every row parses, the declared count matches, then the census guard fires.
    let error = load::parse(&text).expect_err("3 rows must hit the population law");
    assert!(
        error.message().contains("row population"),
        "unexpected refusal: {}",
        error.message()
    );
    expect_typed(&load::load(&text), "synthetic baseline load");

    // Truncation sweep: every line prefix, then a byte stride across the body.
    let mut cases = 0_u32;
    for prefix_len in 0..lines.len() {
        let prefix = format!("{}\n", lines[..prefix_len].join("\n"));
        expect_typed(&load::parse(&prefix), "synthetic line truncation");
        expect_typed(&load::load(&prefix), "synthetic line truncation");
        cases += 1;
    }
    let mut cut = 0;
    while cut < text.len() {
        let prefix = String::from_utf8_lossy(&text.as_bytes()[..cut]).into_owned();
        expect_typed(&load::parse(&prefix), "synthetic byte truncation");
        cases += 1;
        cut += 97;
    }
    assert!(cases >= 30, "truncation sweep ran {cases} cases");
}

// ---------------------------------------------------------------------------
// 2. Seeded mutation fuzz over the synthetic contract.
// ---------------------------------------------------------------------------

#[test]
fn synthetic_contract_mutations_never_panic_and_refuse_typed() {
    let (text, _) = synthetic_contract();
    let mut rng = XorShift64::new(0x9E37_79B9_7F4A_7C15);
    let mut cases = 0_u32;
    let mut survived = 0_u32;
    for _ in 0..SYNTHETIC_MUTATION_CASES {
        let mut mutated = text.clone();
        for _ in 0..=rng.below(3) {
            mutated = mutate(&mutated, &mut rng);
        }
        expect_typed(&load::parse(&mutated), "synthetic mutation parse");
        expect_typed(&load::load(&mutated), "synthetic mutation load");
        if load::parse(&mutated).is_ok() {
            survived += 1;
        }
        cases += 1;
    }
    assert_eq!(cases, SYNTHETIC_MUTATION_CASES);
    assert_eq!(
        survived, 0,
        "a 3-row contract must always hit the population law"
    );
}

// ---------------------------------------------------------------------------
// 3. Seeded mutation + truncation fuzz over the real embedded contract. The
//    root law gives a complete decision procedure: byte-identical text loads,
//    anything else is a typed refusal.
// ---------------------------------------------------------------------------

#[test]
fn embedded_contract_mutations_never_panic_and_refuse_typed() {
    let text = load::embedded_contract_text();
    assert!(load::load(text).is_ok(), "the committed contract must load");
    // Confine position-based drift to the hashed region (everything through
    // `rows-end`); the projection line below it has its own exact law, covered
    // by `projection_line_law_is_exact`.
    let hashed_end = text
        .find("rows-end\n")
        .map_or(text.len(), |at| at + "rows-end\n".len());

    let mut rng = XorShift64::new(0xC0FF_EE15_5EED_0001);
    let mut cases = 0_u32;
    let mut noops = 0_u32;
    for _ in 0..EMBEDDED_MUTATION_CASES {
        let mut mutated = mutate_within(text, hashed_end, &mut rng);
        if rng.chance(40) {
            mutated = mutate_within(&mutated, hashed_end, &mut rng);
        }
        let result = load::load(&mutated);
        expect_typed(&result, "embedded mutation load");
        if mutated == text {
            // A no-op mutation (same-byte replace, identity swap, ...) must
            // still load — anything else would be a false refusal.
            assert!(result.is_ok(), "byte-identical text was refused");
            noops += 1;
        } else {
            // Every byte of the body is hashed and the terminal root is
            // recomputed, so any changed text is drift and must be refused.
            assert!(
                result.is_err(),
                "changed contract text loaded: the root law failed to fire"
            );
        }
        cases += 1;
    }
    assert_eq!(cases, EMBEDDED_MUTATION_CASES);
    assert!(
        noops <= cases / 20 + 4,
        "too many no-op mutations ({noops}/{cases}); the fuzz is not biting"
    );
}

#[test]
fn projection_line_law_is_exact() {
    let text = load::embedded_contract_text();
    let marker = "rows-end\n";
    let head_end = text.find(marker).map_or(0, |at| at + marker.len());
    let head = &text[..head_end];
    let rest = &text[head_end..];
    let root_at = rest
        .rfind("\ncontract-root ")
        .map_or(rest.len(), |at| at + 1);
    let root_line = &rest[root_at..];
    let declared = root_line
        .trim_end()
        .strip_prefix("contract-root ")
        .expect("terminal line is the contract-root");
    const PINNED_PATH: &str = "crates/fln-vm/src/extern_table_generated.rs";

    // The two accepted template-root spellings: the declared root (the pinned
    // form) and the generator's placeholder (the two-pass form).
    let placeholder = format!(
        "{head}projection kind=rust path={PINNED_PATH} \
         template-root=fnv1a64:EXTERN_ROW_CONTRACT_ROOT\n{root_line}"
    );
    assert!(
        load::load(&placeholder).is_ok(),
        "the placeholder template-root must load"
    );
    let pinned = format!(
        "{head}projection kind=rust path={PINNED_PATH} template-root={declared}\n{root_line}"
    );
    assert!(
        load::load(&pinned).is_ok(),
        "the declared template-root must load"
    );

    // Everything else about the projection region is exact and refused.
    let violations = [
        // A moved path.
        format!("{head}projection kind=rust path=elsewhere template-root={declared}\n{root_line}"),
        // A template-root that is neither the declared root nor the placeholder.
        format!(
            "{head}projection kind=rust path={PINNED_PATH} \
             template-root=fnv1a64:0000000000000000\n{root_line}"
        ),
        // A dropped projection line.
        format!("{head}{root_line}"),
        // An extra line in the projection region.
        format!("{head}note anything=unhashed\n{rest}"),
        // A missing projection field.
        format!("{head}projection kind=rust path={PINNED_PATH}\n{root_line}"),
        // A token that is not key=value.
        format!(
            "{head}projection kind=rust stray path={PINNED_PATH} template-root={declared}\n{root_line}"
        ),
    ];
    for bad in &violations {
        let result = load::load(bad);
        expect_typed(&result, "projection law violation");
        assert!(
            result.is_err(),
            "projection-law violation must be refused: {bad:?}"
        );
    }

    // The terminal contract-root is content: drift one nibble and the
    // recompute law fires; move a root line earlier and the placement law fires.
    let last = declared.chars().last().expect("root carries hex digits");
    let flipped = if last == '0' { '1' } else { '0' };
    let drifted_declared = format!("{}{flipped}", &declared[..declared.len() - 1]);
    let drifted = format!("{head}{rest}contract-root {drifted_declared}\n");
    let result = load::load(&drifted);
    expect_typed(&result, "contract-root nibble drift");
    assert!(
        result.is_err(),
        "a drifted contract-root must be refused: {drifted_declared:?}"
    );
    let misplaced = format!("{head}contract-root fnv1a64:0000000000000000\n{rest}");
    let result = load::load(&misplaced);
    expect_typed(&result, "early contract-root");
    assert!(
        result.is_err(),
        "a contract-root before the final line must be refused"
    );
}

#[test]
fn embedded_contract_truncations_are_typed_refusals() {
    let text = load::embedded_contract_text();
    let lines: Vec<&str> = text.split_terminator('\n').collect();
    let mut cases = 0_u32;

    // Drop k trailing lines (removes the root, then rows, then the header).
    for drop in 1..=40 {
        let prefix = format!("{}\n", lines[..lines.len() - drop].join("\n"));
        let result = load::load(&prefix);
        expect_typed(&result, "embedded trailing truncation");
        assert!(result.is_err(), "dropping {drop} trailing lines loaded");
        cases += 1;
    }
    // Drop k leading lines (schema/name/reference laws).
    for drop in 1..10 {
        let suffix = format!("{}\n", lines[drop..].join("\n"));
        let result = load::load(&suffix);
        expect_typed(&result, "embedded leading truncation");
        assert!(result.is_err(), "dropping {drop} leading lines loaded");
        cases += 1;
    }
    // Byte-stride truncation across the whole body.
    let stride = text.len() / 30;
    let mut cut = stride;
    while cut < text.len() {
        let prefix = String::from_utf8_lossy(&text.as_bytes()[..cut]).into_owned();
        let result = load::load(&prefix);
        expect_typed(&result, "embedded byte truncation");
        assert!(result.is_err(), "byte truncation at {cut} loaded");
        cases += 1;
        cut += stride;
    }
    assert!(cases >= 75, "truncation sweep ran {cases} cases");
}

// ---------------------------------------------------------------------------
// 4. Pure binary and token-soup garbage.
// ---------------------------------------------------------------------------

#[test]
fn binary_garbage_never_panics_and_refuses_typed() {
    let mut rng = XorShift64::new(0xB1A0_5EED_F00D_1234);
    let alphabet: &[u8] = b"abcdef=%\n \t\x00\xff\xc3(schema)row-contract-root:1";
    let mut cases = 0_u32;
    for _ in 0..BINARY_CASES {
        let len = rng.below(513);
        let mut bytes = Vec::with_capacity(len);
        for _ in 0..len {
            if rng.chance(70) {
                bytes.push(alphabet[rng.below(alphabet.len())]);
            } else {
                bytes.push(rng.below(256) as u8);
            }
        }
        let text = String::from_utf8_lossy(&bytes).into_owned();
        expect_typed(&load::parse(&text), "binary garbage parse");
        expect_typed(&load::load(&text), "binary garbage load");
        cases += 1;
    }
    assert_eq!(cases, BINARY_CASES);
}

// ---------------------------------------------------------------------------
// 5. The percent codec: exact round-trip identity over a seeded unicode
//    corpus, canonical fixed point, and refusal of every non-canonical
//    spelling.
// ---------------------------------------------------------------------------

const POOL: &[char] = &[
    'a', 'Z', '0', '-', '.', '_', '~', '/', ':', '$', '%', ' ', 'é', '☃', '中', '\u{0}', '\n', '=',
    ';', '&', '+', '\t',
];

fn seeded_string(rng: &mut XorShift64, max_len: usize) -> String {
    let len = rng.below(max_len + 1);
    let mut value = String::new();
    for _ in 0..len {
        value.push(POOL[rng.below(POOL.len())]);
    }
    value
}

#[test]
fn percent_codec_round_trip_identity() {
    let mut rng = XorShift64::new(0x5EED_CAFE_0000_0002);
    let mut cases = 0_u32;
    for _ in 0..CODEC_CASES {
        let value = seeded_string(&mut rng, 40);
        let encoded = percent_encode(&value);
        let decoded = percent_decode(&encoded).expect("encode output must decode");
        assert_eq!(decoded, value, "decode∘encode broke for {value:?}");
        assert_eq!(
            percent_encode(&decoded),
            encoded,
            "encode is not the canonical fixed point for {value:?}"
        );
        cases += 1;
    }
    assert_eq!(cases, CODEC_CASES);
}

#[test]
fn percent_codec_refuses_noncanonical_spellings() {
    // Decode-level refusals: truncated escapes, invalid hex, non-UTF-8 bytes.
    for bad in ["%", "%4", "%zz", "%G0", "%ff", "%FF", "a%"] {
        let result = percent_decode(bad);
        expect_typed(&result, bad);
        assert!(result.is_err(), "percent_decode accepted {bad:?}");
    }
    // Field-level refusals: spellings that decode but re-encode differently
    // (lowercase hex, escapes of safe bytes), plus raw structure breaks.
    for bad in [
        "k=%2f",
        "k=%41",
        "k=%7E",
        "k=%c3%a9",
        "k=%e4%b8%ad",
        "k=a b",
        "k=",
        "=v",
        "a=1 a=2",
        "k",
        "k==v",
    ] {
        let result = parse_fields(bad);
        expect_typed(&result, bad);
        assert!(result.is_err(), "parse_fields accepted {bad:?}");
    }
    // Canonical spellings of unsafe bytes (including NUL) DO round-trip; the
    // schema layer — not the codec — refuses them in row fields (see the row
    // fuzz, where "%00" as a field value is always a typed refusal).
    for (text, expected) in [
        ("k=%C3%A9", "é"),
        ("k=%00", "\u{0}"),
        ("k=%3D", "="),
        ("k=abc-._~/:$", "abc-._~/:$"),
    ] {
        let fields = parse_fields(text).expect("canonical spelling must parse");
        assert_eq!(fields.get("k").map(String::as_str), Some(expected));
    }

    // Seeded lowercase-hex and truncated-escape fuzz over the encoded corpus.
    let mut rng = XorShift64::new(0x5EED_CAFE_0000_0003);
    let mut attempts = 0_u32;
    let mut lowered = 0_u32;
    let mut truncated = 0_u32;
    for _ in 0..CODEC_MUTATION_ATTEMPTS {
        let encoded = percent_encode(&seeded_string(&mut rng, 24));
        let bytes = encoded.as_bytes();
        let escapes: Vec<usize> = bytes
            .iter()
            .enumerate()
            .filter_map(|(i, b)| (*b == b'%').then_some(i))
            .collect();
        if escapes.is_empty() {
            continue;
        }
        let at = escapes[rng.below(escapes.len())];
        if rng.chance(50) {
            // Lowercase one uppercase hex digit inside this escape.
            let digits: Vec<usize> = [at + 1, at + 2]
                .into_iter()
                .filter(|&i| i < bytes.len() && bytes[i].is_ascii_uppercase())
                .collect();
            if digits.is_empty() {
                continue;
            }
            let mut mangled = bytes.to_vec();
            let digit = digits[rng.below(digits.len())];
            mangled[digit] = mangled[digit].to_ascii_lowercase();
            let mangled = String::from_utf8_lossy(&mangled).into_owned();
            let result = parse_fields(&format!("k={mangled}"));
            expect_typed(&result, "lowercase hex escape");
            assert!(
                result.is_err(),
                "lowercase hex escape accepted: {mangled:?}"
            );
            lowered += 1;
        } else {
            // Cut the escape short: after the '%' or after one hex digit.
            let cut = at + 1 + rng.below(2);
            let mangled = &encoded[..cut];
            let result = parse_fields(&format!("k={mangled}"));
            expect_typed(&result, "truncated escape");
            assert!(result.is_err(), "truncated escape accepted: {mangled:?}");
            truncated += 1;
        }
        attempts += 1;
    }
    assert!(
        lowered >= 50 && truncated >= 50,
        "codec mutation fuzz bit too rarely: {lowered} lowered, {truncated} truncated \
         ({attempts} attempts)"
    );
}

// ---------------------------------------------------------------------------
// 6. parse_fields structural refusals, spelled out one by one.
// ---------------------------------------------------------------------------

#[test]
fn parse_fields_refuses_duplicates_empties_and_bad_tokens() {
    for bad in [
        "a=1 a=2", // duplicate, different values
        "a=1 a=1", // duplicate, identical values
        "a=",      // empty value
        "=b",      // empty key
        "a= b=1",  // empty value then a valid field
        "a b=1",   // a bare token
        "a==b",    // decodes to "=b", which re-encodes %3Db
    ] {
        let result = parse_fields(bad);
        expect_typed(&result, bad);
        assert!(result.is_err(), "parse_fields accepted {bad:?}");
    }
    let duplicate = parse_fields("a=1 a=2").expect_err("duplicate must be refused");
    assert!(
        duplicate.message().contains("duplicate"),
        "duplicate refusal should name itself: {}",
        duplicate.message()
    );
    // The empty line is the empty map, not an error.
    assert!(parse_fields("").is_ok());
}

// ---------------------------------------------------------------------------
// 7. parse_row under field-level mutation: the decision procedure is exact.
//    `parse_fields` refusing ⇒ parse_row refuses; identical decoded field map
//    ⇒ identical row; any changed field value ⇒ schema or row-root refusal.
// ---------------------------------------------------------------------------

const ROW_VALUE_JUNK: &[&str] = &[
    "",
    "zzz",
    "%00",
    "%zz",
    "a b",
    "007",
    "-1",
    "wobbly",
    "fnv1a64:0000000000000000",
    "mix256:",
    "extern:",
    "rule(bogus)",
    "abi()",
    "%2f",
    "999999999999999999999999",
];

fn mutate_row_line(body: &str, rng: &mut XorShift64) -> String {
    let mut tokens: Vec<String> = body.split(' ').map(str::to_string).collect();
    if tokens.is_empty() {
        return body.to_string();
    }
    match rng.below(8) {
        0 => {
            // Replace one field's value with junk.
            let i = rng.below(tokens.len());
            let key = tokens[i].split('=').next().unwrap_or("x").to_string();
            tokens[i] = format!("{key}={}", ROW_VALUE_JUNK[rng.below(ROW_VALUE_JUNK.len())]);
        }
        1 => {
            // Flip one byte inside a token (ASCII-safe, always a change).
            let i = rng.below(tokens.len());
            let mut bytes = tokens[i].clone().into_bytes();
            let pos = rng.below(bytes.len());
            bytes[pos] = if bytes[pos] == b'a' { b'b' } else { b'a' };
            tokens[i] = String::from_utf8_lossy(&bytes).into_owned();
        }
        2 => {
            // Drop one field.
            tokens.remove(rng.below(tokens.len()));
        }
        3 => {
            // Duplicate one field at a random slot.
            let i = rng.below(tokens.len());
            let copy = tokens[i].clone();
            let at = rng.below(tokens.len() + 1);
            tokens.insert(at, copy);
        }
        4 => {
            // Swap two fields (decoded map unchanged ⇒ must still parse).
            if tokens.len() >= 2 {
                let a = rng.below(tokens.len());
                let b = rng.below(tokens.len());
                tokens.swap(a, b);
            }
        }
        5 => {
            // Single-nibble drift on the stored row-root.
            if let Some(i) = tokens
                .iter()
                .position(|t| t.starts_with("row-root=fnv1a64:"))
            {
                let mut bytes = tokens[i].clone().into_bytes();
                if let Some(last) = bytes.last_mut() {
                    *last = if *last == b'0' { b'1' } else { b'0' };
                }
                tokens[i] = String::from_utf8_lossy(&bytes).into_owned();
            }
        }
        6 => {
            // Rename a key to an unknown field.
            let i = rng.below(tokens.len());
            let value = tokens[i]
                .split_once('=')
                .map(|(_, value)| value.to_string())
                .unwrap_or_default();
            tokens[i] = format!("zz-{i}={value}");
        }
        _ => {
            // Append an unknown field.
            tokens.push(format!("extra{}=1", rng.below(10)));
        }
    }
    tokens.join(" ")
}

#[test]
fn parse_row_field_mutations_fail_schema_or_root() {
    let rows = synthetic_rows();
    let mut rng = XorShift64::new(0xD15E_A5E5_0000_0003);
    let mut cases = 0_u32;
    let mut semantic_noops = 0_u32;
    for _ in 0..ROW_MUTATION_CASES {
        let row = &rows[rng.below(rows.len())];
        let body = render_row(row);
        let original_map = parse_fields(&body).expect("baseline row fields must parse");
        let mutated = mutate_row_line(&body, &mut rng);
        let row_result = parse_row(&mutated);
        match parse_fields(&mutated) {
            Err(_) => {
                expect_typed(&row_result, "row field mutation (fields refused)");
                assert!(
                    row_result.is_err(),
                    "field-level refusal must propagate: {mutated:?}"
                );
            }
            Ok(map) if map == original_map => {
                // Reordering is semantically null: same decoded fields, same row.
                let parsed = row_result.expect("identical field map must still parse");
                assert_eq!(&parsed, row, "field reorder changed the row");
                semantic_noops += 1;
            }
            Ok(_) => {
                // Any changed decoded field value is schema drift or root drift.
                expect_typed(&row_result, "row field mutation (value drift)");
                assert!(
                    row_result.is_err(),
                    "changed field map must fail schema or root recompute: {mutated:?}"
                );
            }
        }
        cases += 1;
    }
    assert_eq!(cases, ROW_MUTATION_CASES);
    assert!(
        semantic_noops < cases / 2,
        "fuzz produced too many no-ops ({semantic_noops}/{cases})"
    );
}

#[test]
fn parse_row_detects_single_nibble_root_drift() {
    const HEX: &[char] = &[
        '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f',
    ];
    let mut cases = 0_u32;
    for row in synthetic_rows() {
        let body = render_row(&row);
        let original = row.row_root.chars().last().expect("root has hex digits");
        for &nibble in HEX {
            if nibble == original {
                continue;
            }
            let drifted = format!("{}{}", &body[..body.len() - 1], nibble);
            let result = parse_row(&drifted);
            expect_typed(&result, "nibble drift");
            assert!(
                result.is_err(),
                "single-nibble root drift must be refused: {drifted:?}"
            );
            cases += 1;
        }
    }
    assert_eq!(cases, 45, "3 rows × 15 drifted nibbles");
}

#[test]
fn row_field_order_is_the_schema() {
    assert_eq!(ROW_FIELD_ORDER.len(), 20);
    assert_eq!(ROW_FIELD_ORDER[0], "id");
    assert_eq!(ROW_FIELD_ORDER[19], "row-root");
}

// ---------------------------------------------------------------------------
// 8. The suite's seeded budget, as a number the CI output can attest.
// ---------------------------------------------------------------------------

#[test]
fn seeded_case_budget_is_met() {
    let budget: u32 = [
        SYNTHETIC_MUTATION_CASES,
        EMBEDDED_MUTATION_CASES,
        BINARY_CASES,
        CODEC_CASES,
        CODEC_MUTATION_ATTEMPTS,
        ROW_MUTATION_CASES,
    ]
    .iter()
    .sum();
    assert_eq!(budget, TOTAL_SEEDED_CASES);
    assert!(budget >= 2000, "seeded case budget shrank: {budget}");
}
