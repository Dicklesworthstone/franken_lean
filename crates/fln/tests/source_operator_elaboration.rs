//! Operator notation elaborates as the pin's `binop%`/`binrel%`/`unop%`/
//! `rightact%` expression-tree elaborator (`Lean.Elab.Extra`), against the
//! pinned Reference's own `Init.Prelude`, `Init.Coe` and `Init.Notation`
//! admitted through the council (bead `franken_lean-z8j.1.11`).
//!
//! Every expected term below is the pinned Reference's own output, copied
//! verbatim. It was produced by running the pin as a fixture generator (D8
//! capacity 2), never by anything this test executes:
//!
//! ```text
//! ulimit -v 40000000
//! ~/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean fixtures.lean
//! ```
//!
//! where `fixtures.lean` is `prelude`, `import Init.Notation`,
//! `set_option pp.all true`, the `FIXTURES` declarations of this file, and
//! one `#print fNN` per declaration. The negative fixtures were run the same
//! way and their refusal stage is recorded beside each one.
//!
//! Typed SKIP without the pin; `FLN_REQUIRE_REFERENCE=1` makes absence fail.

#![forbid(unsafe_code)]

use std::path::{Path, PathBuf};

use fln::source_check::modules::imported::SourceOleanImportLimits;
use fln::{
    Budget, Engine, EngineAdmissionLimits, EngineExecutionError, Environment, KVMap, Name,
    NatDefinitionFrontendError, OleanCheckLimits, OleanModuleInput, Outcome, SourceCheckError,
    SourceCheckLimits, SourceFileCheck,
};
use fln_core::expr::{BinderInfo, Expr, ExprNode, Literal, NatLit};
use fln_core::level::{Level, LevelView};
use fln_elab::NatDefinitionElabError;
use fln_elab::source::SourceInferenceError;
use fln_env::constants::ConstantInfo;

const STACK: usize = 256 * 1024 * 1024;

fn pinned_lib() -> Option<PathBuf> {
    let lib = std::env::var_os("FLN_REFERENCE_LIB")
        .map(PathBuf::from)
        .or_else(|| {
            std::env::var_os("HOME").map(|home| {
                PathBuf::from(home).join(".elan/toolchains/leanprover--lean4---v4.32.0/lib/lean")
            })
        })
        .filter(|lib| lib.is_dir());
    assert!(
        lib.is_some() || std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
        "FLN_REQUIRE_REFERENCE is set but the pinned Reference lib/lean is absent"
    );
    lib
}

fn read_parts(lib: &Path, module: &str) -> [Vec<u8>; 3] {
    let base = module
        .split('.')
        .fold(lib.to_path_buf(), |path, part| path.join(part))
        .with_extension("olean");
    let read = |path: PathBuf| std::fs::read(&path).expect("pinned olean part");
    [
        read(base.clone()),
        read(base.with_extension("olean.server")),
        read(base.with_extension("olean.private")),
    ]
}

/// Admit the pinned modules through the council, then activate their class,
/// instance and default-instance journals for source elaboration.
fn import_modules(lib: &Path, modules: &[&str], root: &str) -> Engine {
    let names: Vec<Name> = modules
        .iter()
        .map(|module| Name::from_components(module.split('.')))
        .collect();
    let parts: Vec<[Vec<u8>; 3]> = modules
        .iter()
        .map(|module| read_parts(lib, module))
        .collect();
    let inputs: Vec<OleanModuleInput<'_>> = names
        .iter()
        .zip(&parts)
        .map(|(name, [exported, server, private])| OleanModuleInput {
            name,
            artifact: exported,
            server_artifact: Some(server),
            private_artifact: Some(private),
        })
        .collect();
    let limits = SourceOleanImportLimits::new(OleanCheckLimits::new(
        256 * 1024 * 1024,
        Budget::for_stack_bytes(STACK),
    ));
    match Engine::from_environment(Environment::new()).import_olean_modules_for_source(
        &inputs,
        &[Name::from_components(root.split('.'))],
        &KVMap::new(),
        limits,
    ) {
        Ok(Outcome::Complete(imported)) => imported.engine,
        other => panic!("the pinned modules pass the council: {other:?}"),
    }
}

fn check(engine: &Engine, source: &str) -> Result<Outcome<SourceFileCheck>, SourceCheckError> {
    engine.check_source_files(
        &[source.as_bytes()],
        &KVMap::new(),
        SourceCheckLimits::new(EngineAdmissionLimits::new(Budget::for_stack_bytes(STACK))),
    )
}

fn on_a_big_stack<T: Send + 'static>(work: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new()
        .stack_size(STACK)
        .spawn(work)
        .expect("spawn the checking thread")
        .join()
        .expect("the checking thread completes")
}

/// A reader for exactly the `pp.all` forms these fixtures print: explicit
/// constants with universe instances, `fun`/Π binder groups, `nat_lit`,
/// `Prop`, bound variables and application by juxtaposition.
struct PinTerm<'a> {
    tokens: Vec<&'a str>,
    at: usize,
}

impl<'a> PinTerm<'a> {
    fn parse(text: &'a str) -> Expr {
        let mut tokens = Vec::new();
        let bytes = text.as_bytes();
        let mut start = None;
        let mut i = 0;
        while i < bytes.len() {
            let c = text[i..].chars().next().unwrap();
            let single = matches!(c, '(' | ')' | ':' | '@' | '→');
            if c.is_whitespace() || single {
                if let Some(s) = start.take() {
                    tokens.push(&text[s..i]);
                }
                if single {
                    tokens.push(&text[i..i + c.len_utf8()]);
                }
            } else if c == '{' {
                // A universe instance `.{0, 0, 0}` belongs to its constant's token.
                assert!(start.is_some() && text[..i].ends_with('.'), "stray brace");
                i = text[i..].find('}').expect("closed universe instance") + i + 1;
                continue;
            } else if start.is_none() {
                start = Some(i);
            }
            i += c.len_utf8();
        }
        if let Some(s) = start {
            tokens.push(&text[s..]);
        }
        let mut reader = PinTerm { tokens, at: 0 };
        let term = reader.term(&mut Vec::new());
        assert_eq!(reader.at, reader.tokens.len(), "trailing pin tokens");
        term
    }

    fn peek(&self) -> Option<&'a str> {
        self.tokens.get(self.at).copied()
    }

    fn next(&mut self) -> &'a str {
        let token = self.tokens[self.at];
        self.at += 1;
        token
    }

    fn expect(&mut self, token: &str) {
        assert_eq!(self.next(), token, "pin term token");
    }

    fn binder_group(&mut self, scope: &mut Vec<String>) -> Vec<(String, Expr)> {
        self.expect("(");
        let mut names = Vec::new();
        while self.peek() != Some(":") {
            names.push(self.next().to_owned());
        }
        self.expect(":");
        let type_ = self.term(scope);
        self.expect(")");
        let mut group = Vec::new();
        for name in names {
            // Each name in a group sees the same domain, shifted past its
            // earlier siblings (`(a b : Nat)` repeats the closed `Nat`).
            group.push((name.clone(), type_.clone()));
            scope.push(name);
        }
        group
    }

    fn is_binder_group(&self) -> bool {
        if self.peek() != Some("(") {
            return false;
        }
        let mut at = self.at + 1;
        while let Some(token) = self.tokens.get(at) {
            match *token {
                ":" => return at > self.at + 1,
                "(" | ")" | "@" | "→" => return false,
                _ => at += 1,
            }
        }
        false
    }

    fn term(&mut self, scope: &mut Vec<String>) -> Expr {
        if self.peek() == Some("fun") {
            self.next();
            let depth = scope.len();
            let mut binders = Vec::new();
            while self.peek() != Some("=>") {
                binders.extend(self.binder_group(scope));
            }
            self.expect("=>");
            let mut body = self.term(scope);
            scope.truncate(depth);
            for (name, type_) in binders.into_iter().rev() {
                body = Expr::lam(
                    Name::from_components([name.as_str()]),
                    type_,
                    body,
                    BinderInfo::Default,
                );
            }
            return body;
        }
        if self.is_binder_group() {
            let depth = scope.len();
            let binders = self.binder_group(scope);
            self.expect("→");
            let mut body = self.term(scope);
            scope.truncate(depth);
            for (name, type_) in binders.into_iter().rev() {
                body = Expr::forall_e(
                    Name::from_components([name.as_str()]),
                    type_,
                    body,
                    BinderInfo::Default,
                );
            }
            return body;
        }
        let mut head = self.atom(scope);
        while let Some(token) = self.peek() {
            if matches!(token, ")" | "→" | "=>") {
                break;
            }
            head = Expr::app(head, self.atom(scope));
        }
        head
    }

    fn atom(&mut self, scope: &mut Vec<String>) -> Expr {
        match self.next() {
            "(" => {
                if self.peek() == Some("nat_lit") {
                    self.next();
                    let value: u64 = self.next().parse().expect("nat_lit value");
                    self.expect(")");
                    return Expr::lit(Literal::Nat(NatLit::from_u64(value)));
                }
                let term = self.term(scope);
                self.expect(")");
                term
            }
            "@" => self.constant(),
            "Prop" => Expr::sort(Level::zero()),
            token => {
                if let Some(index) = scope.iter().rev().position(|name| name == token) {
                    return Expr::bvar(u32::try_from(index).unwrap()).unwrap();
                }
                self.at -= 1;
                self.constant()
            }
        }
    }

    fn constant(&mut self) -> Expr {
        let token = self.next();
        let (name, levels) = match token.split_once(".{") {
            Some((name, levels)) => (
                name,
                levels
                    .trim_end_matches('}')
                    .split(',')
                    .map(|level| {
                        let succs: u32 = level.trim().parse().expect("numeral universe");
                        (0..succs).fold(Level::zero(), |level, _| level.succ().unwrap())
                    })
                    .collect(),
            ),
            None => (token, Vec::new()),
        };
        Expr::const_(Name::from_components(name.split('.')), levels)
    }
}

/// Render an elaborated term in the pin's `pp.all` shape, for diagnostics only.
fn render(term: &Expr, scope: &mut Vec<String>) -> String {
    match term.node() {
        ExprNode::BVar { idx } => scope
            .iter()
            .rev()
            .nth(usize::try_from(*idx).unwrap())
            .cloned()
            .unwrap_or_else(|| format!("#{idx}")),
        ExprNode::Const { name, levels } => {
            let levels: Vec<String> = levels.iter().map(render_level).collect();
            if levels.is_empty() {
                format!("@{}", name.to_display_string())
            } else {
                format!("@{}.{{{}}}", name.to_display_string(), levels.join(", "))
            }
        }
        ExprNode::App { f, a } => format!("({} {})", render(f, scope), render(a, scope)),
        ExprNode::Lam {
            binder_name,
            binder_type,
            body,
            ..
        } => {
            let domain = render(binder_type, scope);
            scope.push(binder_name.to_display_string());
            let body = render(body, scope);
            scope.pop();
            format!(
                "(fun ({} : {domain}) => {body})",
                binder_name.to_display_string()
            )
        }
        ExprNode::ForallE {
            binder_name,
            binder_type,
            body,
            ..
        } => {
            let domain = render(binder_type, scope);
            scope.push(binder_name.to_display_string());
            let body = render(body, scope);
            scope.pop();
            format!(
                "(({} : {domain}) → {body})",
                binder_name.to_display_string()
            )
        }
        ExprNode::Lit {
            literal: Literal::Nat(value),
        } => format!("(nat_lit {value:?})"),
        ExprNode::Sort { level } => format!("Sort {}", render_level(level)),
        other => format!("{other:?}"),
    }
}

fn render_level(level: &Level) -> String {
    let mut succ = 0;
    let mut level = level;
    loop {
        match level.view() {
            LevelView::Zero => return succ.to_string(),
            LevelView::Succ(inner) => {
                succ += 1;
                level = inner;
            }
            _ => return format!("{level:?}+{succ}"),
        }
    }
}

/// The fixture declarations, each paired with the pin's `#print` output for
/// its type and value (`def fNN : TYPE :=` then `VALUE`).
const FIXTURES: &[(&str, &str, &str)] = &[
    (
        "def f01 (n : Nat) : Nat := n + 1",
        "(n : Nat) → Nat",
        "fun (n : Nat) =>
  @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) n
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))",
    ),
    (
        "def f02 (n : Nat) : Nat := 1 + n",
        "(n : Nat) → Nat",
        "fun (n : Nat) =>
  @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) n",
    ),
    (
        "def f03 (i : Nat) : Nat := 0 + i",
        "(i : Nat) → Nat",
        "fun (i : Nat) =>
  @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) i",
    ),
    (
        "def f04 (a b : Nat) : Nat := a * b - a / b % 3",
        "(a b : Nat) → Nat",
        "fun (a b : Nat) =>
  @HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat)
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a b)
    (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod)
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) a b)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))",
    ),
    (
        "def f05 (n : Nat) : Nat := 2 ^ n",
        "(n : Nat) → Nat",
        "fun (n : Nat) =>
  @HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat))
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) n",
    ),
    (
        "def f06 (n : Nat) : Nat := n ^ 2 + 1",
        "(n : Nat) → Nat",
        "fun (n : Nat) =>
  @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@instPowNat.{0} Nat instNatPowNat)) n
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))",
    ),
    (
        "def f07 := 2 + 3 * 4",
        "Nat",
        "@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
  (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
    (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))",
    ),
    (
        "def f08 (a b : Nat) : Bool := a == b + 1",
        "(a b : Nat) → Bool",
        "fun (a b : Nat) =>
  @BEq.beq.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat) a
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))",
    ),
    (
        "def f09 (a : Nat) : Prop := a + 1 = 2 * a",
        "(a : Nat) → Prop",
        "fun (a : Nat) =>
  @Eq.{1} Nat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) a)",
    ),
    (
        "def f10 (a b : Nat) : Prop := a < b + 1",
        "(a b : Nat) → Prop",
        "fun (a b : Nat) =>
  @LT.lt.{0} Nat instLTNat a
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) b
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))",
    ),
    (
        "def f11 (a b : Nat) : Prop := a * 2 <= b",
        "(a b : Nat) → Prop",
        "fun (a b : Nat) =>
  @LE.le.{0} Nat instLENat
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat) a
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    b",
    ),
    (
        "def f12 (a : Nat) : Prop := 1 < a",
        "(a : Nat) → Prop",
        "fun (a : Nat) => @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) a",
    ),
    (
        "def f13 (a b c : Nat) : Nat := (a + b) * (c - 1)",
        "(a b c : Nat) → Nat",
        "fun (a b c : Nat) =>
  @HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) a b)
    (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) c
      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))",
    ),
    (
        "def f14 (a : Nat) : Bool := 3 == a",
        "(a : Nat) → Bool",
        "fun (a : Nat) =>
  @BEq.beq.{0} Nat (@instBEqOfDecidableEq.{0} Nat instDecidableEqNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) a",
    ),
    (
        "def f15 : Prop := 2 + 2 = 4",
        "Prop",
        "@Eq.{1} Nat
  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))",
    ),
    (
        "def f16 (a : Nat) : Nat := a % 2 + a / 2 * 2",
        "(a : Nat) → Nat",
        "fun (a : Nat) =>
  @HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
    (@HMod.hMod.{0, 0, 0} Nat Nat Nat (@instHMod.{0} Nat Nat.instMod) a
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HDiv.hDiv.{0, 0, 0} Nat Nat Nat (@instHDiv.{0} Nat Nat.instDiv) a
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))",
    ),
];

fn declaration_name(source: &str) -> &str {
    source
        .strip_prefix("def ")
        .and_then(|rest| rest.split_whitespace().next())
        .expect("fixture declaration name")
}

#[test]
fn operator_trees_elaborate_to_the_pins_terms() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
        return;
    };
    on_a_big_stack(move || {
        let base = import_modules(
            &lib,
            &["Init.Prelude", "Init.Coe", "Init.Notation"],
            "Init.Notation",
        );
        let mut source = String::new();
        for (declaration, _, _) in FIXTURES {
            source.push_str(declaration);
            source.push('\n');
        }
        let checked = match check(&base, &source) {
            Ok(Outcome::Complete(checked)) => checked,
            other => panic!("fixtures must elaborate: {other:?}"),
        };
        let mut mismatches = Vec::new();
        for (declaration, type_text, value_text) in FIXTURES {
            let name = declaration_name(declaration);
            let Some(ConstantInfo::Defn(info)) = checked
                .engine
                .environment()
                .find(&Name::from_components([name]))
            else {
                panic!("expected admitted definition {name}");
            };
            let expected_type = PinTerm::parse(type_text);
            let expected_value = PinTerm::parse(value_text);
            if info.base.type_ != expected_type || info.value != expected_value {
                mismatches.push(format!(
                    "{name}\n  pin:  {} : {}\n  ours: {} : {}",
                    render(&expected_value, &mut Vec::new()),
                    render(&expected_type, &mut Vec::new()),
                    render(&info.value, &mut Vec::new()),
                    render(&info.base.type_, &mut Vec::new()),
                ));
            }
        }
        assert!(
            mismatches.is_empty(),
            "{} of {} fixtures differ from the pin:\n{}",
            mismatches.len(),
            FIXTURES.len(),
            mismatches.join("\n")
        );
    });
}

/// Planted negatives, run through the pin the same way (`prelude`,
/// `import Init.Notation`, then the declaration). The pin refuses three of them
/// at instance synthesis (`failed to synthesize instance of type class
/// HAdd String Nat Nat`, `HAdd String Nat ?m`, `HMul String Nat Nat`) and the
/// relation with a type mismatch (`n` has type `Nat` but is expected to have
/// type `String`): `binrel%` found the leaf types uncomparable and checked the
/// right operand against the left operand's type.
const NEGATIVES: &[(&str, Refusal)] = &[
    ("def bad1 : Nat := \"a\" + 1", Refusal::InstanceSynthesis),
    (
        "def bad2 (n : Nat) : Nat := \"a\" + n",
        Refusal::InstanceSynthesis,
    ),
    (
        "def bad3 (n : Nat) : Prop := \"a\" < n",
        Refusal::TypeMismatch,
    ),
    (
        "def bad4 (s : String) : Nat := s * 2",
        Refusal::InstanceSynthesis,
    ),
];

#[derive(Debug, PartialEq, Eq)]
enum Refusal {
    InstanceSynthesis,
    TypeMismatch,
}

fn refusal(error: &SourceCheckError) -> Option<Refusal> {
    let SourceCheckError::Command { error, .. } = error else {
        return None;
    };
    let EngineExecutionError::Frontend(NatDefinitionFrontendError::Elaborate(
        NatDefinitionElabError::Inference(reason),
    )) = error.as_ref()
    else {
        return None;
    };
    match reason {
        SourceInferenceError::InstanceSynthesisRequired => Some(Refusal::InstanceSynthesis),
        SourceInferenceError::Unification(_) | SourceInferenceError::TypeMismatch { .. } => {
            Some(Refusal::TypeMismatch)
        }
        _ => None,
    }
}

#[test]
fn operands_without_an_instance_are_refused_where_the_pin_refuses_them() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
        return;
    };
    on_a_big_stack(move || {
        let base = import_modules(
            &lib,
            &["Init.Prelude", "Init.Coe", "Init.Notation"],
            "Init.Notation",
        );
        for (declaration, expected) in NEGATIVES {
            match check(&base, declaration) {
                Err(error) => assert_eq!(
                    refusal(&error).as_ref(),
                    Some(expected),
                    "{declaration}: {error:?}"
                ),
                Ok(other) => panic!("{declaration} must be refused: {other:?}"),
            }
        }
    });
}

/// The `Int`/`Nat` mix, where the pin inserts a coercion `↑n`. Recorded from
/// the pin with `prelude`, `import Init.Data.Int.Basic`,
/// `set_option pp.all true`, the declaration and `#print`:
///
/// ```text
/// def g01 : (n : Nat) → (i : Int) → Int :=
/// fun (n : Nat) (i : Int) =>
///   @HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd) (@Nat.cast.{0} Int instNatCastInt n) i
/// def g02 : (n : Nat) → (i : Int) → Prop :=
/// fun (n : Nat) (i : Int) => @LT.lt.{0} Int Int.instLTInt i (@Nat.cast.{0} Int instNatCastInt n)
/// ```
///
/// The pin's `mkCoe` returns the coercion after `expandCoe` has unfolded the
/// `@[coe_decl]` chain down to `Nat.cast`. That expansion is not implemented,
/// so both must be refused with the typed `OperatorCoercion` refusal; neither
/// may elaborate to the unexpanded `CoeT.coe` term the native search returns.
const COERCION_FIXTURES: &[&str] = &[
    "def g01 (n : Nat) (i : Int) : Int := n + i",
    "def g02 (n : Nat) (i : Int) : Prop := i < n",
];

/// `Init.Data.Int.Basic` and its import closure, dependency first.
const INT_CLOSURE: &[&str] = &[
    "Init.Prelude",
    "Init.Coe",
    "Init.Data.Cast",
    "Init.Notation",
    "Init.Tactics",
    "Init.SizeOf",
    "Init.Core",
    "Init.SimpLemmas",
    "Init.Data.Zero",
    "Init.Data.NeZero",
    "Init.Grind.Attr",
    "Init.Grind.Interactive",
    "Init.Grind.Tactics",
    "Init.Data.Nat.Basic",
    "Init.Data.Int.Basic",
];

#[test]
fn a_coercion_the_pin_inserts_is_refused_typed_rather_than_left_unexpanded() {
    let Some(lib) = pinned_lib() else {
        eprintln!("SKIP: pinned Reference lib/lean absent (set FLN_REQUIRE_REFERENCE=1 to fail)");
        return;
    };
    on_a_big_stack(move || {
        let base = import_modules(&lib, INT_CLOSURE, "Init.Data.Int.Basic");
        for declaration in COERCION_FIXTURES {
            // Matched by variant name so this file also builds against a
            // tree without the variant (the mutant run in the bead record).
            let refused = match check(&base, declaration) {
                Err(error @ SourceCheckError::Command { .. }) => {
                    format!("{error:?}").contains("Elaborate(Inference(OperatorCoercion))")
                }
                _ => false,
            };
            assert!(
                refused,
                "{declaration} must be refused with OperatorCoercion: {:?}",
                check(&base, declaration).map(|_| ())
            );
        }
    });
}
