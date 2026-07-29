#!/usr/bin/env python3
"""Extract and verify the pinned Lean/Leanc/Lake command-surface census.

The generated contract deliberately has three authorities:

* source facts come from the pinned vendor tree;
* support/comparison policy comes from ``ci/CLI_LAKE_POLICY.txt`` and must be
  an exact bijection over those facts; and
* normalized process transcripts come from the exact executables recorded in
  the epoch manifest.

``--check`` is source-only and therefore remains useful on hosts without the
4 GiB Reference installation. ``--check-probes`` is the no-mock producer: it
hashes the installed executables, runs the complete bounded probe matrix twice,
and compares it with the checked-in transcript fixture. ``--capture`` performs
the same two-pass check before atomically publishing that fixture.

Run under the repository's sealed interpreter spelling:

    python3 -I -S scripts/extract/gen_cli_lake_census.py --check
    python3 -I -S scripts/extract/gen_cli_lake_census.py --check-probes
"""

from __future__ import annotations

from dataclasses import dataclass
import hashlib
import os
from pathlib import Path
import re
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[2]
SUITE_LOCK = ROOT / "SUITE.lock"
SHELL_CPP = ROOT / "vendor/lean4-src/src/util/shell.cpp"
LEAN_SHELL = ROOT / "vendor/lean4-src/src/Lean/Shell.lean"
LEANC = ROOT / "vendor/lean4-src/src/bin/leanc.in"
LAKE_MAIN = ROOT / "vendor/lean4-src/src/lake/Lake/CLI/Main.lean"
LAKE_HELP = ROOT / "vendor/lean4-src/src/lake/Lake/CLI/Help.lean"
LAKE_DEFAULTS = ROOT / "vendor/lean4-src/src/lake/Lake/Config/Defaults.lean"
LAKE_ENV = ROOT / "vendor/lean4-src/src/lake/Lake/Config/Env.lean"
LAKE_INSTALL = ROOT / "vendor/lean4-src/src/lake/Lake/Config/InstallPath.lean"
LAKE_NATIVE_LIB = ROOT / "vendor/lean4-src/src/lake/Lake/Util/NativeLib.lean"
LAKE_SERVE = ROOT / "vendor/lean4-src/src/lake/Lake/CLI/Serve.lean"
LAKE_ACTIONS = ROOT / "vendor/lean4-src/src/lake/Lake/Build/Actions.lean"
LAKE_BUILD = ROOT / "vendor/lean4-src/src/lake/Lake/Build"
POLICY = ROOT / "ci/CLI_LAKE_POLICY.txt"
TRANSCRIPTS = ROOT / "contracts/CLI_LAKE_TRANSCRIPTS.txt"
OUTPUT = ROOT / "contracts/CLI_LAKE_INVENTORY.txt"
CONSUMER = ROOT / "crates/fln-conformance/src/cli_lake_census.rs"
UNIT_TEST = ROOT / "crates/fln-conformance/tests/cli_lake_census.rs"
NO_MOCK_TEST = ROOT / "crates/fln-conformance/tests/cli_lake_census_no_mock_e2e.rs"
EXTRACTOR_SOURCE = Path(__file__).resolve()

SCHEMA = "fln-cli-lake-inventory/1"
POLICY_SCHEMA = "fln-cli-lake-policy/1"
TRANSCRIPT_SCHEMA = "fln-cli-lake-transcripts/1"
EXTRACTOR = "pinned-cli-lake-source-walk"
EXTRACTOR_VERSION = "1"
HASH_ALGORITHM = "fnv1a64"
NORMALIZER = "paths-crlf-ansi-v1"
PLATFORM = "linux-x86_64"
PROBE_TIMEOUT_SECONDS = 20
MAX_CAPTURE_BYTES = 4 * 1024 * 1024

SAFE = frozenset(
    b"abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-._/:+@"
)
ANSI = re.compile(r"\x1b\[[0-9;?]*[ -/]*[@-~]")


def die(message: str) -> "NoReturn":  # noqa: F821 - documentation-only type
    print(f"gen_cli_lake_census: {message}", file=sys.stderr)
    raise SystemExit(2)


def relative(path: Path) -> str:
    try:
        return path.relative_to(ROOT).as_posix()
    except ValueError:
        return path.as_posix()


def read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except OSError as error:
        die(f"cannot read {relative(path)}: {error}")


def line_number(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def fnv1a64_bytes(payload: bytes) -> int:
    value = 0xCBF29CE484222325
    for byte in payload:
        value ^= byte
        value = (value * 0x100000001B3) & 0xFFFFFFFFFFFFFFFF
    return value


def fnv(payload: bytes) -> str:
    return f"fnv1a64:{fnv1a64_bytes(payload):016x}"


def framed_hash(domain: str, lines: list[str]) -> str:
    payload = bytearray()
    for field in [domain, *lines]:
        encoded = field.encode("utf-8")
        payload.extend(len(encoded).to_bytes(8, "little"))
        payload.extend(encoded)
    return fnv(bytes(payload))


def file_hash(path: Path) -> str:
    try:
        return fnv(path.read_bytes())
    except OSError as error:
        die(f"cannot hash {relative(path)}: {error}")


def sha256_file(path: Path) -> tuple[str, int]:
    digest = hashlib.sha256()
    size = 0
    try:
        with path.open("rb") as source:
            while chunk := source.read(1024 * 1024):
                digest.update(chunk)
                size += len(chunk)
    except OSError as error:
        die(f"cannot hash executable {path}: {error}")
    return digest.hexdigest(), size


def encode(value: str) -> str:
    encoded = bytearray()
    for byte in value.encode("utf-8"):
        if byte in SAFE:
            encoded.append(byte)
        else:
            encoded.extend(f"%{byte:02X}".encode("ascii"))
    return encoded.decode("ascii")


def read_pin() -> dict[str, str]:
    row = next(
        (
            line
            for line in read_text(SUITE_LOCK).splitlines()
            if line.startswith("reference leanprover/lean4 ")
        ),
        None,
    )
    if row is None:
        die("SUITE.lock has no Reference row")
    fields = {"repo": "leanprover/lean4"}
    for token in row.split()[2:]:
        if "=" in token:
            key, value = token.split("=", 1)
            fields[key] = value
    required = {"tag", "commit", "tree"}
    if not required.issubset(fields):
        die(f"SUITE.lock Reference row lacks {sorted(required - fields.keys())}")
    if not re.fullmatch(r"[0-9a-f]{40}", fields["commit"]):
        die("SUITE.lock Reference commit is not a full lowercase SHA")
    if not re.fullmatch(r"[0-9a-f]{40}", fields["tree"]):
        die("SUITE.lock Reference tree is not a full lowercase SHA")
    return fields


def epoch_manifest(pin: dict[str, str]) -> Path:
    path = ROOT / "tribunal/epochs" / pin["tag"] / "MANIFEST.txt"
    if not path.is_file():
        die(f"epoch manifest is absent: {relative(path)}")
    return path


def executable_rows(pin: dict[str, str]) -> dict[str, tuple[str, int, int]]:
    path = epoch_manifest(pin)
    rows: dict[str, tuple[str, int, int]] = {}
    for number, line in enumerate(read_text(path).splitlines(), start=1):
        match = re.fullmatch(
            r"executable (lean|leanc|lake) sha256=([0-9a-f]{64}) bytes=([0-9]+)",
            line,
        )
        if match:
            rows[match.group(1)] = (
                match.group(2),
                int(match.group(3)),
                number,
            )
    if set(rows) != {"lean", "leanc", "lake"}:
        die(f"{relative(path)} lacks the exact lean/leanc/lake executable set")
    return rows


@dataclass(frozen=True)
class Fact:
    key: str
    kind: str
    attributes: tuple[tuple[str, str], ...]
    source: Path
    line: int

    def render(self) -> str:
        fields = [
            f"key={encode(self.key)}",
            f"kind={self.kind}",
            *(f"{name}={encode(value)}" for name, value in self.attributes),
            f"source={encode(relative(self.source))}:{self.line}",
        ]
        evidence = framed_hash(
            "fln-cli-lake-source-fact/1",
            [self.key, self.kind, *[f"{a}={b}" for a, b in self.attributes]],
        )
        fields.append(f"evidence={evidence}")
        return "surface " + " ".join(fields)


def fact(
    key: str,
    kind: str,
    attributes: dict[str, str],
    source: Path,
    line: int,
) -> Fact:
    return Fact(key, kind, tuple(sorted(attributes.items())), source, line)


def extract_lean_options() -> list[Fact]:
    cpp = read_text(SHELL_CPP)
    shell = read_text(LEAN_SHELL)
    table_start = cpp.find("static struct option g_long_options[]")
    table_end = cpp.find("{0, 0, 0, 0}", table_start)
    if table_start < 0 or table_end < 0:
        die(f"cannot isolate g_long_options in {relative(SHELL_CPP)}")
    table = cpp[table_start:table_end]
    rows: list[Fact] = []
    long_by_short: dict[str, list[str]] = {}
    conditional = "all"
    for offset, line in enumerate(table.splitlines()):
        stripped = line.strip()
        if stripped.startswith("#if") and "LEAN_MULTI_THREAD" in stripped:
            conditional = "feature:multi-thread"
            continue
        if stripped.startswith("#ifdef") and "LEAN_DEBUG" in stripped:
            conditional = "feature:debug"
            continue
        if stripped.startswith("#endif"):
            conditional = "all"
            continue
        match = re.search(
            r'\{"([^"]+)",\s*(no_argument|required_argument|optional_argument),'
            r"\s*0,\s*'([^']+)'\}",
            line,
        )
        if not match:
            continue
        name, argument, short = match.groups()
        line_no = line_number(cpp, table_start) + offset
        long_by_short.setdefault(short, []).append(name)
        rows.append(
            fact(
                f"option:lean:--{name}",
                "option",
                {
                    "personality": "lean",
                    "spelling": f"--{name}",
                    "argument": argument.removesuffix("_argument"),
                    "dispatch": short,
                    "availability": conditional,
                },
                SHELL_CPP,
                line_no,
            )
        )

    opt_start = cpp.find("static char const * g_opt_str")
    opt_end = cpp.find("; // NOLINT", opt_start)
    if opt_start < 0 or opt_end < 0:
        die(f"cannot isolate g_opt_str in {relative(SHELL_CPP)}")
    fragments = re.findall(r'"([^"]*)"', cpp[opt_start:opt_end])
    opt_string = "".join(fragments)
    handler_chars = set(re.findall(r"^\s*\| '([^'])' =>", shell, re.MULTILINE))
    index = 0
    seen: set[str] = set()
    while index < len(opt_string):
        char = opt_string[index]
        index += 1
        if char.isdigit() or char == ":" or not char.isalpha():
            continue
        argument = "required" if index < len(opt_string) and opt_string[index] == ":" else "no"
        if argument == "required":
            index += 1
        if char in seen:
            continue
        seen.add(char)
        aliases = ",".join(f"--{name}" for name in long_by_short.get(char, [])) or "none"
        rows.append(
            fact(
                f"option:lean:-{char}",
                "option",
                {
                    "personality": "lean",
                    "spelling": f"-{char}",
                    "argument": argument,
                    "aliases": aliases,
                    "dispatch": "handled" if char in handler_chars else "unknown",
                    "availability": "feature:multi-thread" if char == "s" else "all",
                },
                SHELL_CPP,
                line_number(cpp, opt_start),
            )
        )
    if len(rows) < 55:
        die(f"Lean option extraction collapsed to {len(rows)} rows")
    return rows


def isolate_definition(text: str, name: str, next_name: str) -> tuple[str, int]:
    start = text.find(name)
    end = text.find(next_name, start + len(name))
    if start < 0 or end < 0:
        die(f"cannot isolate {name!r}")
    return text[start:end], start


def match_arms(
    source: Path,
    definition: str,
    next_definition: str,
) -> list[tuple[list[str], str, int]]:
    text = read_text(source)
    region, start = isolate_definition(text, definition, next_definition)
    matches = list(re.finditer(r'^\| (.+?)\s+=>', region, re.MULTILINE))
    rows: list[tuple[list[str], str, int]] = []
    for index, match in enumerate(matches):
        arm = match.group(1)
        if not arm.startswith('"'):
            continue
        names = re.findall(r'"([^"]+)"', arm)
        body_end = matches[index + 1].start() if index + 1 < len(matches) else len(region)
        body = region[match.end():body_end].strip()
        rows.append((names, body, line_number(text, start + match.start())))
    return rows


def extract_lake_commands() -> list[Fact]:
    definitions = [
        ("def lakeCli : (cmd : String)", "\ndef lake : CliM", "top"),
        ("def cacheCli : (cmd : String)", "\nnamespace script", "cache"),
        ("def scriptCli : (cmd : String)", "\n/-! ### `lake` CLI", "script"),
    ]
    rows: list[Fact] = []
    for start, end, namespace in definitions:
        for names, body, line in match_arms(LAKE_MAIN, start, end):
            action_match = re.search(r"(?:lake|cache|script)\.([A-Za-z0-9]+)", body)
            action = action_match.group(1) if action_match else "typed-error"
            for name in names:
                qualified = name if namespace == "top" else f"{namespace}/{name}"
                rows.append(
                    fact(
                        f"command:lake:{qualified}",
                        "command",
                        {
                            "personality": "lake",
                            "spelling": name,
                            "namespace": namespace,
                            "action": action,
                        },
                        LAKE_MAIN,
                        line,
                    )
                )
    if len(rows) < 35:
        die(f"Lake command extraction collapsed to {len(rows)} rows")
    return rows


def option_arms(
    definition: str,
    next_definition: str,
    quoted: bool,
) -> list[tuple[str, str, int]]:
    text = read_text(LAKE_MAIN)
    region, start = isolate_definition(text, definition, next_definition)
    pattern = r'^\| "([^"]+)"\s*=>' if quoted else r"^\| '([^'])'\s*=>"
    matches = list(re.finditer(pattern, region, re.MULTILINE))
    rows: list[tuple[str, str, int]] = []
    for index, match in enumerate(matches):
        body_end = matches[index + 1].start() if index + 1 < len(matches) else len(region)
        rows.append(
            (
                match.group(1),
                region[match.end():body_end],
                line_number(text, start + match.start()),
            )
        )
    return rows


def extract_lake_options() -> list[Fact]:
    rows: list[Fact] = []
    for spelling, body, line in option_arms(
        "def lakeShortOption", "\n/-- Returns an error", False
    ):
        if spelling == "opt":
            continue
        rows.append(
            fact(
                f"option:lake:-{spelling}",
                "option",
                {
                    "personality": "lake",
                    "spelling": f"-{spelling}",
                    "argument": "required" if "takeOptArg" in body else "no",
                    "position": "before-or-after-command",
                },
                LAKE_MAIN,
                line,
            )
        )
    for spelling, body, line in option_arms(
        "def lakeLongOption", "\ndef lakeOption", True
    ):
        rows.append(
            fact(
                f"option:lake:{spelling}",
                "option",
                {
                    "personality": "lake",
                    "spelling": spelling,
                    "argument": "required" if "takeOptArg" in body else "no",
                    "position": "before-or-after-command",
                },
                LAKE_MAIN,
                line,
            )
        )
    if len(rows) < 55:
        die(f"Lake option extraction collapsed to {len(rows)} rows")
    return rows


def extract_facets() -> list[Fact]:
    rows: list[Fact] = []
    pattern = re.compile(
        r"^\s*builtin_facet\s+(?:(?P<decl>[A-Za-z0-9_]+)\s+@\s+)?"
        r"(?P<name>[A-Za-z0-9_.]+)\s*:\s*(?P<kind>[A-Za-z0-9_.]+)\s*=>",
        re.MULTILINE,
    )
    for path in sorted(LAKE_BUILD.glob("*.lean")):
        text = read_text(path)
        for match in pattern.finditer(text):
            name = match.group("name")
            kind = match.group("kind")
            rows.append(
                fact(
                    f"facet:lake:{kind}:{name}",
                    "facet",
                    {
                        "personality": "lake",
                        "target-kind": kind,
                        "name": name,
                        "declaration": match.group("decl") or name,
                    },
                    path,
                    line_number(text, match.start()),
                )
            )
    if len(rows) < 35:
        die(f"Lake facet extraction collapsed to {len(rows)} rows")
    return rows


def extract_environment() -> list[Fact]:
    sources = [
        LAKE_ENV,
        LAKE_INSTALL,
        LAKE_NATIVE_LIB,
        LAKE_SERVE,
        LAKE_MAIN,
        LAKE_ACTIONS,
    ]
    observations: dict[str, list[tuple[Path, int, str]]] = {}
    read_patterns = [
        re.compile(r'IO\.getEnv\s+"([A-Z][A-Z0-9_]*)"'),
        re.compile(r'getSearchPath\s+"([A-Z][A-Z0-9_]*)"'),
        re.compile(r'getUrlD\s+"([A-Z][A-Z0-9_]*)"'),
    ]
    write_pattern = re.compile(r'\("([A-Z][A-Z0-9_]*)",')
    for path in sources:
        text = read_text(path)
        for pattern in read_patterns:
            for match in pattern.finditer(text):
                observations.setdefault(match.group(1), []).append(
                    (path, line_number(text, match.start()), "read")
                )
        for match in write_pattern.finditer(text):
            observations.setdefault(match.group(1), []).append(
                (path, line_number(text, match.start()), "write")
            )
    leanc_text = read_text(LEANC)
    for match in re.finditer(r"\$\{([A-Z][A-Z0-9_]*)[:-]", leanc_text):
        observations.setdefault(match.group(1), []).append(
            (LEANC, line_number(leanc_text, match.start()), "read")
        )
    # sharedLibPathEnvVar is selected by platform rather than a literal at the call site.
    for name in ("DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"):
        observations.setdefault(name, []).append((LAKE_NATIVE_LIB, 38, "read"))
    rows: list[Fact] = []
    for name, sites in sorted(observations.items()):
        roles = {role for _, _, role in sites}
        source, line, _ = min(sites, key=lambda site: (relative(site[0]), site[1]))
        role = "read-write" if roles == {"read", "write"} else next(iter(roles))
        rows.append(
            fact(
                f"environment:lake:{name}",
                "environment",
                {
                    "personality": "lake",
                    "name": name,
                    "role": role,
                    "site-count": str(len(sites)),
                },
                source,
                line,
            )
        )
    if "LEAN_CC" not in observations or "LAKE_CONFIG" not in observations:
        die("environment extraction lost LEAN_CC or LAKE_CONFIG")
    if len(rows) < 25:
        die(f"environment extraction collapsed to {len(rows)} rows")
    return rows


DEFAULT_VALUES = {
    "defaultLakeDir": ".lake",
    "defaultPackagesDir": ".lake/packages",
    "defaultConfigFile": "lakefile",
    "defaultLeanConfigFile": "lakefile.lean",
    "defaultTomlConfigFile": "lakefile.toml",
    "defaultManifestFile": "lake-manifest.json",
    "defaultBuildDir": ".lake/build",
    "defaultLeanLibDir": "lib/lean",
    "defaultNativeLibDir": "lib",
    "defaultBinDir": "bin",
    "defaultIrDir": "ir",
}


def extract_config_defaults() -> list[Fact]:
    text = read_text(LAKE_DEFAULTS)
    rows: list[Fact] = []
    for name, value in DEFAULT_VALUES.items():
        match = re.search(rf"^public def {re.escape(name)}\b", text, re.MULTILINE)
        if not match:
            die(f"{relative(LAKE_DEFAULTS)} lacks {name}")
        rows.append(
            fact(
                f"config-default:lake:{name}",
                "config-default",
                {
                    "personality": "lake",
                    "name": name,
                    "value": value,
                },
                LAKE_DEFAULTS,
                line_number(text, match.start()),
            )
        )
    return rows


def extract_static_facts(pin: dict[str, str]) -> list[Fact]:
    rows = [
        fact(
            f"personality:{name}",
            "personality",
            {"personality": name, "binary": name},
            LEAN_SHELL if name == "lean" else LEANC if name == "leanc" else LAKE_MAIN,
            1,
        )
        for name in ("lean", "leanc", "lake")
    ]
    manifest = epoch_manifest(pin)
    for name, (sha256, size, line) in executable_rows(pin).items():
        rows.append(
            fact(
                f"executable:{name}",
                "executable",
                {
                    "personality": name,
                    "sha256": sha256,
                    "bytes": str(size),
                    "platform": PLATFORM,
                },
                manifest,
                line,
            )
        )
    leanc_text = read_text(LEANC)
    rules = [
        ("compiler", "LEAN_CC-or-pinned-default", 10),
        ("include", "prepend-toolchain-include", 10),
        ("link", "append-toolchain-link-flags-unless-c", 4),
        ("forward", "forward-all-user-arguments", 10),
        ("verbose", "echo-expanded-command-on-v", 12),
    ]
    for name, value, approximate_line in rules:
        needle = {
            "compiler": "${LEAN_CC",
            "include": '"-I$root/include"',
            "link": '[[ "$arg" = "-c" ]]',
            "forward": '"$@"',
            "verbose": "[[ $v == 1 ]]",
        }[name]
        at = leanc_text.find(needle)
        if at < 0:
            die(f"{relative(LEANC)} lost rule anchor {needle!r}")
        rows.append(
            fact(
                f"leanc-rule:{name}",
                "leanc-rule",
                {
                    "personality": "leanc",
                    "rule": value,
                    "surface": "inherited-compiler-delegation",
                    "platform": PLATFORM,
                },
                LEANC,
                line_number(leanc_text, at) or approximate_line,
            )
        )
    for name, disposition in [
        ("success", "accepted"),
        ("error", "rejected"),
        ("unknown", "rejected"),
        ("malformed", "rejected"),
        ("cancelled", "inconclusive"),
        ("resource-exhausted", "inconclusive"),
        ("internal-fault", "internal-fault"),
    ]:
        rows.append(
            fact(
                f"outcome:{name}",
                "outcome",
                {
                    "personality": "all",
                    "input": name,
                    "disposition": disposition,
                },
                CONSUMER,
                1,
            )
        )
    return rows


def extract_facts(pin: dict[str, str]) -> list[Fact]:
    rows = [
        *extract_static_facts(pin),
        *extract_lean_options(),
        *extract_lake_commands(),
        *extract_lake_options(),
        *extract_facets(),
        *extract_environment(),
        *extract_config_defaults(),
    ]
    by_key: dict[str, Fact] = {}
    for row in rows:
        prior = by_key.get(row.key)
        if prior is not None:
            die(
                f"duplicate surface key {row.key!r}: "
                f"{relative(prior.source)}:{prior.line} and "
                f"{relative(row.source)}:{row.line}"
            )
        by_key[row.key] = row
    return sorted(rows, key=lambda row: row.key)


def policy_fields(row: Fact) -> dict[str, str]:
    if row.kind == "environment":
        return {
            "support": "optional",
            "comparison": "normalized",
            "precedence": "environment-fallback",
            "channel": "n/a",
            "platform": "all",
            "authority": "native-target",
        }
    if row.kind == "leanc-rule":
        return {
            "support": "required",
            "comparison": "normalized",
            "precedence": "forwarded",
            "channel": "delegated",
            "platform": PLATFORM,
            "authority": "inherited",
        }
    if row.kind == "executable":
        return {
            "support": "required",
            "comparison": "exact",
            "precedence": "n/a",
            "channel": "n/a",
            "platform": PLATFORM,
            "authority": "epoch-manifest",
        }
    if row.kind == "outcome":
        return {
            "support": "required",
            "comparison": "exact",
            "precedence": "typed",
            "channel": "n/a",
            "platform": "all",
            "authority": "harness",
        }
    precedence = {
        "option": "ordered",
        "command": "first-positional",
        "facet": "config-overlay",
        "config-default": "default",
        "personality": "n/a",
    }.get(row.kind, "n/a")
    return {
        "support": "required",
        "comparison": "exact",
        "precedence": precedence,
        "channel": "n/a",
        "platform": "all",
        "authority": "native-target",
    }


def policy_template(rows: list[Fact]) -> str:
    lines = [f"schema {POLICY_SCHEMA}"]
    for row in rows:
        fields = policy_fields(row)
        lines.append(
            f"row {encode(row.key)} "
            + " ".join(f"{name}={fields[name]}" for name in sorted(fields))
        )
    return "\n".join(lines) + "\n"


def read_policy(rows: list[Fact]) -> tuple[str, dict[str, dict[str, str]]]:
    text = read_text(POLICY)
    lines = text.splitlines()
    if not lines or lines[0] != f"schema {POLICY_SCHEMA}":
        die(f"{relative(POLICY)} has wrong or absent schema")
    parsed: dict[str, dict[str, str]] = {}
    previous = ""
    expected_fields = {
        "support",
        "comparison",
        "precedence",
        "channel",
        "platform",
        "authority",
    }
    for number, line in enumerate(lines[1:], start=2):
        if not line or line.startswith("#"):
            continue
        tokens = line.split()
        if len(tokens) != 8 or tokens[0] != "row":
            die(f"{relative(POLICY)}:{number}: noncanonical policy row")
        key = tokens[1]
        if key <= previous:
            die(f"{relative(POLICY)}:{number}: keys are not strictly sorted")
        previous = key
        fields: dict[str, str] = {}
        for token in tokens[2:]:
            if token.count("=") != 1:
                die(f"{relative(POLICY)}:{number}: malformed field {token!r}")
            name, value = token.split("=", 1)
            if name in fields or not value:
                die(f"{relative(POLICY)}:{number}: duplicate/empty field {name!r}")
            fields[name] = value
        if set(fields) != expected_fields:
            die(f"{relative(POLICY)}:{number}: wrong policy field set")
        if fields["support"] not in {"required", "optional"}:
            die(f"{relative(POLICY)}:{number}: unsupported support class")
        if fields["comparison"] not in {"exact", "normalized"}:
            die(f"{relative(POLICY)}:{number}: unsupported comparison class")
        parsed[key] = fields
    raw_keys = {encode(row.key) for row in rows}
    policy_keys = set(parsed)
    if raw_keys != policy_keys:
        die(
            "surface/policy bijection failed: "
            f"missing={sorted(raw_keys - policy_keys)} "
            f"stale={sorted(policy_keys - raw_keys)}"
        )
    return text, parsed


@dataclass(frozen=True)
class Probe:
    key: str
    personality: str
    argv: tuple[str, ...]
    stdin: bytes = b""


PROBES = (
    Probe("lean:help", "lean", ("--help",)),
    Probe("lean:version", "lean", ("--version",)),
    Probe("lean:short-version", "lean", ("--short-version",)),
    Probe("lean:githash", "lean", ("--githash",)),
    Probe("lean:features", "lean", ("--features",)),
    Probe("lean:print-prefix", "lean", ("--print-prefix",)),
    Probe("lean:print-libdir", "lean", ("--print-libdir",)),
    Probe("lean:unknown-option", "lean", ("--fln-census-unknown",)),
    Probe("lean:malformed-timeout", "lean", ("--timeout=not-a-number",)),
    Probe("lean:stdin-success", "lean", ("--stdin",), b"#check Nat\n"),
    Probe(
        "lean:json-error",
        "lean",
        ("--json", "--stdin"),
        b"#check CliLakeCensusMissing\n",
    ),
    Probe("lake:usage", "lake", ()),
    Probe("lake:help", "lake", ("--help",)),
    Probe("lake:help-build", "lake", ("help", "build")),
    Probe("lake:help-query", "lake", ("help", "query")),
    Probe("lake:help-env", "lake", ("help", "env")),
    Probe("lake:version", "lake", ("--version",)),
    Probe("lake:unknown-command", "lake", ("fln-census-unknown",)),
    Probe("lake:unknown-option", "lake", ("--fln-census-unknown", "help")),
    Probe("lake:missing-dir-value", "lake", ("--dir",)),
    Probe(
        "lake:missing-root",
        "lake",
        ("--dir", "/fln-cli-census/absent", "build"),
    ),
    Probe("lake:json-help", "lake", ("--json", "help", "query")),
    Probe("leanc:help", "leanc", ("--help",)),
    Probe("leanc:version", "leanc", ("--version",)),
    Probe("leanc:unknown-option", "leanc", ("--fln-census-unknown",)),
)


@dataclass(frozen=True)
class ProbeResult:
    key: str
    personality: str
    argv: str
    stdin_hash: str
    exit_code: int
    stdout_hash: str
    stderr_hash: str
    stdout_bytes: int
    stderr_bytes: int
    channel: str

    def render(self) -> str:
        return (
            f"probe key={encode(self.key)} personality={self.personality} "
            f"argv={encode(self.argv)} stdin={self.stdin_hash} "
            f"exit={self.exit_code} stdout={self.stdout_hash} "
            f"stderr={self.stderr_hash} stdout-bytes={self.stdout_bytes} "
            f"stderr-bytes={self.stderr_bytes} channel={self.channel} "
            f"normalizer={NORMALIZER}"
        )


def locate_binaries(pin: dict[str, str]) -> dict[str, Path]:
    override = os.environ.get("FLN_REFERENCE_BIN")
    if override:
        lean = Path(override)
    else:
        home = os.environ.get("HOME")
        if not home:
            die("HOME is unset and FLN_REFERENCE_BIN was not provided")
        lean = (
            Path(home)
            / ".elan/toolchains"
            / f"leanprover--lean4---{pin['tag']}"
            / "bin/lean"
        )
    binaries = {name: lean.with_name(name) for name in ("lean", "leanc", "lake")}
    missing = [str(path) for path in binaries.values() if not path.is_file()]
    if missing:
        die(f"pinned executable set is absent: {missing}")
    return binaries


def verify_binary_identity(
    binaries: dict[str, Path],
    expected: dict[str, tuple[str, int, int]],
) -> None:
    for name, path in binaries.items():
        digest, size = sha256_file(path)
        want_digest, want_size, _line = expected[name]
        if (digest, size) != (want_digest, want_size):
            die(
                f"{path} does not match the epoch manifest: "
                f"sha256={digest} bytes={size}, expected "
                f"sha256={want_digest} bytes={want_size}"
            )


def clean_environment(toolchain_root: Path) -> dict[str, str]:
    environment = dict(os.environ)
    for name in list(environment):
        if name.startswith("LAKE_") or name in {
            "LEAN",
            "LEAN_PATH",
            "LEAN_SRC_PATH",
            "LEAN_SYSROOT",
            "LEAN_CC",
            "LEAN_AR",
            "LEAN_GITHASH",
            "ELAN_TOOLCHAIN",
        }:
            environment.pop(name, None)
    environment.update(
        {
            "LANG": "C",
            "LC_ALL": "C",
            "TERM": "dumb",
            "NO_COLOR": "1",
            "CLICOLOR": "0",
            "PATH": f"{toolchain_root / 'bin'}:/usr/bin:/bin",
        }
    )
    return environment


def normalize(payload: bytes, replacements: list[tuple[str, str]]) -> bytes:
    text = payload.decode("utf-8", errors="replace").replace("\r\n", "\n")
    text = ANSI.sub("", text)
    for actual, symbolic in sorted(replacements, key=lambda item: -len(item[0])):
        if actual:
            text = text.replace(actual, symbolic)
    return text.encode("utf-8")


def run_probe(
    probe: Probe,
    binaries: dict[str, Path],
    environment: dict[str, str],
    replacements: list[tuple[str, str]],
) -> ProbeResult:
    command = [str(binaries[probe.personality]), *probe.argv]
    try:
        result = subprocess.run(
            command,
            input=probe.stdin,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            cwd=ROOT,
            env=environment,
            check=False,
            timeout=PROBE_TIMEOUT_SECONDS,
        )
    except subprocess.TimeoutExpired:
        die(f"probe {probe.key} exhausted its {PROBE_TIMEOUT_SECONDS}s budget")
    if len(result.stdout) > MAX_CAPTURE_BYTES or len(result.stderr) > MAX_CAPTURE_BYTES:
        die(f"probe {probe.key} exceeded the {MAX_CAPTURE_BYTES}-byte channel budget")
    stdout = normalize(result.stdout, replacements)
    stderr = normalize(result.stderr, replacements)
    channel = (
        "split"
        if stdout and stderr
        else "stdout"
        if stdout
        else "stderr"
        if stderr
        else "silent"
    )
    return ProbeResult(
        key=probe.key,
        personality=probe.personality,
        argv="\x1f".join(probe.argv) or "<none>",
        stdin_hash=fnv(probe.stdin) if probe.stdin else "none",
        exit_code=result.returncode,
        stdout_hash=fnv(stdout),
        stderr_hash=fnv(stderr),
        stdout_bytes=len(stdout),
        stderr_bytes=len(stderr),
        channel=channel,
    )


def capture_results(pin: dict[str, str]) -> list[ProbeResult]:
    binaries = locate_binaries(pin)
    expected = executable_rows(pin)
    verify_binary_identity(binaries, expected)
    toolchain_root = binaries["lean"].parent.parent.resolve()
    replacements = [
        (str(toolchain_root), "<TOOLCHAIN>"),
        (str(ROOT.resolve()), "<WORKSPACE>"),
        (os.environ.get("HOME", ""), "<HOME>"),
    ]
    environment = clean_environment(toolchain_root)
    first = [
        run_probe(probe, binaries, environment, replacements) for probe in PROBES
    ]
    second = [
        run_probe(probe, binaries, environment, replacements) for probe in PROBES
    ]
    if first != second:
        for left, right in zip(first, second):
            if left != right:
                die(f"probe {left.key} is nondeterministic across fresh executions")
        die("probe matrix cardinality changed between executions")
    return first


def render_transcripts(pin: dict[str, str], rows: list[ProbeResult]) -> str:
    probe_lines = [row.render() for row in rows]
    lines = [
        f"schema {TRANSCRIPT_SCHEMA}",
        f"reference tag={pin['tag']} commit={pin['commit']} platform={PLATFORM}",
        f"normalizer {NORMALIZER}",
        f"probe-count {len(rows)}",
        *probe_lines,
        f"transcript-root {framed_hash(TRANSCRIPT_SCHEMA, probe_lines)}",
    ]
    return "\n".join(lines) + "\n"


def read_transcripts(pin: dict[str, str]) -> tuple[str, list[str], str]:
    text = read_text(TRANSCRIPTS)
    lines = text.splitlines()
    prefix = [
        f"schema {TRANSCRIPT_SCHEMA}",
        f"reference tag={pin['tag']} commit={pin['commit']} platform={PLATFORM}",
        f"normalizer {NORMALIZER}",
        f"probe-count {len(PROBES)}",
    ]
    if lines[:4] != prefix:
        die(f"{relative(TRANSCRIPTS)} has stale schema, pin, normalizer or count")
    if len(lines) != len(PROBES) + 5:
        die(f"{relative(TRANSCRIPTS)} has wrong line count")
    probe_lines = lines[4:-1]
    keys: list[str] = []
    for number, line in enumerate(probe_lines, start=5):
        tokens = line.split()
        if len(tokens) != 12 or tokens[0] != "probe":
            die(f"{relative(TRANSCRIPTS)}:{number}: noncanonical probe row")
        fields = dict(token.split("=", 1) for token in tokens[1:])
        required = {
            "key",
            "personality",
            "argv",
            "stdin",
            "exit",
            "stdout",
            "stderr",
            "stdout-bytes",
            "stderr-bytes",
            "channel",
            "normalizer",
        }
        if set(fields) != required:
            die(f"{relative(TRANSCRIPTS)}:{number}: wrong probe field set")
        keys.append(fields["key"])
        if fields["normalizer"] != NORMALIZER:
            die(f"{relative(TRANSCRIPTS)}:{number}: wrong normalizer")
    expected_keys = [encode(probe.key) for probe in PROBES]
    if keys != expected_keys:
        die(f"{relative(TRANSCRIPTS)} probe order/set drifted")
    want_root = framed_hash(TRANSCRIPT_SCHEMA, probe_lines)
    if lines[-1] != f"transcript-root {want_root}":
        die(f"{relative(TRANSCRIPTS)} transcript root mismatch")
    return text, probe_lines, want_root


def source_rows(facts: list[Fact], pin: dict[str, str]) -> list[Path]:
    paths = {
        EXTRACTOR_SOURCE,
        SUITE_LOCK,
        epoch_manifest(pin),
        SHELL_CPP,
        LEAN_SHELL,
        LEANC,
        LAKE_MAIN,
        LAKE_HELP,
        LAKE_DEFAULTS,
        LAKE_ENV,
        LAKE_INSTALL,
        LAKE_NATIVE_LIB,
        LAKE_SERVE,
        LAKE_ACTIONS,
        TRANSCRIPTS,
    }
    paths.update(row.source for row in facts)
    for path in (CONSUMER, UNIT_TEST, NO_MOCK_TEST):
        if path.is_file():
            paths.add(path)
    return sorted(paths, key=relative)


def render_inventory() -> tuple[str, dict[str, int]]:
    pin = read_pin()
    facts = extract_facts(pin)
    policy_text, _policy_rows = read_policy(facts)
    _transcript_text, probe_lines, transcript_root = read_transcripts(pin)
    raw: list[str] = [
        "reference "
        f"repo={pin['repo']} tag={pin['tag']} commit={pin['commit']} tree={pin['tree']}"
    ]
    for path in source_rows(facts, pin):
        raw.append(f"source path={encode(relative(path))} hash={file_hash(path)}")
    raw.extend(row.render() for row in facts)
    raw.extend(f"transcript {line.removeprefix('probe ')}" for line in probe_lines)
    kind_counts: dict[str, int] = {}
    for row in facts:
        kind_counts[row.kind] = kind_counts.get(row.kind, 0) + 1
    lines = [
        f"schema {SCHEMA}",
        f"extractor {EXTRACTOR} version={EXTRACTOR_VERSION}",
        f"hash {HASH_ALGORITHM} framing=u64le-length-prefixed",
        "policy-join exact-surface-bijection",
        f"platform {PLATFORM}",
        f"surface-count {len(facts)}",
        f"transcript-count {len(probe_lines)}",
        f"source-count {sum(line.startswith('source ') for line in raw)}",
        *(
            f"{kind}-count {count}"
            for kind, count in sorted(kind_counts.items())
        ),
        "leanc-surface inherited-compiler-delegation-not-native-flag-parity",
        "cancellation-outcome typed-inconclusive",
        "resource-outcome typed-inconclusive",
        "raw-begin",
        *raw,
        "raw-end",
    ]
    raw_root = framed_hash("fln-cli-lake-raw/1", raw)
    policy_root = framed_hash(POLICY_SCHEMA, policy_text.splitlines())
    lines.extend(
        [
            f"raw-root {raw_root}",
            f"policy-root {policy_root}",
            f"transcript-root {transcript_root}",
        ]
    )
    inventory_root = framed_hash(SCHEMA, lines)
    lines.append(f"inventory-root {inventory_root}")
    counts = {
        "surfaces": len(facts),
        "transcripts": len(probe_lines),
        "sources": sum(line.startswith("source ") for line in raw),
    }
    return "\n".join(lines) + "\n", counts


def atomic_publish(path: Path, text: str) -> str:
    payload = text.encode("utf-8")
    if path.exists() and path.read_bytes() == payload:
        return "unchanged"
    path.parent.mkdir(parents=True, exist_ok=True)
    candidate = path.with_name(path.name + ".candidate")
    try:
        with candidate.open("xb") as output:
            output.write(payload)
            output.flush()
            os.fsync(output.fileno())
    except FileExistsError:
        die(f"interrupted publication candidate exists: {relative(candidate)}")
    except OSError as error:
        die(f"cannot write publication candidate {relative(candidate)}: {error}")
    try:
        os.replace(candidate, path)
        flags = os.O_RDONLY | getattr(os, "O_DIRECTORY", 0)
        directory_fd = os.open(path.parent, flags)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    except OSError as error:
        die(f"atomic publication failed for {relative(path)}: {error}")
    return "published"


def check_output(path: Path, want: str) -> int:
    candidate = path.with_name(path.name + ".candidate")
    if candidate.exists():
        print(
            f"gen_cli_lake_census: DRIFT: interrupted candidate "
            f"{relative(candidate)} exists",
            file=sys.stderr,
        )
        return 1
    if not path.exists():
        print(
            f"gen_cli_lake_census: DRIFT: {relative(path)} missing",
            file=sys.stderr,
        )
        return 1
    have = read_text(path)
    if have == want:
        return 0
    have_lines = have.splitlines()
    want_lines = want.splitlines()
    for number, (actual, expected) in enumerate(
        zip(have_lines, want_lines), start=1
    ):
        if actual != expected:
            print(
                f"gen_cli_lake_census: DRIFT: {relative(path)}:{number}\n"
                f"  checked-in: {actual!r}\n"
                f"  regenerated: {expected!r}",
                file=sys.stderr,
            )
            return 1
    print(
        f"gen_cli_lake_census: DRIFT: {relative(path)} line count differs "
        f"({len(have_lines)} vs {len(want_lines)})",
        file=sys.stderr,
    )
    return 1


def main() -> int:
    arguments = sys.argv[1:]
    allowed = {
        "--check",
        "--check-probes",
        "--capture",
        "--print-policy-template",
    }
    if len(arguments) > 1 or any(argument not in allowed for argument in arguments):
        die(
            "usage is gen_cli_lake_census.py "
            "[--check|--check-probes|--capture|--print-policy-template]"
        )
    pin = read_pin()
    facts = extract_facts(pin)
    if arguments == ["--print-policy-template"]:
        sys.stdout.write(policy_template(facts))
        return 0
    if arguments in (["--capture"], ["--check-probes"]):
        transcript_text = render_transcripts(pin, capture_results(pin))
        if arguments == ["--check-probes"]:
            result = check_output(TRANSCRIPTS, transcript_text)
            if result == 0:
                print(
                    "gen_cli_lake_census: probe check OK "
                    f"({len(PROBES)} probes, two identical complete passes)"
                )
            return result
        transcript_action = atomic_publish(TRANSCRIPTS, transcript_text)
        inventory_text, counts = render_inventory()
        inventory_action = atomic_publish(OUTPUT, inventory_text)
        print(
            "gen_cli_lake_census: "
            f"{transcript_action} {relative(TRANSCRIPTS)}; "
            f"{inventory_action} {relative(OUTPUT)} "
            f"({counts['surfaces']} surfaces, {counts['transcripts']} probes)"
        )
        return 0
    inventory_text, counts = render_inventory()
    if arguments == ["--check"]:
        result = check_output(OUTPUT, inventory_text)
        if result == 0:
            print(
                "gen_cli_lake_census: source check OK "
                f"({counts['surfaces']} surfaces, {counts['transcripts']} transcripts, "
                f"{counts['sources']} source bindings)"
            )
        return result
    action = atomic_publish(OUTPUT, inventory_text)
    print(
        f"gen_cli_lake_census: {action} {relative(OUTPUT)} "
        f"({counts['surfaces']} surfaces, {counts['transcripts']} transcripts, "
        f"{counts['sources']} source bindings)"
    )
    return 0


if __name__ == "__main__":
    hostile_python = sorted(name for name in os.environ if name.startswith("PYTHON"))
    if not all((sys.flags.isolated, sys.flags.ignore_environment, sys.flags.no_site)):
        die("must run under python3 -I -S")
    if hostile_python:
        print(
            "gen_cli_lake_census: isolated mode ignores ambient "
            f"{', '.join(hostile_python)}",
            file=sys.stderr,
        )
    raise SystemExit(main())
