//! Real lexer/header boundaries for native message specifications.
use fln_parse::command_scope::{self, ScopeCommand, guard_spec::{self, Action, Severity, Whitespace}};

fn parsed(source: &str) -> Result<guard_spec::GuardSpec, fln_parse::DefinitionParseError> {
    let ScopeCommand::GuardMsgs { body, .. } = command_scope::parse(source.as_bytes())?.unwrap() else {
        panic!("not a guard: {source}");
    };
    assert!(source[body..].starts_with("#eval"));
    guard_spec::parse(source.as_bytes(), body)
}

#[test]
fn comments_unicode_and_crlf_preserve_the_guarded_body() {
    for source in [
        "/-- info: 4 -/\n#guard_msgs (whitespace := lax, drop warning, info) in\n#eval 4\n",
        "/-- β info: 4 -/\r\n#guard_msgs (whitespace /- outer /- nested -/ -/ := lax, drop warning, info) in\r\n#eval 4\r\n",
        "#guard_msgs (whitespace := lax, -- next rule\n drop warning, info) in\n#eval 4\n",
    ] {
        let spec = parsed(source).unwrap();
        assert_eq!(spec.whitespace, Whitespace::Lax);
        assert_eq!(spec.action(Severity::Warning), Action::Drop);
        assert_eq!(spec.action(Severity::Info), Action::Check);
        assert_eq!(spec.action(Severity::Error), Action::Pass);
    }
}

#[test]
fn no_spec_and_empty_spec_have_identical_defaults() {
    assert_eq!(parsed("#guard_msgs in\n#eval 4\n").unwrap(),
        parsed("#guard_msgs () in\n#eval 4\n").unwrap());
}

#[test]
fn malformed_specifications_are_not_silently_replaced_with_defaults() {
    for spec in ["whitespace := wide", "substring := 1", "drop infos", "info warning",
        "unknown := true", "info,", "whitespace := exact, whitespace := invalid"] {
        let source = format!("/-- info: 4 -/\n#guard_msgs ({spec}) in\n#eval 4\n");
        assert!(parsed(&source).is_err(), "{source}");
    }
}
