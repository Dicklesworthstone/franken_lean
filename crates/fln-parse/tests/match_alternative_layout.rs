//! Regression for fln-match-alt-column-false-accept-u3fv.
//! Lean v4.32.0's Parser/Term.lean matchAlt applies checkColGe before
//! every RHS parser. These tests exercise the real native parser, not a
//! standalone indentation predicate; accepted inputs must round-trip intact.
use fln_parse::parse_definition;

fn accepts(source: &str) {
    let parsed = parse_definition(source.as_bytes())
        .unwrap_or_else(|error| panic!("expected acceptance:\n{source}\n{error:?}"));
    assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    assert_eq!(
        parsed.reconstruct_normalized().unwrap(),
        source.replace("\r\n", "\n").as_bytes()
    );
}

fn refuses(source: &str) {
    assert!(
        parse_definition(source.as_bytes()).is_err(),
        "under-indented alternative was accepted:\n{source}"
    );
}

#[test]
fn upstream_partial_equation_false_accept_is_refused() {
    refuses("partial def frob : Nat → Nat | i =>\nif i > 10 then frob 5 else frob (i-1)\n");
}

#[test]
fn term_equation_and_function_rhs_use_the_same_column_boundary() {
    for header in [
        "def f (n : Nat) : Nat := match n with",
        "def f : Nat -> Nat",
        "def f : Nat -> Nat := fun",
    ] {
        for indentation in 1..=8 {
            let pipe = " ".repeat(indentation);
            accepts(&format!("{header}\n{pipe}| n =>\n{pipe}n\n"));
            accepts(&format!("{header}\n{pipe}| n =>\n{pipe}  n\n"));
            refuses(&format!(
                "{header}\n{pipe}| n =>\n{}n\n",
                " ".repeat(indentation - 1)
            ));
        }
    }
}

#[test]
fn same_line_rhs_remains_accepted_for_all_three_forms() {
    for source in [
        "def f (b : Bool) := match b with | true => 1 | false => 0",
        "def f : Bool -> Nat | true => 1 | false => 0",
        "def f : Bool -> Nat := fun | true => 1 | false => 0",
    ] {
        accepts(source);
    }
}

#[test]
fn each_branch_is_checked_not_just_the_final_branch() {
    let header = "def f (b : Bool) : Nat := match b with\n";
    accepts(&format!("{header}  | true =>\n  1\n  | false =>\n  0\n"));
    refuses(&format!("{header}  | true =>\n 1\n  | false =>\n  0\n"));
    refuses(&format!("{header}  | true =>\n  1\n  | false =>\n 0\n"));
}

#[test]
fn shared_patterns_measure_from_the_first_pipe() {
    accepts("def f (b : Bool) : Nat := match b with\n  | true | false =>\n  7\n");
    refuses("def f (b : Bool) : Nat := match b with\n  | true | false =>\n 7\n");
}

#[test]
fn next_line_arrow_cannot_reset_the_pipe_baseline() {
    accepts("def f (n : Nat) := match n with\n    | n\n      => n\n");
    refuses("def f (n : Nat) := match n with\n    | n\n=> n\n");
}

#[test]
fn brackets_and_proof_bodies_do_not_bypass_the_boundary() {
    for rhs in ["(7)", "{ value := 7 }", "by exact 7"] {
        accepts(&format!("def f (n : Nat) := match n with\n    | _ =>\n    {rhs}\n"));
        refuses(&format!("def f (n : Nat) := match n with\n    | _ =>\n   {rhs}\n"));
    }
}

#[test]
fn crlf_and_comments_preserve_the_actual_rhs_position() {
    accepts("def f (n : Nat) := match n with\r\n  | n => -- arrow\r\n/- trivia -/\r\n  n\r\n");
    refuses("def f (n : Nat) := match n with\r\n  | n => -- arrow\r\n/- trivia -/\r\n n\r\n");
}

#[test]
fn unicode_before_an_inline_pipe_uses_character_not_byte_columns() {
    for header in [
        "def f : Nat → Nat := fun | n =>",
        "def f : Nat -> Nat := λ | n =>",
        "def f : Nat -> Nat := fun /- λ🙂 -/ | n =>",
    ] {
        let byte_offset = header.find('|').unwrap();
        let column = header[..byte_offset].chars().count();
        assert!(byte_offset > column, "control must distinguish byte columns");
        accepts(&format!("{header}\n{}n\n", " ".repeat(column)));
        refuses(&format!("{header}\n{}n\n", " ".repeat(column - 1)));
    }
}

#[test]
fn nested_match_uses_its_own_pipe_not_the_outer_pipe() {
    accepts("def f (b : Bool) := match b with\n  | true => match b with\n    | _ =>\n    7\n  | false => 0\n");
    refuses("def f (b : Bool) := match b with\n  | true => match b with\n    | _ =>\n   7\n  | false => 0\n");
}
