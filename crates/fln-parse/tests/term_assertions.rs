#![forbid(unsafe_code)]
use fln_parse::parse_definition;
#[test]
fn original_assertion_tokens_comments_and_crlf_round_trip() {
    for source in [
        "theorem t (P : Prop) (p : P) : P := have h : P := p; show P from h",
        "theorem t (P : Prop) (p : P) : P := have : P := p; this",
        "theorem t (P : Prop) (p : P) : P := show P by exact p",
        "theorem t (P : Prop) (p : P) : P := have h : P := (by exact p); h",
        "theorem τ (P : Prop) (p : P) : P := have h : P := p;\r\n -- retained\r\n show P from h\r\n",
    ] {
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            source.replace('\r', "").as_bytes()
        );
    }
}
#[test]
fn incomplete_assertions_never_drop_a_type_value_or_continuation() {
    for source in [
        "def x : Nat := have h : Nat := 0",
        "def x : Nat := have h : Nat := 0;",
        "def x : Nat := have h : := 0; h",
        "def x : Nat := have h := ; h",
        "def x : Nat := show Nat",
        "def x : Nat := show from 0",
        "def x : Nat := show Nat from",
        "def x : Nat := show Nat by",
        "def x : Nat := have h Nat := 0; h",
    ] {
        assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
    }
}
#[test]
fn nested_assertions_use_heap_frames_on_a_small_stack() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut source = String::from("def x : Nat := ");
            for _ in 0..600 {
                source.push_str("show Nat from ");
            }
            source.push('0');
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            let mut source = String::from("def x : Nat := ");
            for _ in 0..600 {
                source.push_str("have h : Nat := 0; ");
            }
            source.push('0');
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        })
        .unwrap()
        .join()
        .unwrap();
}
#[test]
fn scalar_extensions_do_not_widen_the_nat_only_driver() {
    // The older driver still reads contextual words as ordinary identifiers,
    // not as the richer source form. Its grammar and vocabulary are unchanged.
    let source = b"def x : Nat := show Nat from 0";
    let plain = fln_parse::parse_nat_definition(source).unwrap();
    let extended = parse_definition(source).unwrap();
    assert_ne!(plain.syntax(), extended.syntax());
    assert_eq!(plain.reconstruct_original(), source);
    assert!(fln_parse::parse_nat_definition(b"def x : Nat := have h : Nat := 0; h").is_err());
}

#[test]
fn contextual_keywords_do_not_steal_declaration_or_escaped_names() {
    for source in [
        "def have (n : Nat) : Nat := n",
        "def show (n : Nat) : Nat := n",
        "def from (n : Nat) : Nat := n",
        "def value («have» : Nat) : Nat := «have»",
        "def value («show» : Nat) : Nat := «show»",
        "def value («from» : Nat) : Nat := «from»",
    ] {
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    }
}

#[test]
fn suffices_retains_its_source_order_and_rejects_incomplete_chains() {
    for source in [
        "theorem t (P : Prop) (p : P) : P := suffices h : P from h; p",
        "theorem t (P : Prop) (p : P) : P := suffices P from this; p",
        "theorem t (P : Prop) (p : P) : P := suffices /- fact -/ h : P from (by exact h);\r\n  p\r\n",
    ] {
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        assert_eq!(
            parsed.reconstruct_normalized().unwrap(),
            source.replace('\r', "").as_bytes()
        );
    }
    for tail in [
        "suffices",
        "suffices h : P",
        "suffices h : P from h",
        "suffices P from this;",
        "suffices : P from this; p",
        "suffices h := p; h",
    ] {
        assert!(
            parse_definition(format!("theorem t (P : Prop) (p : P) : P := {tail}").as_bytes())
                .is_err(),
            "{tail}"
        );
    }
}
#[test]
fn deeply_chained_suffices_does_not_recurse_on_the_host_stack() {
    std::thread::Builder::new()
        .stack_size(128 * 1024)
        .spawn(|| {
            let mut source = String::from("def chain : Nat := ");
            for _ in 0..600 {
                source.push_str("suffices h : Nat from h; ");
            }
            source.push('0');
            let parsed = parse_definition(source.as_bytes()).unwrap();
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        })
        .unwrap()
        .join()
        .unwrap();
}
