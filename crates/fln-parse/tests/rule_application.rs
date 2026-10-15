//! Rule tactic syntax is lossless and has the pin's five exact slots.
#![forbid(unsafe_code)]
use fln_core::name::Name;
use fln_parse::parse_definition;
use fln_syntax::tree::Syntax;

#[test]
fn rule_tactics_keep_options_arguments_and_all_original_bytes() {
    for tactic in ["apply_assumption", "apply_rules"] {
        for suffix in [
            "",
            " only []",
            " only [*]",
            " [-h, h]",
            " (maxDepth := (0x10)) -symm +exfalso only [*, -h, (f h),]",
            " (symm := false) (exfalso := Bool.true) [f h]",
        ] {
            let source = format!(
                "/-- λ 🦀 -/\r\ntheorem result (P : Prop) (h : P) (f : P -> P) : P := by\r\n  {tactic}{suffix}\r\n"
            );
            let parsed =
                parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
            assert_eq!(parsed.reconstruct_original(), source.as_bytes());
            let expected = Name::from_components([
                "Lean",
                "Parser",
                "Tactic",
                if tactic == "apply_rules" {
                    "applyRules"
                } else {
                    "applyAssumption"
                },
            ]);
            let mut work = vec![parsed.syntax()];
            let mut found = false;
            while let Some(node) = work.pop() {
                if let Syntax::Node { kind, args, .. } = node {
                    if kind == &expected {
                        found = true;
                        assert_eq!(args.len(), 5);
                        assert!(matches!(&args[0], Syntax::Atom {val, ..} if val == tactic));
                        assert_eq!(
                            args[1].kind(),
                            Some(&Name::from_components([
                                "Lean",
                                "Parser",
                                "Tactic",
                                "optConfig"
                            ]))
                        );
                        assert!(matches!(&args[4], Syntax::Node {args, ..} if args.is_empty()));
                    }
                    work.extend(args);
                }
            }
            assert!(found);
        }
    }
}

#[test]
fn contextual_identifiers_and_nested_controls_keep_distinct_meaning() {
    for source in [
        "def apply_rules : Nat := 7",
        "def apply_assumption : Nat := 8",
        "theorem result (P : Prop) (apply_rules : P) : P := by exact apply_rules",
        "theorem result (P : Prop) (h : P) : P := by first | apply_rules only [] | apply_assumption only [h]",
        "theorem result (P : Prop) (h : P) : P := by (apply_rules only [h])",
    ] {
        let parsed =
            parse_definition(source.as_bytes()).unwrap_or_else(|e| panic!("{source}\n{e:?}"));
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
    }
}

#[test]
fn missing_terms_star_modifiers_and_using_suffixes_are_not_discarded() {
    for tactic in ["apply_rules", "apply_assumption"] {
        for suffix in [
            "*",
            " [",
            " [h,,h]",
            " [,h]",
            " [-]",
            " [* h]",
            " [-f h]",
            " using other",
            " [h] trailing",
            " (maxDepth :=)",
            " +",
            " (symm := true",
        ] {
            let source = format!("theorem bad (P : Prop) (h : P) : P := by {tactic}{suffix}");
            assert!(parse_definition(source.as_bytes()).is_err(), "{source}");
        }
    }
}

#[test]
fn selected_congruence_lemmas_remain_terms_not_tactic_keywords() {
    for tactic in ["apply_rules", "apply_assumption", "solve_by_elim"] {
        let source = format!(
            "/-- λ -/\r\ntheorem t (f : Nat -> Nat) (a b : Nat) (h : a = b) : f a = f b := by\r\n  {tactic} only [congrArg f, (congrFun h), Eq.refl]\r\n"
        );
        let parsed = parse_definition(source.as_bytes()).unwrap();
        assert_eq!(parsed.reconstruct_original(), source.as_bytes());
        let mut work = vec![parsed.syntax()];
        let mut names = Vec::new();
        while let Some(node) = work.pop() {
            match node {
                Syntax::Ident { val, .. } => names.push(val.clone()),
                Syntax::Node { args, .. } => work.extend(args),
                _ => {}
            }
        }
        for expected in ["congrArg", "congrFun"] {
            assert_eq!(
                names
                    .iter()
                    .filter(|n| **n == Name::from_components([expected]))
                    .count(),
                1,
                "a selected congruence lemma is an ordinary term identifier"
            );
        }
        assert!(names.contains(&Name::from_components(["Eq", "refl"])));
    }
}
