//! Imported tactic MacroM code, real parser journals and kernel-checked proofs.
use super::*;

fn provider() -> String {
    format!(
        "{}\n#check Nat\npublic def admittedMacroValue : Nat := 11\n#check admittedMacroValue\n",
        include_str!("../../../fln-olean/fixtures/ir/AdmittedTacticMacro.lean"),
    )
}

const CLIENT: &str = concat!(
    "prelude\nimport AdmittedSourceMacro\n",
    "theorem macroCloses (n : Nat) : Eq n n := by imported_do [rfl]\n",
    "theorem macroIntroduces (P : Prop) : P → P := by\n",
    "  imported_do [intro h]\n  exact h\n",
    "theorem macroSplits (P : Prop) (h : P) : And P P := by\n",
    "  imported_do [constructor]\n  all_goals exact h\n",
    "theorem macroNested (n : Nat) : Eq n n := by imported_do [imported_do [rfl]]\n",
    "theorem macroFallback (n : Nat) : Eq n n := by\n",
    "  imported_choice [rfl] [exact Nat.zero]\n",
    "theorem macroRollback (P : Prop) : P → P := by\n",
    "  imported_choice [intro h] [(intro abandoned; fail)]\n  exact h\n",
    "theorem macroCaught (n : Nat) : Eq n n := by\n",
    "  first | imported_failure | rfl\n",
    "theorem macroCallback (n : Nat) : Eq n n := by imported_expand [imported_do [rfl]]\n",
    "theorem macroLazy (n : Nat) : Eq n n := by imported_lazy [rfl]\n",
    "theorem macroTerm (n : Nat) : Eq n n := by imported_do [exact imported_term [Eq.refl n]]\n",
    "theorem macroNativeTerm (n : Nat) : Eq n n := by exact imported_term [Eq.refl n]\n",
    "theorem macroHEq (n : Nat) : HEq n n := by imported_do [rfl]\n",
    "def use {A : Type} (run : A → Nat) (value : A) : Nat := run value\n",
    "def postponedTerm : Nat := by\n",
    "  exact use (imported_term [fun f => f Nat.zero]) (fun n => Nat.succ n)\n",
    "theorem postponedTerm_eq : Eq postponedTerm (Nat.succ Nat.zero) := by rfl\n",
    "def postponedTactic : Nat := use\n",
    "  (fun f => by first | imported_do [exact f Nat.zero] | exact Nat.zero)\n",
    "  (fun n => Nat.succ n)\n",
    "theorem postponedTactic_eq : Eq postponedTactic (Nat.succ Nat.zero) := by rfl\n",
    "def postponedNested : Nat := by\n",
    "  exact use (imported_term [fun f => use (fun g => g Nat.zero) f]) (fun n => Nat.succ n)\n",
    "theorem postponedNested_eq : Eq postponedNested (Nat.succ Nat.zero) := by rfl\n",
    "theorem macroQuoted (n : Nat) : Eq n n := by imported_quoted\n",
    "theorem macroQuotedAssumption (P : Prop) (h : P) : P := by imported_assumption\n",
    "theorem macroQuotedIdentifier : True := by imported_true\n",
);

#[test]
fn installed_imported_tactics_execute_backtrack_and_leave_checked_goals() {
    let Some(project) = ImportedMacroProject::prepare_with_source(&provider()) else {
        return;
    };
    let selected = ["AdmittedSourceMacro"];
    let oracle = project.oracle(CLIENT);
    assert!(oracle.status.success(), "{oracle:?}; {:?}", project.root);
    assert!(
        oracle.stdout.is_empty() && oracle.stderr.is_empty(),
        "{oracle:?}"
    );
    let report = project.check_with_syntax_report(CLIENT, &selected);
    let macros = assert_imported_macro_execution(&report);
    assert!(report.contains("\"theorems\":18"), "{report}");
    assert!(report.contains("\"axioms\":0"), "{report}");
    assert!(report.contains("\"sorryDeclarations\":0"), "{report}");
    for declaration in [
        "admittedTacticMacro",
        "admittedTacticEarlier",
        "admittedTacticLater",
        "admittedTacticFail",
        "admittedRflFallback",
        "admittedTacticExpand",
        "admittedTacticLazyWinner",
        "admittedTacticTermMacro",
        "_aux_AdmittedSourceMacro___macroRules_tacticImported_quoted_1",
        "_aux_AdmittedSourceMacro___macroRules_tacticImported_assumption_1",
        "_aux_AdmittedSourceMacro___macroRules_tacticImported_true_1",
    ] {
        assert!(
            report.contains(&format!(
                "{{\"name\":\"{declaration}\",\"producer\":\"reference\"}}"
            )),
            "{report}"
        );
    }
    assert!(
        !report.contains("\"name\":\"admittedTacticUnusedLoop\""),
        "{report}"
    );
    let (_, native) = macros.split_once("\"linkedNativeFunctions\":[").unwrap();
    let (native, _) = native.split_once(']').unwrap();
    for method in [
        "mirror:Lean.Macro.expandMacro?",
        "mirror:Lean.Name.str._override",
        "mirror:Lean.Syntax.getArg",
        "mirror:Lean.Syntax.isOfKind",
        "mirror:Lean.addMacroScope",
    ] {
        assert!(native.contains(&format!("\"{method}\"")), "{report}");
    }

    let queries =
        format!("{CLIENT}#check macroIntroduces\n#check macroSplits\n#check macroRollback\n");
    let oracle = project.oracle(&queries);
    assert!(oracle.status.success(), "{oracle:?}");
    let native = project.native_with_syntax("lean", &queries, Some(&project.partition), &selected);
    assert!(native.status.success(), "{native:?}; {:?}", project.root);
    assert_eq!(native.stdout, oracle.stdout);
    assert!(native.stderr.is_empty(), "{native:?}");

    let false_proof = concat!(
        "prelude\nimport AdmittedSourceMacro\n",
        "theorem falseProof : Eq (0 : Nat) 1 := by imported_do [rfl]\n",
    );
    assert!(!project.oracle(false_proof).status.success());
    ImportedMacroProject::refused(project.native_with_syntax(
        "check-source",
        false_proof,
        Some(&project.partition),
        &selected,
    ));

    // A nonterminating macro cannot be treated as an ordinary failed branch.
    let looped = concat!(
        "prelude\nimport AdmittedSourceMacro\n",
        "theorem nonanswer (n : Nat) : Eq n n := by first | imported_loop | rfl\n",
    );
    let output =
        project.native_with_syntax("check-source", looped, Some(&project.partition), &selected);
    assert_eq!(output.status.code(), Some(3), "{output:?}");
    let refusal = ImportedMacroProject::refused(output);
    assert!(
        refusal.contains("\"outcome\":\"inconclusive\""),
        "{refusal}"
    );
    assert!(refusal.contains("\"authority\":false"), "{refusal}");
}
