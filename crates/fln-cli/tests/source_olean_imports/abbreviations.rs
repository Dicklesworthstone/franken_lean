//! Real Reference-produced abbreviation descriptions and MacroM IR, loaded
//! through the production import council and used without client syntax.
#![forbid(unsafe_code)]

use super::*;

fn provider() -> String {
    format!(
        "{}\n{}",
        include_str!("../../../fln-olean/fixtures/ir/AdmittedSourceMacro.lean"),
        concat!(
            "public syntax admittedNumber := num\n",
            "public syntax admittedHead := \"head%\"\n",
            "public syntax admittedPayload := \"[\" admittedNumber \"]\"\n",
            "syntax (name := admittedAbbrev) \"abbrev%\" admittedNumber : term\n",
            "@[macro admittedAbbrev]\n",
            "public meta def admittedAbbrevMacro : Macro := fun stx _ state =>\n",
            "  .ok ((stx.getArg 1).getArg 0) state\n",
            "syntax (name := admittedAbbrevHead) admittedHead term:1024 : term\n",
            "@[macro admittedAbbrevHead]\n",
            "public meta def admittedAbbrevHeadMacro : Macro := fun stx _ state =>\n",
            "  .ok (stx.getArg 1) state\n",
            "syntax (name := admittedPacket) \"packet%\" admittedPayload : term\n",
            "@[macro admittedPacket]\n",
            "public meta def admittedPacketMacro : Macro := fun stx _ state =>\n",
            "  .ok (((stx.getArg 1).getArg 1).getArg 0) state\n",
        ),
    )
}

const CLIENT: &str = concat!(
    "prelude\nimport AdmittedSourceMacro\n",
    "def commandMacroValue : Nat := (11 : Bool)\n",
    "def numberValue : Nat := abbrev% 41\n",
    "theorem numberValue_eq : Eq numberValue 41 := Eq.refl numberValue\n",
    "def headValue : Nat := head% 43\n",
    "theorem headValue_eq : Eq headValue 43 := Eq.refl headValue\n",
    "def nestedValue : Nat := packet% [47]\n",
    "theorem nestedValue_eq : Eq nestedValue 47 := Eq.refl nestedValue\n",
);

#[test]
fn installed_imported_syntax_abbreviations_reach_macro_execution_and_admission() {
    let Some(project) = ImportedMacroProject::prepare_with_source(&provider()) else {
        return;
    };
    let selected = ["AdmittedSourceMacro"];
    let report = project.check_with_syntax(CLIENT, &selected);
    assert!(report.contains("\"theorems\":3"), "{report}");
    for declaration in [
        "admittedAbbrevMacro",
        "admittedAbbrevHeadMacro",
        "admittedPacketMacro",
    ] {
        assert!(
            report.contains(&format!(
                "{{\"name\":\"{declaration}\",\"producer\":\"reference\"}}"
            )),
            "{report}"
        );
    }

    let queries = format!("{CLIENT}#check numberValue\n#check headValue\n#check nestedValue\n");
    let oracle = project.oracle(&queries);
    assert!(oracle.status.success(), "{oracle:?}");
    assert!(oracle.stderr.is_empty(), "{oracle:?}");
    assert_eq!(
        oracle.stdout,
        b"numberValue : Nat\nheadValue : Nat\nnestedValue : Nat\n"
    );
    let native = project.native_with_syntax("lean", &queries, Some(&project.partition), &selected);
    assert!(native.status.success(), "{native:?}");
    assert!(native.stderr.is_empty(), "{native:?}");
    assert_eq!(native.stdout, oracle.stdout);

    let executable = format!("{CLIENT}#eval numberValue\n#eval headValue\n#eval nestedValue\n");
    let executed =
        project.native_with_syntax("run", &executable, Some(&project.partition), &selected);
    assert!(executed.status.success(), "{executed:?}");
    assert!(executed.stderr.is_empty(), "{executed:?}");
    let report = String::from_utf8(executed.stdout).unwrap();
    assert_imported_macro_provenance(&report);
    for value in [41, 43, 47] {
        assert!(
            report.contains(&format!("\"kind\":\"nat\",\"value\":{value}")),
            "{report}"
        );
    }
    assert_eq!(report.matches("\"event\":\"evaluation\"").count(), 3);

    // The parser selection is necessary, and it grants no theorem authority.
    ImportedMacroProject::refused(project.native("lean", CLIENT, Some(&project.partition)));
    for rejected in [
        format!("{CLIENT}theorem falseResult : Eq nestedValue 48 := Eq.refl nestedValue\n"),
        format!("{CLIENT}def malformed : Nat := packet% [true]\n"),
    ] {
        let oracle = project.oracle(&rejected);
        assert!(!oracle.status.success(), "{oracle:?}");
        ImportedMacroProject::refused(project.native_with_syntax(
            "lean",
            &rejected,
            Some(&project.partition),
            &selected,
        ));
    }
}
