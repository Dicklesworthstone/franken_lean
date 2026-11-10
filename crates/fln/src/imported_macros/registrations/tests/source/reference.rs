//! Actual pinned Lean source macros, decoded from their emitted attribute
//! journal and executed by native counterparts or imported user IR before the
//! Engine's ordinary checker.
use super::*;
use fln_olean::region::{OleanView, WalkBudget};
use std::path::PathBuf;
use std::process::Command;

const SEQUENCING_OWNERS: [(&str, &str); 3] = [
    ("term_<*>_", "_aux_Init_Notation___macroRules_term_<*>__1"),
    ("term_<*_", "_aux_Init_Notation___macroRules_term_<*__1"),
    ("term_*>_", "_aux_Init_Notation___macroRules_term_*>__1"),
];

const CONDITIONAL_OWNERS: [(&str, &str, &str); 2] = [
    (
        "boolIfThenElse",
        "_aux_Init_Notation___macroRules_boolIfThenElse_1",
        "app",
    ),
    (
        "termIfLet",
        "_aux_Init_Notation___macroRules_termIfLet_1",
        "match",
    ),
];

const OPERATOR_KINDS: [(&str, &str); 20] = [
    ("term_|||_", "binop"),
    ("term_^^^_", "binop"),
    ("term_&&&_", "binop"),
    ("term_+_", "binop"),
    ("term_-_", "binop"),
    ("term_*_", "binop"),
    ("term_/_", "binop"),
    ("term_%_", "binop"),
    ("term_++_", "binop"),
    ("term_^_", "rightact"),
    ("term_•_", "leftact"),
    ("term-_", "unop"),
    ("term_>=_", "binrel"),
    ("term_<=_", "binrel"),
    ("term_≤_", "binrel"),
    ("term_<_", "binrel"),
    ("term_>_", "binrel"),
    ("term_≥_", "binrel"),
    ("term_=_", "binrel"),
    ("term_==_", "binrel_no_prop"),
];

const BINDER_OWNERS: [(&str, &str); 6] = [
    (
        "term∃_,_",
        "_aux_Init_NotationExtra___macroRules_term∃_,__1",
    ),
    (
        "termExists_,_",
        "_aux_Init_NotationExtra___macroRules_termExists_,__1",
    ),
    (
        "termΣ_,_",
        "_aux_Init_NotationExtra___macroRules_termΣ_,__1",
    ),
    (
        "termΣ'_,_",
        "_aux_Init_NotationExtra___macroRules_termΣ'_,__1",
    ),
    (
        "term_×__1",
        "_aux_Init_NotationExtra___macroRules_term_×__1_1",
    ),
    (
        "term_×'__1",
        "_aux_Init_NotationExtra___macroRules_term_×'__1_1",
    ),
];

#[test]
fn pinned_sequencing_registry_binds_authority_and_serves_recursive_user_macros() {
    quotation_registry_controls(
        "Init.Notation",
        &SEQUENCING_OWNERS.map(|(kind, owner)| (kind, owner, "app")),
        operator_input,
    );
}

#[test]
fn pinned_conditional_registry_binds_authority_and_serves_recursive_user_macros() {
    quotation_registry_controls("Init.Notation", &CONDITIONAL_OWNERS, conditional_input);
}

fn conditional_input(kind: &str) -> Syntax {
    let atom = |text| Syntax::atom(SourceInfo::None, text);
    let capture = |label| Syntax::node(name(label), vec![atom("captured operand")]);
    let args = if kind == "boolIfThenElse" {
        vec![
            atom("bif"),
            capture("Client.condition"),
            atom("then"),
            capture("Client.then"),
            atom("else"),
            capture("Client.else"),
        ]
    } else {
        vec![
            atom("if"),
            atom("let"),
            capture("Client.pattern"),
            atom(":="),
            capture("Client.discriminant"),
            atom("then"),
            capture("Client.then"),
            atom("else"),
            capture("Client.else"),
        ]
    };
    Syntax::node(name(kind), args)
}

#[test]
fn pinned_operator_registry_binds_authority_and_serves_recursive_user_macros() {
    let owners =
        OPERATOR_KINDS.map(|(kind, _)| format!("_aux_Init_Notation___macroRules_{kind}_2"));
    let candidates: Vec<_> = OPERATOR_KINDS
        .iter()
        .zip(&owners)
        .map(|(&(kind, helper), owner)| (kind, owner.as_str(), helper))
        .collect();
    quotation_registry_controls("Init.Notation", &candidates, operator_input);
}

#[test]
fn pinned_binder_registry_binds_authority_and_serves_recursive_user_macros() {
    quotation_registry_controls(
        "Init.NotationExtra",
        &BINDER_OWNERS.map(|(kind, owner)| (kind, owner, "app")),
        binder_input,
    );
}

fn operator_input(kind: &str) -> Syntax {
    let rhs = Syntax::node(
        name("unexpandedRhs"),
        vec![Syntax::atom(SourceInfo::None, "right operand")],
    );
    Syntax::node(
        name(kind),
        if kind == "term-_" {
            vec![Syntax::atom(SourceInfo::None, "-"), rhs]
        } else {
            vec![
                Syntax::atom(SourceInfo::None, "left operand"),
                Syntax::atom(SourceInfo::None, "operator"),
                rhs,
            ]
        },
    )
}

fn binder_input(kind: &str) -> Syntax {
    let atom = |value| Syntax::atom(SourceInfo::None, value);
    let null = |args| Syntax::node(name("null"), args);
    let identifier = Syntax::Ident {
        info: SourceInfo::None,
        raw_val: fln_syntax::source::ByteSpan::default().into(),
        val: name("capturedBinder"),
        preresolved: Vec::new(),
    };
    let binders = null(vec![
        Syntax::node(name("Lean.binderIdent"), vec![identifier]),
        Syntax::node(
            name("Lean.binderIdent"),
            vec![Syntax::node(name("Lean.Parser.Term.hole"), vec![atom("_")])],
        ),
    ]);
    let domain = Syntax::node(name("capturedDomain"), vec![atom("domain")]);
    let body = Syntax::node(name("capturedBody"), vec![atom("body")]);
    if matches!(kind, "term_×__1" | "term_×'__1") {
        let group = Syntax::node(
            name("Lean.bracketedExplicitBinders"),
            vec![atom("("), binders, atom(":"), domain, atom(")")],
        );
        Syntax::node(
            name(kind),
            vec![
                group,
                atom(if kind == "term_×__1" { "×" } else { "×'" }),
                body,
            ],
        )
    } else {
        let keyword = match kind {
            "term∃_,_" => "∃",
            "termExists_,_" => "exists",
            "termΣ_,_" => "Σ",
            "termΣ'_,_" => "Σ'",
            _ => panic!("unexpected binder notation: {kind}"),
        };
        let binders = Syntax::node(
            name("Lean.explicitBinders"),
            vec![Syntax::node(
                name("Lean.unbracketedExplicitBinders"),
                vec![binders, null(vec![atom(":"), domain])],
            )],
        );
        Syntax::node(name(kind), vec![atom(keyword), binders, atom(","), body])
    }
}

fn quotation_registry_controls(
    module: &str,
    candidates: &[(&str, &str, &str)],
    input: fn(&str) -> Syntax,
) {
    let Some(path) = std::env::var_os("FLN_REFERENCE_PARTITION").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "quotation registry requires the verified pinned partition"
        );
        eprintln!("SKIP: quotation registry requires FLN_REFERENCE_PARTITION");
        return;
    };
    let partition =
        VerifiedPartition::from_pinned_tsv(&std::fs::read_to_string(path).unwrap()).unwrap();
    // These are constructed ownership records, as in the parent registry
    // tests. They isolate dispatch and authority; actual artifact admission
    // and checked source meaning are covered by the live import cell below.
    let constants: Vec<_> = candidates
        .iter()
        .map(|(_, declaration, _)| owner(declaration))
        .collect();
    let native = checked(module, &constants, &[]);
    let client = checked(
        "SequenceClient",
        &[owner("SequenceClient.expand")],
        &[module],
    );
    let rows = journal(
        &candidates
            .iter()
            .map(|&(kind, declaration, _)| (kind, declaration, None))
            .collect::<Vec<_>>(),
    );
    let client_rows = journal(&[("sequenceOuter", "SequenceClient.expand", None)]);
    let code = code(vec![
        super::super::recursive::recursive_function_requiring_child("SequenceClient.expand", 0),
    ]);
    let registry = RegisteredMacros::prepare(
        &[
            MacroRegistrationModule {
                checked: &native,
                extensions: &rows,
            },
            MacroRegistrationModule {
                checked: &client,
                extensions: &client_rows,
            },
        ],
        &environment(&[&native, &client]),
        &code,
        &partition,
        &users(&code),
        MacroRegistryLimits::default(),
    )
    .unwrap();
    let source = SourceText::from_utf8(b"").unwrap();
    let dispatch = |input: &Syntax, scope| {
        registry.expand_root(
            input,
            &source,
            &context(),
            MacroState {
                macro_scope: scope,
                ..MacroState::default()
            },
            MacroDispatchLimits::default(),
            None,
        )
    };
    for &(kind, declaration, helper) in candidates {
        let child = input(kind);
        let outer = Syntax::node(name("sequenceOuter"), vec![child.clone()]);
        let nested = dispatch(&outer, 17);
        // The nested invocation receives the scope after the user macro's
        // fresh scope. Compare against the same ordinary registry route with
        // that starting state, including all quotation metadata and captures.
        let direct = dispatch(&child, 18);
        let Outcome::Complete(Ok(RegisteredExpansion::Expanded { syntax, state, .. })) =
            &nested.outcome
        else {
            panic!("{nested:?}")
        };
        let Outcome::Complete(Ok(RegisteredExpansion::Expanded {
            syntax: expected, ..
        })) = &direct.outcome
        else {
            panic!("{direct:?}")
        };
        assert_eq!(syntax, expected);
        assert_eq!(
            syntax.kind(),
            Some(&Name::from_components(["Lean", "Parser", "Term", helper]))
        );
        assert_eq!(state.macro_scope, 19);
        assert_eq!(
            state.expanded_macro_declarations,
            vec![name("SequenceClient.expand"), name(declaration)]
        );
        assert_eq!(nested.attempts.len(), 2);
        assert_eq!(
            nested.attempts[0].declaration,
            name("SequenceClient.expand")
        );
        assert!(
            nested.attempts[0]
                .native_functions
                .iter()
                .any(|function| { function == "mirror:Lean.Macro.expandMacro?" })
        );
        assert_eq!(nested.attempts[1].declaration, name(declaration));
        assert!(nested.attempts[1].reference_functions.is_empty());
        assert!(
            nested.attempts[1]
                .native_functions
                .iter()
                .any(|function| function == &format!("mirror:{declaration}"))
        );
    }

    // An exact generated declaration spelling conveys no native authority
    // without both its checked module identity and census classification.
    let wrong_module = checked("User.Notation", &constants, &[]);
    let unclassified = VerifiedPartition::user_fixture();
    for (module, classification) in [(&wrong_module, &partition), (&native, &unclassified)] {
        for &(kind, declaration, _) in candidates {
            let rows = journal(&[(kind, declaration, None)]);
            let refused = RegisteredMacros::prepare(
                &[MacroRegistrationModule {
                    checked: module,
                    extensions: &rows,
                }],
                &environment(&[module]),
                &[],
                classification,
                &BTreeSet::new(),
                MacroRegistryLimits::default(),
            );
            assert!(
                matches!(refused, Err(MacroRegistrationError::Compile {
                    declaration: ref attempted, ..
                }) if attempted == &name(declaration)),
                "{declaration}: {refused:?}"
            );
        }
    }
}

#[test]
fn live_pinned_sequencing_macros_preserve_thunks_hygiene_and_checked_meaning() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from);
    let library = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from);
    let partition = std::env::var_os("FLN_REFERENCE_PARTITION").map(PathBuf::from);
    let (Some(reference), Some(library), Some(partition)) = (reference, library, partition) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "native sequencing requires the pinned executable, library and partition"
        );
        eprintln!("SKIP: set FLN_REFERENCE_LEAN, FLN_REFERENCE_LIB and FLN_REFERENCE_PARTITION");
        return;
    };
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || sequencing_from_actual_imports(reference, library, partition))
        .unwrap()
        .join()
        .unwrap();
}

fn sequencing_from_actual_imports(reference: PathBuf, library: PathBuf, partition: PathBuf) {
    use crate::imported_macros::registrations::MacroCompilationInputs;
    use crate::source_check::SourceCheckLimits;
    use crate::source_check::modules::imported::SourceOleanImportLimits;
    use crate::{Budget, OleanCheckLimits, OleanModuleInput};

    let version = Command::new(&reference)
        .args(["-j1", "--githash"])
        .output()
        .unwrap();
    assert!(version.status.success());
    assert_eq!(
        String::from_utf8(version.stdout).unwrap().trim(),
        format::PIN_COMMIT
    );
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!("sequencing-source-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let source = r#"
def sequenceFunction (f : Option (Nat → Nat)) (x : Option Nat) : Option Nat := f <*> x
def sequenceLeft (x y : Option Nat) : Option Nat := x <* y
def sequenceRight (x y : Option Nat) : Option Nat := x *> y
def sequenceShadow (Unit : Type) (SeqRight : Nat) (x y : Option Nat) : Option Nat := x *> y
theorem sequenceFunction_thunk (f : Option (Nat → Nat)) (x : Option Nat) :
    Eq (sequenceFunction f x) (Seq.seq f (fun _ : Unit => x)) := rfl
theorem sequenceLeft_thunk (x y : Option Nat) :
    Eq (sequenceLeft x y) (SeqLeft.seqLeft x (fun _ : Unit => y)) := rfl
theorem sequenceRight_thunk (x y : Option Nat) :
    Eq (sequenceRight x y) (SeqRight.seqRight x (fun _ : Unit => y)) := rfl
theorem sequenceFunction_value :
    Eq (some (fun n : Nat => Nat.succ n) <*> some 40) (some 41) := rfl
theorem sequenceAssociation_value :
    Eq (some (fun a b : Nat => Nat.add a b) <*> some 7 <*> some 11) (some 18) := rfl
theorem sequenceDirections_value : Eq (some 7 <* some 11 *> some 13) (some 13) := rfl
theorem sequenceLeft_none : Eq (some 7 <* (none : Option Nat)) none := rfl
theorem sequenceRight_none : Eq ((none : Option Nat) *> some 7) none := rfl
theorem sequenceShadow_value : Eq (sequenceShadow Nat 99 (some 7) (some 11)) (some 11) := rfl
def operatorArithmetic (n : Nat) : Nat := (n + 3) * 5 - 2
def operatorDivision (n : Nat) : Nat := n / 3 + n % 3
def operatorPower (n : Nat) : Nat := 2 ^ n
def operatorBits [HOr Nat Nat Nat] [HXor Nat Nat Nat] [HAnd Nat Nat Nat]
    (x y : Nat) : Nat := (x ||| y) ^^^ (x &&& y)
def operatorAppend [HAppend (List Nat) (List Nat) (List Nat)]
    (xs ys : List Nat) : List Nat := xs ++ ys
def operatorNegative {α : Type} [Neg α] (x : α) : α := -x
def operatorScale [HSMul Nat Nat Nat] (n x : Nat) : Nat := n • x
def operatorEqShadow (Eq : Nat) (x y : Nat) : Prop := x = y
def operatorBoolean (x y : Nat) : Bool := x == y
def operatorLess (x y : Nat) : Prop := x < y
def operatorGreater (x y : Nat) : Prop := x > y
def operatorLe (x y : Nat) : Prop := x ≤ y
def operatorGe (x y : Nat) : Prop := x ≥ y
def operatorLeAscii (x y : Nat) : Prop := x <= y
def operatorGeAscii (x y : Nat) : Prop := x >= y
theorem operatorArithmetic_value : operatorArithmetic 7 = 48 := rfl
theorem operatorDivision_value : operatorDivision 11 = 5 := rfl
theorem operatorPower_value : operatorPower 3 = 8 := rfl
theorem operatorBoolean_value : operatorBoolean 7 7 = true := rfl
theorem operatorEqShadow_value : operatorEqShadow 99 7 7 := rfl
theorem operatorGreater_direction (x y : Nat) : operatorGreater x y = (y < x) := rfl
theorem operatorAscii_value (x y : Nat) : operatorLeAscii x y = operatorLe x y := rfl
def binderExists (P : Nat → Nat → Prop) : Prop := ∃ x y : Nat, P x y
def binderExistsAscii (P : Nat → Prop) : Prop := exists x, P x
def binderDependentExists (P : (A : Type) → A → Prop) : Prop := ∃ (A : Type) (x : A), P A x
def binderAnonymousExists (P : Prop) : Prop := ∃ _ : Nat, P
def binderExistsShadow (Exists : Nat) (P : Nat → Prop) : Prop := ∃ x, P x
def binderSigma (P : Nat → Type) : Type := Σ x : Nat, P x
def binderSigmaInferred (P : Nat → Type) : Type := Σ x, P x
def binderSigmaGrouped (P : Nat → Nat → Type) : Type := Σ (x y : Nat), P x y
def binderDependentSigma : Type 1 := Σ (A : Type) (x : A), A
def binderSigmaShadow (Sigma : Nat) (P : Nat → Type) : Type := Σ x : Nat, P x
def binderPSigma (P : Prop) : Type := Σ' h : P, Eq h h
def binderPSigmaShadow (PSigma : Nat) (P : Prop) : Type := Σ' _ : P, Nat
def binderDependentProduct (P : Nat → Type) : Type := (x : Nat) × P x
def binderDependentPProduct (P : Prop) : Type := (h : P) ×' Eq h h
def binderAnonymousSigma (P : Type) : Type := Σ _ : Nat, P
def binderSigmaValue : binderSigma (fun _ : Nat => Nat) := ⟨7, 11⟩
theorem binderExists_shape (P : Nat → Nat → Prop) :
    binderExists P = Exists (fun x : Nat => Exists (fun y : Nat => P x y)) := rfl
theorem binderExistsAscii_shape (P : Nat → Prop) :
    binderExistsAscii P = Exists (fun x : Nat => P x) := rfl
theorem binderExistsShadow_shape (P : Nat → Prop) :
    binderExistsShadow 99 P = Exists (fun x : Nat => P x) := rfl
theorem binderSigmaValue_fst : binderSigmaValue.1 = 7 := rfl
theorem binderSigmaValue_snd : binderSigmaValue.2 = 11 := rfl
theorem binderExists_intro : ∃ x y : Nat, x = y := ⟨7, 7, rfl⟩
def conditionalBoolean (b : Bool) (yes no : Nat) : Nat := bif b then yes else no
def conditionalShadow (cond : Nat) (b : Bool) : Nat := bif b then 7 else 11
def conditionalPattern (x : Option Nat) : Nat := if let some n := x then n else 13
def conditionalPatternShadow (x : Option Nat) (n : Nat) : Nat :=
    if let some n := x then n else n
theorem conditionalBoolean_true : Eq (conditionalBoolean true 7 11) 7 := rfl
theorem conditionalBoolean_false : Eq (conditionalBoolean false 7 11) 11 := rfl
theorem conditionalPattern_some : Eq (conditionalPattern (some 7)) 7 := rfl
theorem conditionalPattern_none : Eq (conditionalPattern none) 13 := rfl
theorem conditionalPatternShadow_some : Eq (conditionalPatternShadow (some 7) 11) 7 := rfl
theorem conditionalPatternShadow_none : Eq (conditionalPatternShadow none 11) 11 := rfl
"#;
    let header =
        "module\nprelude\npublic import Init.NotationExtra\npublic section\n@[expose] section\n";
    std::fs::write(dir.join("Sequencing.lean"), format!("{header}{source}")).unwrap();
    let oracle = Command::new(&reference)
        .current_dir(&dir)
        .args(["-j1", "-o", "Sequencing.olean", "Sequencing.lean"])
        .output()
        .unwrap();
    std::fs::write(dir.join("oracle.stdout"), &oracle.stdout).unwrap();
    std::fs::write(dir.join("oracle.stderr"), &oracle.stderr).unwrap();
    assert!(oracle.status.success(), "{oracle:?}; {dir:?}");
    let oracle_parts = ["olean", "olean.server", "olean.private"]
        .map(|extension| std::fs::read(dir.join(format!("Sequencing.{extension}"))).unwrap());
    let oracle_module = crate::decode_olean_module_artifacts(
        &oracle_parts[0],
        &oracle_parts[1],
        &oracle_parts[2],
        OleanDecodeLimits::new(oracle_parts.iter().map(Vec::len).sum()),
    )
    .unwrap();

    // Import the actual closure and its entire macro journal. Synthetic owners
    // or a registry filtered down to the new candidates cannot establish the
    // ordinary import-to-source route or its candidate ordering.
    let target = name("Init.NotationExtra");
    let mut pending = vec![target.clone()];
    let mut seen = BTreeSet::new();
    let mut loaded = Vec::new();
    while let Some(module) = pending.pop() {
        if !seen.insert(module.clone()) {
            continue;
        }
        let base = library.join(module.to_display_string().replace('.', "/"));
        let parts = ["olean", "olean.server", "olean.private"]
            .map(|extension| std::fs::read(base.with_extension(extension)).unwrap());
        pending.extend(
            crate::olean_module_imports(&parts[0], OleanDecodeLimits::new(parts[0].len())).unwrap(),
        );
        loaded.push((module, parts));
    }
    let inputs: Vec<_> = loaded
        .iter()
        .map(|(name, parts)| OleanModuleInput {
            name,
            artifact: &parts[0],
            server_artifact: Some(&parts[1]),
            private_artifact: Some(&parts[2]),
        })
        .collect();
    let options = KVMap::new();
    let imported = Engine::from_environment(Environment::new())
        .import_olean_modules_for_source(
            &inputs,
            std::slice::from_ref(&target),
            &options,
            SourceOleanImportLimits::new(OleanCheckLimits::new(
                1 << 30,
                Budget::for_stack_bytes(64 * 1024 * 1024),
            )),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(imported.checked.modules.len(), loaded.len());
    let partition =
        VerifiedPartition::from_pinned_tsv(&std::fs::read_to_string(partition).unwrap()).unwrap();
    let compilation = MacroCompilationInputs::new(Vec::new(), partition, BTreeSet::new());
    let limited = imported
        .prepare_imported_macros_deferred(
            compilation.clone(),
            MacroRegistryLimits {
                max_macros: 256,
                ..MacroRegistryLimits::default()
            },
        )
        .unwrap_err();
    assert!(
        matches!(limited, MacroRegistrationError::Limit("compiled macros")),
        "{limited:?}"
    );
    let registry = imported
        .prepare_imported_macros_deferred(compilation, MacroRegistryLimits::default())
        .unwrap();
    // The exact pinned census has 284 distinct macro owners in this 51-module
    // closure. Ordinary defaults must retain its complete table, including
    // inactive scoped entries, instead of selecting only executable candidates.
    assert_eq!(registry.owners.len(), 284);
    let retained: BTreeSet<_> = registry
        .global
        .values()
        .chain(registry.scoped.values().flat_map(|table| table.values()))
        .flat_map(|chain| chain.iter().map(|entry| &entry.declaration))
        .collect();
    assert_eq!(retained, registry.owners.keys().collect());
    for (kind, owner) in SEQUENCING_OWNERS {
        assert_eq!(
            registry.declarations(&name(kind)).collect::<Vec<_>>(),
            vec![&name(owner)]
        );
    }
    for (kind, owner, _) in CONDITIONAL_OWNERS {
        assert_eq!(
            registry.declarations(&name(kind)).collect::<Vec<_>>(),
            vec![&name(owner)],
            "the complete journal must retain the conditional owner: {kind}"
        );
    }
    for (kind, _) in OPERATOR_KINDS {
        assert_eq!(
            registry
                .declarations(&name(kind))
                .cloned()
                .collect::<Vec<_>>(),
            [2, 1].map(|index| name(&format!("_aux_Init_Notation___macroRules_{kind}_{index}"))),
            "the complete journal must try the expression-tree rule first: {kind}"
        );
    }
    for (kind, owner) in BINDER_OWNERS {
        assert_eq!(
            registry.declarations(&name(kind)).collect::<Vec<_>>(),
            vec![&name(owner)],
            "the complete journal must retain the exact binder owner: {kind}"
        );
    }
    let engine = &imported.engine;
    let before = engine.logical_root(&options);
    let run = |source: &[u8], limits| {
        engine.check_source_files_with_imported_macros(
            &[source],
            &options,
            SourceCheckLimits::new(admission()),
            SourceMacroInvocation {
                registry: &registry,
                context: &context(),
                state: MacroState::default(),
                lookup: None,
                limits,
                cancellation: None,
            },
        )
    };
    let report = run(source.as_bytes(), MacroTreeLimits::default());
    let Outcome::Complete(Ok(checked)) = &report.outcome else {
        panic!("notation source: {report:?}; {dir:?}");
    };
    assert!(report.state.is_some());
    assert_eq!(
        (checked.files, checked.commands, checked.theorems),
        (1, 67, 28)
    );
    for (_, owner) in SEQUENCING_OWNERS {
        assert!(report.attempts.iter().any(|attempt| {
            attempt.declaration == name(owner)
                && attempt
                    .native_functions
                    .iter()
                    .any(|id| id == &format!("mirror:{owner}"))
                && attempt.reference_functions.is_empty()
        }));
    }
    for (kind, owner, _) in CONDITIONAL_OWNERS {
        assert!(
            report.attempts.iter().any(|attempt| {
                attempt.declaration == name(owner)
                    && attempt
                        .native_functions
                        .iter()
                        .any(|id| id == &format!("mirror:{owner}"))
                    && attempt.reference_functions.is_empty()
            }),
            "native conditional was not exercised: {kind}"
        );
    }
    // ASCII relation spellings can parse to the canonical Unicode syntax
    // kinds. Their legacy kinds are covered separately by recursive dispatch.
    for (kind, _) in OPERATOR_KINDS {
        if matches!(kind, "term_<=_" | "term_>=_") {
            continue;
        }
        let owner = format!("_aux_Init_Notation___macroRules_{kind}_2");
        assert!(
            report.attempts.iter().any(|attempt| {
                attempt.declaration == name(&owner)
                    && attempt
                        .native_functions
                        .iter()
                        .any(|id| id == &format!("mirror:{owner}"))
                    && attempt.reference_functions.is_empty()
            }),
            "native operator was not exercised: {kind}"
        );
    }
    assert!(!report.attempts.iter().any(|attempt| {
        OPERATOR_KINDS.iter().any(|(kind, _)| {
            attempt.declaration == name(&format!("_aux_Init_Notation___macroRules_{kind}_1"))
        })
    }));
    for (kind, owner) in BINDER_OWNERS {
        assert!(
            report.attempts.iter().any(|attempt| {
                attempt.declaration == name(owner)
                    && attempt
                        .native_functions
                        .iter()
                        .any(|id| id == &format!("mirror:{owner}"))
                    && attempt.reference_functions.is_empty()
            }),
            "native binder notation was not exercised: {kind}"
        );
    }
    // Compare the actual checked functions to the pin's emitted terms. This
    // includes the Unit thunk's type, each operator's chosen typeclass method,
    // and operands beneath local binders. Result values alone would miss
    // capture defects and operators with deliberately local instances.
    for label in [
        "sequenceFunction",
        "sequenceLeft",
        "sequenceRight",
        "sequenceShadow",
        "operatorArithmetic",
        "operatorDivision",
        "operatorPower",
        "operatorBits",
        "operatorAppend",
        "operatorNegative",
        "operatorScale",
        "operatorEqShadow",
        "operatorBoolean",
        "operatorLess",
        "operatorGreater",
        "operatorLe",
        "operatorGe",
        "operatorLeAscii",
        "operatorGeAscii",
        "binderExists",
        "binderExistsAscii",
        "binderDependentExists",
        "binderAnonymousExists",
        "binderExistsShadow",
        "binderSigma",
        "binderSigmaInferred",
        "binderSigmaGrouped",
        "binderDependentSigma",
        "binderSigmaShadow",
        "binderPSigma",
        "binderPSigmaShadow",
        "binderDependentProduct",
        "binderDependentPProduct",
        "binderAnonymousSigma",
        "binderSigmaValue",
        "conditionalBoolean",
        "conditionalShadow",
    ] {
        let Some(ConstantInfo::Defn(actual)) = checked.engine.environment().find(&name(label))
        else {
            panic!("native checked definition missing: {label}");
        };
        let Some(ConstantInfo::Defn(expected)) = oracle_module
            .constants
            .iter()
            .find(|constant| constant.constant_val().name == name(label))
        else {
            panic!("oracle definition missing: {label}");
        };
        assert_eq!(actual.base.level_params, expected.base.level_params);
        for (left, right) in [
            (&actual.base.type_, &expected.base.type_),
            (&actual.value, &expected.value),
        ] {
            let verdict = fln_kernel::check_def_eq(
                checked.engine.environment(),
                &actual.base.level_params,
                left,
                right,
                admission().kernel,
            );
            assert!(
                matches!(
                    verdict,
                    Outcome::Complete(fln_kernel::verdict::Verdict::Accepted { .. })
                ),
                "{label}: {verdict:?}; {dir:?}"
            );
        }
    }
    for (label, suffix) in [
        (
            "wrongFunction",
            "def wrongFunction : Option Nat := some 7 <*> some 11",
        ),
        (
            "wrongResult",
            "theorem wrongResult : Eq (some 7 *> some 11) (some 7) := rfl",
        ),
        (
            "wrongOperatorType",
            "def wrongOperatorType : Nat := 1 + true",
        ),
        (
            "wrongOperatorValue",
            "theorem wrongOperatorValue : 2 + 3 * 4 = 20 := rfl",
        ),
        (
            "wrongExistsBody",
            "def wrongExistsBody : Prop := exists n : Nat, n",
        ),
        (
            "wrongSigmaBody",
            "def wrongSigmaBody : Type := Σ n : Nat, n",
        ),
        (
            "escapedBinder",
            "def escapedBinder : Nat := (fun _ : (∃ x : Nat, True) => x) (Exists.intro 7 True.intro)",
        ),
        (
            "wrongBooleanCondition",
            "def wrongBooleanCondition : Nat := bif (1 : Nat) then 7 else 11",
        ),
        (
            "wrongPatternResult",
            "theorem wrongPatternResult : Eq (conditionalPattern (some 7)) 13 := rfl",
        ),
        (
            "escapedPatternBinder",
            "def escapedPatternBinder (x : Option Nat) : Nat := if let some n := x then n else n",
        ),
    ] {
        let rejected_source = format!("{source}\n{suffix}\n");
        let filename = format!("{label}.lean");
        std::fs::write(dir.join(&filename), format!("{header}{rejected_source}")).unwrap();
        let rejected = Command::new(&reference)
            .current_dir(&dir)
            .args(["-j1", &filename])
            .output()
            .unwrap();
        std::fs::write(dir.join(format!("{label}.stdout")), &rejected.stdout).unwrap();
        std::fs::write(dir.join(format!("{label}.stderr")), &rejected.stderr).unwrap();
        assert!(!rejected.status.success(), "{label}: {rejected:?}");
        let refused = run(rejected_source.as_bytes(), MacroTreeLimits::default());
        assert!(
            matches!(refused.outcome, Outcome::Complete(Err(_))),
            "{label}: {refused:?}"
        );
        assert!(refused.state.is_none());
    }
    let mut limited = MacroTreeLimits::default();
    limited.dispatch.max_attempts = 0;
    let stopped = run(source.as_bytes(), limited);
    assert!(
        matches!(stopped.outcome, Outcome::Inconclusive(_)),
        "{stopped:?}"
    );
    assert!(stopped.state.is_none());
    assert_eq!(engine.logical_root(&options), before);
    assert!(!engine.environment().contains(&name("sequenceFunction")));
}

#[test]
fn live_pinned_composite_tactics_admit_source_from_complete_import_journals() {
    let reference = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from);
    let library = std::env::var_os("FLN_REFERENCE_LIB").map(PathBuf::from);
    let partition = std::env::var_os("FLN_REFERENCE_PARTITION").map(PathBuf::from);
    let (Some(reference), Some(library), Some(partition)) = (reference, library, partition) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "native composite source tactics require the pinned executable, library and partition"
        );
        eprintln!("SKIP: set FLN_REFERENCE_LEAN, FLN_REFERENCE_LIB and FLN_REFERENCE_PARTITION");
        return;
    };
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(move || composite_tactics_from_actual_imports(reference, library, partition))
        .unwrap()
        .join()
        .unwrap();
}

fn composite_tactics_from_actual_imports(reference: PathBuf, library: PathBuf, partition: PathBuf) {
    use crate::imported_macros::registrations::MacroCompilationInputs;
    use crate::imported_macros::source::SourceMacroFileCheck;
    use crate::source_check::modules::imported::SourceOleanImportLimits;
    use crate::source_check::{SourceCheckError, SourceCheckLimits};
    use crate::{Budget, OleanCheckLimits, OleanModuleInput};

    let version = Command::new(&reference)
        .args(["-j1", "--githash"])
        .output()
        .unwrap();
    assert!(version.status.success());
    assert_eq!(
        String::from_utf8(version.stdout).unwrap().trim(),
        format::PIN_COMMIT
    );
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!("composite-source-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();

    let cases = [
        (
            "rwaTarget",
            true,
            "theorem rwaTarget (P : Nat → Prop) (n m : Nat) (h : Eq n m) (hm : P m) : P n := by rwa [h]",
        ),
        (
            "rwaReverse",
            true,
            "theorem rwaReverse (P : Nat → Prop) (n m : Nat) (h : Eq n m) (hn : P n) : P m := by rwa [← h]",
        ),
        (
            "rwaHyp",
            true,
            "theorem rwaHyp (P : Nat → Prop) (n m : Nat) (h : Eq n m) (hn : P n) : P m := by rwa [h] at hn",
        ),
        (
            "trivialTrue",
            true,
            "theorem trivialTrue : True := by trivial",
        ),
        (
            "trivialAssumption",
            true,
            "theorem trivialAssumption (P : Prop) (h : P) : P := by trivial",
        ),
        (
            "trivialRefl",
            true,
            "theorem trivialRefl (α : Type) (x : α) : Eq x x := by trivial",
        ),
        (
            "trivialContradiction",
            true,
            "theorem trivialContradiction (P : Prop) (h : False) : P := by trivial",
        ),
        (
            "trivialDecide",
            true,
            "theorem trivialDecide : Eq Nat.zero Nat.zero := by trivial",
        ),
        (
            "trivialAnd",
            true,
            "theorem trivialAnd (P : Prop) (h : P) : And P True := by trivial",
        ),
        (
            "rwaRecover",
            true,
            "theorem rwaRecover (P : Nat → Prop) (n m : Nat) (h : Eq n m) (hn : P n) : P n := by first | (rwa [h]; fail) | exact hn",
        ),
        (
            "falseTrivial",
            false,
            "theorem falseTrivial : False := by trivial",
        ),
        (
            "falseRwa",
            false,
            "theorem falseRwa (P : Nat → Prop) (n m : Nat) (h : Eq n m) : P n := by rwa [h]",
        ),
    ];
    for (label, accepted, source) in cases {
        let filename = format!("{label}.lean");
        std::fs::write(
            dir.join(&filename),
            format!("prelude\nimport Init.Core\n{source}\n"),
        )
        .unwrap();
        let oracle = Command::new(&reference)
            .current_dir(&dir)
            .args(["-j1", &filename])
            .output()
            .unwrap();
        std::fs::write(dir.join(format!("{label}.stdout")), &oracle.stdout).unwrap();
        std::fs::write(dir.join(format!("{label}.stderr")), &oracle.stderr).unwrap();
        assert_eq!(
            oracle.status.success(),
            accepted,
            "{label}: {oracle:?}; {dir:?}"
        );
    }

    // Discover and admit the real closure. No caller-forged checked owners,
    // source seed or filtered macro journal supplies native execution authority.
    let target = name("Init.Core");
    let mut pending = vec![target.clone()];
    let mut seen = BTreeSet::new();
    let mut loaded = Vec::new();
    while let Some(module) = pending.pop() {
        if !seen.insert(module.clone()) {
            continue;
        }
        let base = library.join(module.to_display_string().replace('.', "/"));
        let parts = ["olean", "olean.server", "olean.private"]
            .map(|extension| std::fs::read(base.with_extension(extension)).unwrap());
        pending.extend(
            crate::olean_module_imports(&parts[0], OleanDecodeLimits::new(parts[0].len())).unwrap(),
        );
        loaded.push((module, parts));
    }
    let inputs: Vec<_> = loaded
        .iter()
        .map(|(name, parts)| OleanModuleInput {
            name,
            artifact: &parts[0],
            server_artifact: Some(&parts[1]),
            private_artifact: Some(&parts[2]),
        })
        .collect();
    let options = KVMap::new();
    let imported = Engine::from_environment(Environment::new())
        .import_olean_modules_for_source(
            &inputs,
            std::slice::from_ref(&target),
            &options,
            SourceOleanImportLimits::new(OleanCheckLimits::new(
                1 << 30,
                Budget::for_stack_bytes(64 * 1024 * 1024),
            )),
        )
        .unwrap()
        .into_complete()
        .unwrap();
    assert_eq!(imported.checked.modules.len(), loaded.len());
    assert_eq!(imported.engine.imported_modules().len(), loaded.len());
    let partition =
        VerifiedPartition::from_pinned_tsv(&std::fs::read_to_string(partition).unwrap()).unwrap();
    let registry = imported
        .prepare_imported_macros_deferred(
            MacroCompilationInputs::new(Vec::new(), partition, BTreeSet::new()),
            MacroRegistryLimits::default(),
        )
        .unwrap();
    let trivial_kind = name("Lean.Parser.Tactic.tacticTrivial");
    let expected_order: Vec<_> = (1..=6)
        .rev()
        .map(|index| {
            name(&format!(
                "Lean.Parser.Tactic._aux_Init_Tactics___macroRules_Lean_Parser_Tactic_tacticTrivial_{index}"
            ))
        })
        .collect();
    assert_eq!(
        registry
            .declarations(&trivial_kind)
            .cloned()
            .collect::<Vec<_>>(),
        expected_order,
        "the complete imported journal determines fallback order"
    );
    let engine = &imported.engine;
    let before = engine.logical_root(&options);

    // The declaration-only adapter deliberately refuses runtime tactic
    // dispatch; the owned file session installs that provider during checking.
    let node_only = admit(
        engine,
        &registry,
        cases[0].2.as_bytes(),
        MacroTreeLimits::default(),
        admission(),
        None,
    );
    assert!(matches!(
        &node_only.outcome,
        Outcome::Complete(Err(SourceMacroError::TacticExpansion { kind }))
            if *kind == name("Lean.Parser.Tactic.tacticRwa__")
    ));
    assert!(node_only.state.is_none());
    assert!(node_only.attempts.is_empty());
    assert_eq!(node_only.completed_vm_usage.steps, 0);

    let run =
        |source: &[u8], limits: MacroTreeLimits, cancellation: Option<&dyn CancellationProbe>| {
            engine.check_source_files_with_imported_macros(
                &[source],
                &options,
                SourceCheckLimits::new(admission()),
                SourceMacroInvocation {
                    registry: &registry,
                    context: &context(),
                    state: MacroState {
                        macro_scope: 17,
                        ..MacroState::default()
                    },
                    lookup: None,
                    limits,
                    cancellation,
                },
            )
        };
    fn assert_checked(engine: &Engine, report: &SourceMacroFileCheck, label: &str) {
        let Outcome::Complete(Ok(checked)) = &report.outcome else {
            panic!("{label}: {report:?}")
        };
        assert!(report.state.is_some());
        assert_eq!(
            (checked.files, checked.commands, checked.theorems),
            (1, 1, 1)
        );
        assert_eq!(
            checked.base_logical_root,
            engine.logical_root(&KVMap::new())
        );
        assert_ne!(checked.result_logical_root, checked.base_logical_root);
        let Some(ConstantInfo::Thm(theorem)) = checked.engine.environment().find(&name(label))
        else {
            panic!("{label}: the checked source did not publish its theorem")
        };
        // Recheck the returned closed proof against the original imports, so
        // the integration assertion retains the exact body-checking ground.
        let admitted = engine
            .admit_declaration(
                crate::Declaration::Thm(theorem.clone()),
                &KVMap::new(),
                admission(),
            )
            .unwrap()
            .into_complete()
            .unwrap();
        assert_eq!(
            admitted.checker.ground,
            crate::CheckerAdmissionGround::BodyCheckedAgainstDeclaredType
        );
    }

    for (label, accepted, source) in cases {
        let report = run(source.as_bytes(), MacroTreeLimits::default(), None);
        if accepted {
            assert_checked(engine, &report, label);
        } else {
            assert!(
                matches!(
                    &report.outcome,
                    Outcome::Complete(Err(SourceCheckError::Command { error, .. }))
                        if matches!(error.as_ref(), crate::EngineExecutionError::Frontend(_))
                ),
                "{label}: {report:?}; {dir:?}"
            );
            assert!(report.state.is_none());
        }
        assert!(
            !report.attempts.is_empty(),
            "{label} bypassed imported macros"
        );
        assert!(report.attempts.iter().all(|attempt| {
            attempt.reference_functions.is_empty() && !attempt.native_functions.is_empty()
        }));
        assert!(report.completed_vm_usage.steps > 0);
        let trivial_order: Option<&[usize]> = match label {
            "trivialTrue" => Some(&[6, 5]),
            "trivialAssumption" => Some(&[6, 5, 4, 3, 2, 1]),
            "trivialRefl" => Some(&[6, 5, 4, 3, 2]),
            "trivialContradiction" => Some(&[6, 5, 4, 3]),
            "trivialDecide" => Some(&[6, 5, 4]),
            "trivialAnd" => Some(&[6, 6, 5, 4, 3, 2, 1, 6, 5]),
            _ => None,
        };
        if let Some(order) = trivial_order {
            let actual: Vec<_> = report
                .attempts
                .iter()
                .filter(|attempt| expected_order.contains(&attempt.declaration))
                .map(|attempt| attempt.declaration.clone())
                .collect();
            let expected: Vec<_> = order
                .iter()
                .map(|index| expected_order[6 - index].clone())
                .collect();
            assert_eq!(
                actual, expected,
                "{label}: native candidates must succeed before builtin fallback"
            );
        }
        assert_eq!(engine.logical_root(&options), before);
        assert!(!engine.environment().contains(&name(label)));
    }

    let source = cases[8].2.as_bytes();
    let mut limited = MacroTreeLimits::default();
    limited.dispatch.max_attempts = 1;
    let stopped = run(source, limited, None);
    assert!(
        matches!(stopped.outcome, Outcome::Inconclusive(_)),
        "{stopped:?}"
    );
    assert!(stopped.state.is_none());
    assert!(stopped.completed_vm_usage.steps > 0);
    let cancelled = run(source, MacroTreeLimits::default(), Some(&|| true));
    assert!(matches!(cancelled.outcome, Outcome::Inconclusive(_)));
    assert!(cancelled.state.is_none());
    let recovered = run(source, MacroTreeLimits::default(), None);
    assert_checked(engine, &recovered, cases[8].0);
    assert_eq!(engine.logical_root(&options), before);
}

#[test]
fn live_imported_ir_changes_source_checks_with_the_pins_order_and_scoped_behavior() {
    let Some(reference) = std::env::var_os("FLN_REFERENCE_LEAN").map(PathBuf::from) else {
        assert!(
            std::env::var_os("FLN_REQUIRE_REFERENCE").is_none(),
            "pinned Reference required for imported macro source checks"
        );
        eprintln!("SKIP: imported source macro reference requires FLN_REFERENCE_LEAN");
        return;
    };
    let version = Command::new(&reference).arg("--githash").output().unwrap();
    assert!(version.status.success());
    assert_eq!(
        String::from_utf8(version.stdout).unwrap().trim(),
        format::PIN_COMMIT
    );
    let root = std::env::var_os("FLN_IR_REFERENCE_ARTIFACTS")
        .map(PathBuf::from)
        .unwrap_or_else(std::env::temp_dir);
    let unique = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap()
        .as_nanos();
    let dir = root.join(format!("source-macro-{}-{unique}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let source =
        include_str!("../../../../../../fln-olean/fixtures/ir/NativeSourceMacroModule.lean");
    std::fs::write(dir.join("NativeSourceMacroModule.lean"), source).unwrap();
    let result = Command::new(&reference)
        .current_dir(&dir)
        .args([
            "-o",
            "NativeSourceMacroModule.olean",
            "NativeSourceMacroModule.lean",
        ])
        .output()
        .unwrap();
    std::fs::write(dir.join("compile.stdout"), &result.stdout).unwrap();
    std::fs::write(dir.join("compile.stderr"), &result.stderr).unwrap();
    assert!(
        result.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
    assert_eq!(
        result.stdout,
        b"Bool : Type\n11\n11\nNat : Type\n7\n7\nBool : Type\n11\n11\n11\n"
    );
    assert!(result.stderr.is_empty());
    // Same successful prefix, one false proof appended. A query's preceding
    // output does not make a failing file a positive oracle result.
    std::fs::write(
        dir.join("FalseSourceMacroModule.lean"),
        format!("{source}\nexample : pinDeclaredValue = 18 := by rfl\n"),
    )
    .unwrap();
    let rejected = Command::new(&reference)
        .current_dir(&dir)
        .arg("FalseSourceMacroModule.lean")
        .output()
        .unwrap();
    std::fs::write(dir.join("false.stdout"), &rejected.stdout).unwrap();
    std::fs::write(dir.join("false.stderr"), &rejected.stderr).unwrap();
    assert!(
        !rejected.status.success(),
        "the pin must refuse the false theorem"
    );

    let public = std::fs::read(dir.join("NativeSourceMacroModule.olean")).unwrap();
    let server = std::fs::read(dir.join("NativeSourceMacroModule.olean.server")).unwrap();
    let private = std::fs::read(dir.join("NativeSourceMacroModule.olean.private")).unwrap();
    let decoded = crate::decode_olean_module_artifacts(
        &public,
        &server,
        &private,
        OleanDecodeLimits::new(public.len() + server.len() + private.len()),
    )
    .unwrap();
    let extensions = OleanView::parse_with_dependencies(&private, &[&public, &server])
        .unwrap()
        .extension_payloads(WalkBudget::default(), 32 * 1024 * 1024)
        .unwrap();
    let rows = macros::decode(&extensions, DecodeLimits::default()).unwrap();
    let plus_rows: Vec<_> = rows
        .iter()
        .filter(|row| row.key == name("term_+_"))
        .collect();
    assert_eq!(plus_rows.len(), 3);
    assert_eq!(plus_rows[0].declaration, name("sourceChooseRight"));
    assert_eq!(plus_rows[1].declaration, name("sourceTryNext"));
    assert_eq!(
        plus_rows[2].declaration,
        name("SourceScoped.sourceChooseLeft")
    );
    assert_eq!(plus_rows[2].scope, Some(name("SourceScoped")));
    let code = [crate::decode_ir_artifact(
        &std::fs::read(dir.join("NativeSourceMacroModule.ir")).unwrap(),
        32 * 1024 * 1024,
    )
    .unwrap()];

    // Exact decoded owners are test caller inputs, as in the parent live
    // registry test. This does not claim to admit Lean's full import closure.
    let root = Environment::new().logical_root(&KVMap::new());
    let module = CheckedOleanModule {
        name: name("NativeSourceMacroModule"),
        decoded,
        base_logical_root: root,
        result_logical_root: root,
        declarations: Vec::new(),
    };
    let registry = RegisteredMacros::prepare(
        &[MacroRegistrationModule {
            checked: &module,
            extensions: &extensions,
        }],
        &environment(&[&module]),
        &code,
        &VerifiedPartition::user_fixture(),
        &users(&code),
        MacroRegistryLimits::default(),
    )
    .unwrap_or_else(|error| panic!("{error}; {dir:?}"));
    let engine = bound_engine(&module);
    let before = engine.logical_root(&KVMap::new());
    assert!(
        engine
            .check_source_command(b"#check (Nat + Bool)", &KVMap::new(), admission())
            .is_err()
    );

    let report = run(
        &engine,
        &registry,
        b"#check (Nat + Bool)",
        MacroTreeLimits::default(),
        None,
    );
    checked_constant(&report, "Bool");
    assert_eq!(report.attempts.len(), 2);
    assert_eq!(report.attempts[0].declaration, name("sourceTryNext"));
    assert_eq!(report.attempts[1].declaration, name("sourceChooseRight"));
    assert!(report.attempts.iter().all(|attempt| {
        attempt
            .reference_functions
            .iter()
            .any(|function| function.name == attempt.declaration)
    }));
    let scoped = registry.activate_scoped(&name("SourceScoped")).unwrap();
    let scoped_report = run(
        &engine,
        &scoped,
        b"#check (Nat + Bool)",
        MacroTreeLimits::default(),
        None,
    );
    checked_constant(&scoped_report, "Nat");
    assert_eq!(scoped_report.attempts.len(), 1);
    assert_eq!(
        scoped_report.attempts[0].declaration,
        name("SourceScoped.sourceChooseLeft")
    );
    let diagnostic = run(
        &engine,
        &registry,
        b"#check Nat - Bool",
        MacroTreeLimits::default(),
        None,
    );
    assert!(matches!(
        diagnostic.outcome,
        Outcome::Complete(Err(SourceMacroError::Diagnostic { message, .. }))
            if message == "source macro diagnostic"
    ));
    assert!(diagnostic.state.is_none());
    let mut artifacts = Vec::new();
    for (active, expected) in [(&registry, 11), (&scoped, 7), (&registry, 11)] {
        let report = evaluate(
            &engine,
            active,
            b"#eval (7 + 11)",
            MacroTreeLimits::default(),
            execution_limits(),
            None,
        );
        let result = evaluated_nat(&report, expected);
        artifacts.push(result.execution.flbc_artifact.clone());
        assert!(report.attempts.iter().all(|attempt| {
            attempt
                .reference_functions
                .iter()
                .any(|function| function.name == attempt.declaration)
        }));
    }
    assert_eq!(artifacts[0], artifacts[2]);
    assert_ne!(artifacts[0], artifacts[1]);
    let named = admit(
        &engine,
        &registry,
        b"def nativeDeclaredValue : Nat := 7 + 11",
        MacroTreeLimits::default(),
        admission(),
        None,
    );
    let named = admitted(&named);
    assert_declared_value(&named.admission.engine, "nativeDeclaredValue", 11);
    let proof = admit(
        &named.admission.engine,
        &registry,
        b"theorem nativeDeclaredValue_eq : nativeDeclaredValue = 11 := by rfl",
        MacroTreeLimits::default(),
        admission(),
        None,
    );
    admitted(&proof);
    let false_proof = admit(
        &named.admission.engine,
        &registry,
        b"theorem falseDeclaredValue : nativeDeclaredValue = 18 := by rfl",
        MacroTreeLimits::default(),
        admission(),
        None,
    );
    assert!(matches!(
        false_proof.outcome,
        Outcome::Complete(Err(SourceMacroError::Frontend(_)))
    ));
    assert!(false_proof.state.is_none());
    let scoped_named = admit(
        &engine,
        &scoped,
        b"def nativeScopedDeclaredValue : Nat := 7 + 11",
        MacroTreeLimits::default(),
        admission(),
        None,
    );
    assert_declared_value(
        &admitted(&scoped_named).admission.engine,
        "nativeScopedDeclaredValue",
        7,
    );
    let helper = admit(&engine, &registry, b"def nativeDeclaredHelper (n : Nat) : Nat := let rec helper (x : Nat) : Nat := x + 11; helper n", MacroTreeLimits::default(), admission(), None);
    let helper = admitted(&helper);
    assert!(helper.admission.admissions.len() >= 2);
    assert_declared_value(&helper.admission.engine, "nativeDeclaredHelper 7", 11);

    // The provider is unchanged pinned user MacroM code, loaded from its
    // emitted journal and IR above. These source registrations target the SAME
    // kind and must interleave with its scoped activation, not replace the
    // imported fallback table or receive unconditional precedence over it.
    let client = "macro_rules | `(7 + 11) => `(23)\n\
        def mixedSourceFirst : Nat := 7 + 11\n\
        def mixedImportedFallback : Nat := 0 + 13\n\
        section\n\
        open scoped SourceScoped\n\
        def mixedImportedLater : Nat := 7 + 11\n\
        macro_rules | `(7 + 11) => `(41)\n\
        def mixedSourceLater : Nat := 7 + 11\n\
        open scoped SourceScoped\n\
        def mixedRepeated : Nat := 7 + 11\n\
        section\n\
        local macro_rules | `(7 + 11) => `(43)\n\
        def mixedLocal : Nat := 7 + 11\n\
        end\n\
        def mixedLocalRestored : Nat := 7 + 11\n\
        end\n\
        def mixedGlobalSurvives : Nat := 7 + 11\n\
        open scoped SourceScoped in def mixedTemporary : Nat := 7 + 11\n\
        def mixedTemporaryRestored : Nat := 7 + 11\n\
        namespace SourceScoped\n\
        scoped macro_rules | `(7 + 11) => `(53)\n\
        def mixedScopedSource : Nat := 7 + 11\n\
        end SourceScoped\n\
        def mixedScopedInactive : Nat := 7 + 11\n\
        open scoped SourceScoped\n\
        def mixedSourceWithinActivation : Nat := 7 + 11\n";
    let expected = [
        ("mixedSourceFirst", 23),
        ("mixedImportedFallback", 13),
        ("mixedImportedLater", 7),
        ("mixedSourceLater", 41),
        ("mixedRepeated", 41),
        ("mixedLocal", 43),
        ("mixedLocalRestored", 41),
        ("mixedGlobalSurvives", 41),
        ("mixedTemporary", 7),
        ("mixedTemporaryRestored", 41),
        ("SourceScoped.mixedScopedSource", 53),
        ("mixedScopedInactive", 41),
        ("mixedSourceWithinActivation", 53),
    ];
    let mut oracle = format!("import NativeSourceMacroModule\n{client}");
    for (declaration, _) in expected {
        oracle.push_str(&format!("#eval {declaration}\n"));
    }
    std::fs::write(dir.join("SameKindSourceClient.lean"), oracle).unwrap();
    let result = Command::new(&reference)
        .current_dir(&dir)
        .env("LEAN_PATH", &dir)
        .arg("SameKindSourceClient.lean")
        .output()
        .unwrap();
    std::fs::write(dir.join("same-kind.stdout"), &result.stdout).unwrap();
    std::fs::write(dir.join("same-kind.stderr"), &result.stderr).unwrap();
    assert!(
        result.status.success(),
        "{dir:?}: {}{}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
    let expected_output: String = expected
        .iter()
        .map(|(_, value)| format!("{value}\n"))
        .collect();
    assert_eq!(result.stdout, expected_output.as_bytes(), "{dir:?}");
    assert!(result.stderr.is_empty());
    let report = engine.check_source_files_with_imported_macros(
        &[client.as_bytes()],
        &KVMap::new(),
        crate::source_check::SourceCheckLimits::new(admission()),
        SourceMacroInvocation {
            registry: &registry,
            context: &context(),
            state: MacroState::default(),
            lookup: None,
            limits: MacroTreeLimits::default(),
            cancellation: None,
        },
    );
    let Outcome::Complete(Ok(checked)) = &report.outcome else {
        panic!("{dir:?}: {report:?}")
    };
    assert!(report.state.is_some());
    for (declaration, value) in expected {
        assert_declared_value(&checked.engine, declaration, value);
    }
    assert_eq!(engine.logical_root(&KVMap::new()), before);

    // Source atomic templates use actual native term/pattern positions, while
    // generated compound terms reenter the unchanged pinned artifact macros.
    let atomic_client = r#"
structure AtomicPair where
  fst : Nat
  snd : Nat
section
local macro_rules | `(1) => `(5 + 2)
local macro_rules | `(2) => `(11)
local macro_rules | `("source") => `(23)
def mixedAtomicGenerated : Nat := 1
def mixedAtomicUniverse : Sort 1 := Nat
def mixedAtomicProjection : Nat := (AtomicPair.mk (Nat.succ Nat.zero) Nat.zero).1
def mixedAtomicString : Nat := "source"
def mixedAtomicChoose : Nat -> Nat
  | 2 => 42
  | _ => 0
end
def mixedAtomicPattern : Nat := mixedAtomicChoose 11
theorem mixedAtomicPattern_eq : Eq mixedAtomicPattern 42 := Eq.refl mixedAtomicPattern
"#;
    let expected = [
        ("mixedAtomicGenerated", 11),
        ("mixedAtomicProjection", 1),
        ("mixedAtomicString", 23),
        ("mixedAtomicPattern", 42),
    ];
    let mut oracle = format!("import NativeSourceMacroModule\n{atomic_client}");
    for (declaration, _) in expected {
        oracle.push_str(&format!("#eval {declaration}\n"));
    }
    std::fs::write(dir.join("AtomicSourceClient.lean"), oracle).unwrap();
    let result = Command::new(&reference)
        .current_dir(&dir)
        .env("LEAN_PATH", &dir)
        .arg("AtomicSourceClient.lean")
        .output()
        .unwrap();
    std::fs::write(dir.join("atomic-source.stdout"), &result.stdout).unwrap();
    std::fs::write(dir.join("atomic-source.stderr"), &result.stderr).unwrap();
    assert!(result.status.success(), "{dir:?}: {result:?}");
    assert_eq!(result.stdout, b"11\n1\n23\n42\n");
    assert!(result.stderr.is_empty());
    let report = engine.check_source_files_with_imported_macros(
        &[atomic_client.as_bytes()],
        &KVMap::new(),
        crate::source_check::SourceCheckLimits::new(admission()),
        SourceMacroInvocation {
            registry: &registry,
            context: &context(),
            state: MacroState::default(),
            lookup: None,
            limits: MacroTreeLimits::default(),
            cancellation: None,
        },
    );
    let Outcome::Complete(Ok(checked)) = &report.outcome else {
        panic!("{dir:?}: {report:?}")
    };
    assert!(report.state.is_some());
    for (declaration, value) in expected {
        assert_declared_value(&checked.engine, declaration, value);
    }
    assert!(report.attempts.iter().any(|attempt| {
        attempt.declaration == name("sourceChooseRight")
            && attempt.reference_functions.iter().any(|function| {
                function.name == name("sourceChooseRight") && function.producer() == "reference"
            })
    }));
    assert_eq!(engine.logical_root(&KVMap::new()), before);
}
