//! Native source reflexivity tags. These are selection metadata, not proofs.
//!
//! The pin infers its default dsimp tag for naked `:= rfl`, but not `:= (rfl)`
//! or `:= by rfl`. Preserve that distinction after syntax has been discarded.
//! Before recording a tag, verify the admitted declaration's generic
//! definitional equality. User-written `:= rfl` is the pin's
//! explicit defeq-attribute path (MutualDef.elabMutualDef), not its stricter
//! generated-theorem inference path. Module replay keeps this bounded journal.
use super::super::super::*;
use fln_env::constants::{ConstantInfo, DefinitionSafety};
use fln_env::extensions::{
    CheckpointSemantics, ExtensionDescriptor, MergeSemantics, PayloadProvenance,
};
use std::collections::BTreeSet;

const MAGIC: &[u8] = b"FLNDSIMP\x01";
// Generated semireducible equation theorems can be backward-definitional
// without being strict rfl theorems. Preserve old strict-tag bytes unchanged.
const BACKWARD_MAGIC: &[u8] = b"FLNDSIMP\x02";
// The pinned `Init` alone tags 1,559 theorems; `Std` and `Lean` add more.
/// Maximum number of validated native reflexivity tags.
pub const MAX_ROWS: usize = 1 << 16;
const MAX_ENTRY_BYTES: usize = 16 * 1024;

/// Native reflexivity journal name, for artifact export and typed refusals.
pub fn journal_name() -> Name {
    Name::from_components(["FrankenLean", "sourceDefEq", "v1"])
}

fn descriptor() -> ExtensionDescriptor {
    ExtensionDescriptor {
        name: journal_name(),
        merge: MergeSemantics::AppendOrdered,
        checkpoint: CheckpointSemantics::FullJournal,
        provenance: PayloadProvenance::Understood,
    }
}

/// Exact journal whose validated tags the pinned-format writer can serialize.
pub fn supports(candidate: &ExtensionDescriptor) -> bool {
    *candidate == descriptor()
}
fn malformed() -> NatDefinitionElabError {
    failure(SourceInferenceError::SimpSet(
        super::SimpSetError::Malformed,
    ))
}
fn limit() -> NatDefinitionElabError {
    failure(SourceInferenceError::SimpSet(super::SimpSetError::Limit))
}
fn codec(error: crate::instances::InstanceRegistryError) -> NatDefinitionElabError {
    match error {
        crate::instances::InstanceRegistryError::Limit => limit(),
        _ => malformed(),
    }
}

/// Only the original naked syntax requests the explicit tag. The pin applies
/// it to definitions and instances too; examples, parentheses, tactic
/// blocks and macros are not guessed equivalent.
pub fn direct_rfl(syntax: &Syntax) -> bool {
    let Syntax::Node { kind, args, .. } = syntax else {
        return false;
    };
    if kind != &parser_kind(&["Command", "declaration"]) {
        return false;
    }
    let [_, declaration @ Syntax::Node { kind, args, .. }] = args.as_slice() else {
        return false;
    };
    let value = if kind == &parser_kind(&["Command", "definition"]) && args.len() == 5
        || args.len() == 4
            && ["theorem", "abbrev"]
                .iter()
                .any(|name| kind == &parser_kind(&["Command", name]))
    {
        &args[3]
    } else if kind == &parser_kind(&["Command", "instance"]) {
        let Ok(parts) = instance_command::parts(declaration) else {
            return false;
        };
        parts.value
    } else {
        return false;
    };
    let Syntax::Node { kind, args, .. } = value else {
        return false;
    };
    if kind != &parser_kind(&["Command", "declValSimple"]) {
        return false;
    }
    let [
        Syntax::Atom {
            val: assignment, ..
        },
        Syntax::Ident { val, .. },
        suffix,
        clause,
    ] = args.as_slice()
    else {
        return false;
    };
    assignment == ":="
        && val == &Name::from_components(["rfl"])
        && expect_empty_null(clause, "no where clause").is_ok()
        && matches!(suffix, Syntax::Node { kind, args, .. }
            if kind == &parser_kind(&["Termination", "suffix"])
            && args.len() == 2
            && args.iter().all(|arg| expect_empty_null(arg, "no termination hint").is_ok()))
}

fn taggable(info: &ConstantInfo) -> bool {
    matches!(info, ConstantInfo::Thm(_))
        || matches!(info, ConstantInfo::Defn(value) if value.safety == DefinitionSafety::Safe)
}

/// Read validated tags; charge bounded name-decoding work before retaining it.
/// Corrupt, oversized or dangling metadata is an error, never an empty rule set.
pub fn read(
    environment: &Environment,
    tick: impl FnMut() -> Result<(), NatDefinitionElabError>,
) -> Result<BTreeSet<Name>, NatDefinitionElabError> {
    read_tags(environment, tick).map(|(strict, _)| strict)
}

/// Read all backward-definitional tags. Strict `defeq` implies backward-defeq,
/// while a backward-only tag must never make the theorem available to `dsimp`.
pub fn read_backward(
    environment: &Environment,
    tick: impl FnMut() -> Result<(), NatDefinitionElabError>,
) -> Result<BTreeSet<Name>, NatDefinitionElabError> {
    let (strict, mut backward) = read_tags(environment, tick)?;
    backward.extend(strict);
    Ok(backward)
}

fn read_tags(
    environment: &Environment,
    mut tick: impl FnMut() -> Result<(), NatDefinitionElabError>,
) -> Result<(BTreeSet<Name>, BTreeSet<Name>), NatDefinitionElabError> {
    let mut strict = BTreeSet::new();
    let mut backward = BTreeSet::new();
    let descriptor = descriptor();
    let Some(state) = environment.extension(&descriptor.name) else {
        return Ok((strict, backward));
    };
    if state.descriptor != descriptor {
        return Err(malformed());
    }
    if state.len() > MAX_ROWS {
        return Err(limit());
    }
    for entry in state.entries() {
        tick()?;
        if entry.payload.len() > MAX_ENTRY_BYTES {
            return Err(limit());
        }
        for _ in entry.payload.chunks(64) {
            tick()?;
        }
        let (mut bytes, names) = if let Some(bytes) = entry.payload.strip_prefix(MAGIC) {
            (bytes, &mut strict)
        } else if let Some(bytes) = entry.payload.strip_prefix(BACKWARD_MAGIC) {
            (bytes, &mut backward)
        } else {
            return Err(malformed());
        };
        let name = crate::instances::read_name(&mut bytes).map_err(codec)?;
        if !bytes.is_empty()
            || !environment.find(&name).is_some_and(taggable)
            || !names.insert(name)
        {
            return Err(malformed());
        }
    }
    Ok((strict, backward))
}

/// Record an imported module's `Lean.defeqAttr` tag (the pin's `@[defeq]`, which its
/// `dsimp` reads through `isRflTheorem`). Like the imported simp attribute it is the
/// pin's own metadata, and like every tag it selects candidates only: `dsimp` still
/// checks each replacement by conversion. A name the import exposes only as an
/// interface, without its safe proof declaration, keeps no tag. Without these,
/// under the real `Init` no imported rfl lemma (`id_eq`, `Nat.add_zero`, …) was
/// ever reflexive to `dsimp`.
pub fn register_imported(
    environment: &Environment,
    name: &Name,
) -> Result<Environment, NatDefinitionElabError> {
    register_tag(environment, name, MAGIC)
}

/// Record a backward-only tag after admission. Callers deduplicate registrations
/// just as for [`register_imported`]; recording both kinds for one name is valid.
/// This changes rewrite metadata only and confers no proof authority.
pub fn register_backward(
    environment: &Environment,
    name: &Name,
) -> Result<Environment, NatDefinitionElabError> {
    register_tag(environment, name, BACKWARD_MAGIC)
}

fn register_tag(
    environment: &Environment,
    name: &Name,
    magic: &[u8],
) -> Result<Environment, NatDefinitionElabError> {
    if !environment.find(name).is_some_and(taggable) {
        return Ok(environment.clone());
    }
    let mut payload = magic.to_vec();
    crate::instances::write_name(name, &mut payload).map_err(codec)?;
    if payload.len() > MAX_ENTRY_BYTES {
        return Err(limit());
    }
    let descriptor = descriptor();
    let environment = match environment.extension(&descriptor.name) {
        None => environment
            .register_extension(descriptor.clone())
            .map_err(|_| malformed())?,
        Some(state) if state.descriptor != descriptor => return Err(malformed()),
        Some(state) if state.len() >= MAX_ROWS => return Err(limit()),
        Some(_) => environment.clone(),
    };
    environment
        .push_extension_entry(&descriptor.name, payload)
        .map_err(|_| malformed())
}

/// Called only for naked `:= rfl` on the successor of checked source admission.
/// The pin's explicit attribute validates the normalized equality type, not the
/// proof body's syntax. No declaration is created and every use still checks
/// conversion independently of this selection metadata.
pub fn infer(
    environment: &Environment,
    name: &Name,
    kernel: Budget,
) -> Result<Environment, NatDefinitionElabError> {
    let Some(info) = environment.find(name).filter(|info| taggable(info)) else {
        // Public module theorem interfaces may deliberately conceal the body.
        // Lack of a body is not evidence that its proof is reflexive.
        return Ok(environment.clone());
    };
    let mut context = Context::new(environment, kernel);
    let tagged = read(environment, || context.tick())?;
    if tagged.contains(name) {
        return Ok(environment.clone());
    }
    let base = info.constant_val();
    if !context.dsimp_generic_defeq(&base.type_, &base.level_params)? {
        return Err(failure(SourceInferenceError::SimpSet(
            super::SimpSetError::UnsupportedDeclaration(name.clone()),
        )));
    }
    register_imported(environment, name)
}

/// The pin's `inferDefEqAttr` (vendored `Lean/DefEqAttrib.lean:159-190`) for a theorem this
/// engine generates, such as an equation theorem. A structural reflexivity proof
/// receives the backward tag; only an equality at instance transparency also
/// receives the strict tag. Other checked proofs remain untagged: unlike
/// [`infer`], nothing here was written as `:= rfl`. Existing realization flags
/// are retained even when later attributes change a definition's reducibility.
pub fn infer_generated(
    environment: &Environment,
    name: &Name,
    kernel: Budget,
) -> Result<Environment, NatDefinitionElabError> {
    let Some(ConstantInfo::Thm(theorem)) = environment.find(name) else {
        return Ok(environment.clone());
    };
    let mut context = Context::new(environment, kernel);
    let backward = read_backward(environment, || context.tick())?;
    if backward.contains(name) {
        return Ok(environment.clone());
    }
    let proof = Typed {
        value: theorem.value.clone(),
        type_: theorem.base.type_.clone(),
    };
    if !context.dsimp_rfl_proof(proof, &backward)? {
        return Ok(environment.clone());
    }
    if context.dsimp_generic_defeq_at(
        &theorem.base.type_,
        &theorem.base.level_params,
        UnificationTransparency::Instances,
    )? {
        register_imported(environment, name)
    } else {
        register_backward(environment, name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_env::constants::{ConstantVal, DefinitionVal, ReducibilityHints, TheoremVal};
    use fln_env::environment::{DeclarationBudget, DeclarationCommitted};
    use fln_env::pmap::CollisionBudget;
    use fln_kernel::capability::{Published, admit};
    use fln_kernel::council::{Council, CouncilOutcome, convene};

    fn name(text: &str) -> Name {
        Name::from_components(text.split('.'))
    }

    fn budget() -> Budget {
        Budget::for_stack_bytes(2 * 1024 * 1024)
    }

    fn publish(environment: &Environment, declaration: Declaration) -> Environment {
        let Outcome::Complete(admitted) = admit(environment, declaration, budget()) else {
            panic!("fixture admission must complete")
        };
        let CouncilOutcome::Agreed(checked) = convene(&Council::nobody_was_asked(), admitted)
        else {
            panic!("fixture must pass the kernel")
        };
        match checked.publish(
            DeclarationBudget::default(),
            CollisionBudget::default(),
            None,
        ) {
            Outcome::Complete(Published::Committed(DeclarationCommitted::Published(result))) => {
                result.environment
            }
            Outcome::Complete(Published::BlockCommitted(result)) => result.environment,
            other => panic!("fixture publication: {other:?}"),
        }
    }

    fn reflexivity_declaration(label: &str, beta: bool, definition: bool) -> Declaration {
        let universe = Level::param(name("u"));
        let type_variable = Expr::bvar(1).unwrap();
        let value_variable = Expr::bvar(0).unwrap();
        let reflexivity = Expr::app(
            Expr::app(
                Expr::const_(name("Eq.refl"), vec![universe.clone()]),
                type_variable.clone(),
            ),
            value_variable.clone(),
        );
        let mut equality = Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(name("Eq"), vec![universe.clone()]),
                    type_variable,
                ),
                value_variable.clone(),
            ),
            value_variable,
        );
        if beta {
            equality = Expr::app(
                Expr::lam(
                    name("P"),
                    Expr::sort(Level::zero()),
                    Expr::bvar(0).unwrap(),
                    BinderInfo::Default,
                ),
                equality,
            );
        }
        let type_ = Expr::forall_e(
            name("A"),
            Expr::sort(universe.clone()),
            Expr::forall_e(
                name("x"),
                Expr::bvar(0).unwrap(),
                equality,
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let value = Expr::lam(
            name("A"),
            Expr::sort(universe),
            Expr::lam(
                name("x"),
                Expr::bvar(0).unwrap(),
                reflexivity,
                BinderInfo::Default,
            ),
            BinderInfo::Default,
        );
        let base = ConstantVal {
            name: name(label),
            level_params: vec![name("u")],
            type_,
        };
        if definition {
            Declaration::Defn(DefinitionVal {
                base,
                value,
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![name(label)],
            })
        } else {
            Declaration::Thm(TheoremVal {
                base,
                value,
                all: vec![name(label)],
            })
        }
    }

    #[test]
    fn source_tag_inference_requires_naked_rfl_not_equivalent_syntax() {
        for kind in ["theorem", "def", "abbrev", "instance"] {
            for (body, expected) in [("rfl", true), ("(rfl)", false), ("by rfl", false)] {
                let source = format!("{kind} t (A : Type) (x : A) : x = x := {body}");
                let parsed = fln_parse::parse_definition(source.as_bytes()).unwrap();
                assert_eq!(direct_rfl(parsed.syntax()), expected, "{source}");
            }
        }
        let parsed =
            fln_parse::parse_definition(b"example (A : Type) (x : A) : x = x := rfl").unwrap();
        assert!(!direct_rfl(parsed.syntax()));
    }

    #[test]
    fn explicit_tags_validate_reduced_types_for_theorems_and_safe_definitions() {
        let initial = publish(&Environment::new(), crate::seed::eq_seed_declaration());
        for (label, beta, definition) in [
            ("ordinaryDefinition", false, true),
            ("betaDefinition", true, true),
            ("betaTheorem", true, false),
        ] {
            let checked = publish(&initial, reflexivity_declaration(label, beta, definition));
            let inferred = infer(&checked, &name(label), budget()).unwrap();
            assert_eq!(
                read(&inferred, || Ok(())).unwrap(),
                BTreeSet::from([name(label)])
            );
            assert!(read(&checked, || Ok(())).unwrap().is_empty());
            let imported = register_imported(&checked, &name(label)).unwrap();
            assert_eq!(
                read(&imported, || Ok(())).unwrap(),
                BTreeSet::from([name(label)])
            );
        }
    }

    #[test]
    fn backward_only_tags_preserve_strict_dsimp_and_legacy_journal_bytes() {
        let initial = publish(&Environment::new(), crate::seed::eq_seed_declaration());
        let checked = publish(&initial, reflexivity_declaration("rule", false, false));
        let backward = register_backward(&checked, &name("rule")).unwrap();
        assert!(read(&backward, || Ok(())).unwrap().is_empty());
        assert_eq!(
            read_backward(&backward, || Ok(())).unwrap(),
            BTreeSet::from([name("rule")])
        );
        let strict = register_imported(&checked, &name("rule")).unwrap();
        assert_eq!(
            read(&strict, || Ok(())).unwrap(),
            read_backward(&strict, || Ok(())).unwrap()
        );
        assert!(
            strict
                .extension(&journal_name())
                .unwrap()
                .entries()
                .next()
                .unwrap()
                .payload
                .starts_with(MAGIC)
        );
        let both = register_imported(&backward, &name("rule")).unwrap();
        assert_eq!(
            read(&both, || Ok(())).unwrap(),
            BTreeSet::from([name("rule")])
        );
        assert_eq!(
            read_backward(&both, || Ok(())).unwrap(),
            BTreeSet::from([name("rule")])
        );
        // Repeated rows of one kind are still malformed. Two different tag
        // kinds for one admitted theorem do not authorize duplicated imports.
        let duplicate = register_backward(&backward, &name("rule")).unwrap();
        assert!(read(&duplicate, || Ok(())).is_err());
        assert!(read_backward(&duplicate, || Ok(())).is_err());
        assert!(read_backward(&checked, || Ok(())).unwrap().is_empty());
    }

    #[test]
    fn generated_tags_respect_instance_transparency_and_structural_proof_shape() {
        let initial = publish(&Environment::new(), crate::seed::eq_seed_declaration());
        let checked = publish(
            &initial,
            Declaration::Defn(DefinitionVal {
                base: ConstantVal {
                    name: name("f"),
                    level_params: vec![],
                    type_: Expr::sort(Level::one()),
                },
                value: Expr::sort(Level::zero()),
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![name("f")],
            }),
        );
        let universe = Level::succ(Level::one()).expect("universe two is within the depth bound");
        let lhs = Expr::const_(name("f"), vec![]);
        let carrier = Expr::sort(Level::one());
        let type_ = [carrier.clone(), lhs.clone(), Expr::sort(Level::zero())]
            .into_iter()
            .fold(Expr::const_(name("Eq"), vec![universe.clone()]), Expr::app);
        let proof = [carrier, lhs]
            .into_iter()
            .fold(Expr::const_(name("Eq.refl"), vec![universe]), Expr::app);
        let equation = |label: &str, value: Expr| {
            Declaration::Thm(TheoremVal {
                base: ConstantVal {
                    name: name(label),
                    level_params: vec![],
                    type_: type_.clone(),
                },
                value,
                all: vec![name(label)],
            })
        };
        let checked = publish(&checked, equation("f.eq_1", proof.clone()));
        let generated = infer_generated(&checked, &name("f.eq_1"), budget()).unwrap();
        assert!(read(&generated, || Ok(())).unwrap().is_empty());
        assert_eq!(
            read_backward(&generated, || Ok(())).unwrap(),
            BTreeSet::from([name("f.eq_1")])
        );
        assert!(read_backward(&checked, || Ok(())).unwrap().is_empty());

        // The generated proof classifier recognizes applications of backward
        // lemmas too, without promoting their semireducible statements.
        let via = publish(
            &generated,
            equation("via", Expr::const_(name("f.eq_1"), vec![])),
        );
        let via = infer_generated(&via, &name("via"), budget()).unwrap();
        assert!(read(&via, || Ok(())).unwrap().is_empty());
        assert!(
            read_backward(&via, || Ok(()))
                .unwrap()
                .contains(&name("via"))
        );

        let reducible = crate::reducibility::register(
            &generated,
            &name("f"),
            crate::reducibility::Reducibility::Reducible,
        )
        .unwrap();
        let repeated = infer_generated(&reducible, &name("f.eq_1"), budget()).unwrap();
        assert_eq!(repeated, reducible);
        let second = publish(&repeated, equation("f.eq_2", proof.clone()));
        let second = infer_generated(&second, &name("f.eq_2"), budget()).unwrap();
        assert_eq!(
            read(&second, || Ok(())).unwrap(),
            BTreeSet::from([name("f.eq_2")])
        );

        // A checked proof convertible to rfl is not necessarily a structural
        // rfl proof. Keep the peer's generated-pattern proof gate intact.
        let wrapped = Expr::app(
            Expr::lam(
                name("h"),
                type_.clone(),
                Expr::bvar(0).unwrap(),
                BinderInfo::Default,
            ),
            proof,
        );
        let checkpoint = publish(&second, equation("checkpoint", wrapped));
        let selected = infer_generated(&checkpoint, &name("checkpoint"), budget()).unwrap();
        assert_eq!(selected, checkpoint);
        assert!(
            !read_backward(&selected, || Ok(()))
                .unwrap()
                .contains(&name("checkpoint"))
        );
    }

    #[test]
    fn explicit_validation_failure_or_exhaustion_never_becomes_an_untagged_success() {
        let initial = publish(&Environment::new(), crate::seed::eq_seed_declaration());
        let data = publish(
            &initial,
            Declaration::Defn(DefinitionVal {
                base: ConstantVal {
                    name: name("data"),
                    level_params: vec![],
                    type_: Expr::sort(Level::one()),
                },
                value: Expr::sort(Level::zero()),
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![name("data")],
            }),
        );
        // `unfolds : data = Prop := Eq.refl Prop`. Its sides meet only once
        // `data` is unfolded, so the comparison must take unifier steps.
        let two = Level::one().succ().unwrap();
        let unfolds = publish(
            &data,
            Declaration::Thm(TheoremVal {
                base: ConstantVal {
                    name: name("unfolds"),
                    level_params: vec![],
                    type_: Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::const_(name("Eq"), vec![two.clone()]),
                                Expr::sort(Level::one()),
                            ),
                            Expr::const_(name("data"), vec![]),
                        ),
                        Expr::sort(Level::zero()),
                    ),
                },
                value: Expr::app(
                    Expr::app(
                        Expr::const_(name("Eq.refl"), vec![two]),
                        Expr::sort(Level::one()),
                    ),
                    Expr::sort(Level::zero()),
                ),
                all: vec![name("unfolds")],
            }),
        );
        // The comparison is metavariable-free, so it makes no kernel check and
        // `infer`'s kernel budget never runs out on it. What it spends are the
        // transaction's heartbeats, which also cap the unifier's steps. Starved
        // of them it is a resource error: never untagged success, never a
        // verdict that the rule is unsupported.
        let type_ = unfolds
            .find(&name("unfolds"))
            .unwrap()
            .constant_val()
            .type_
            .clone();
        let mut starved = Context::new(&unfolds, budget());
        starved.txn.budget.max_heartbeats = 1;
        let exhausted = starved.dsimp_generic_defeq(&type_, &[]);
        assert!(
            matches!(
                exhausted,
                Err(NatDefinitionElabError::Inference(
                    SourceInferenceError::ResourceLimit
                )) | Err(NatDefinitionElabError::Inference(
                    SourceInferenceError::Unification(_)
                ))
            ),
            "{exhausted:?}"
        );
        assert_eq!(
            Context::new(&unfolds, budget()).dsimp_generic_defeq(&type_, &[]),
            Ok(true)
        );
        // The control: the same rule with the full budget is tagged.
        let tagged = infer(&unfolds, &name("unfolds"), budget()).unwrap();
        assert!(read(&tagged, || Ok(())).unwrap().contains(&name("unfolds")));

        assert!(matches!(
            infer(&data, &name("data"), budget()),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::SimpSet(super::super::SimpSetError::UnsupportedDeclaration(
                    _
                ))
            ))
        ));
        assert!(read(&data, || Ok(())).unwrap().is_empty());
    }

    #[test]
    fn unsafe_definition_metadata_cannot_acquire_a_reflexivity_tag() {
        // A journal-shape fixture only: unsafe evidence never reaches admission
        // or the conversion validator through this metadata path.
        let Declaration::Defn(mut definition) = reflexivity_declaration("unsafeRule", false, true)
        else {
            unreachable!()
        };
        definition.safety = DefinitionSafety::Unsafe;
        let environment = Environment::new()
            .add_decl(ConstantInfo::Defn(definition))
            .unwrap();
        let selected = register_imported(&environment, &name("unsafeRule")).unwrap();
        assert!(read(&selected, || Ok(())).unwrap().is_empty());
        let descriptor = descriptor();
        let mut payload = MAGIC.to_vec();
        crate::instances::write_name(&name("unsafeRule"), &mut payload).unwrap();
        let malformed = environment
            .register_extension(descriptor.clone())
            .unwrap()
            .push_extension_entry(&descriptor.name, payload)
            .unwrap();
        assert!(read(&malformed, || Ok(())).is_err());
    }

    #[test]
    fn malformed_and_dangling_metadata_never_become_an_empty_set() {
        let descriptor = descriptor();
        let environment = Environment::new()
            .register_extension(descriptor.clone())
            .unwrap();
        let invalid = environment
            .push_extension_entry(&descriptor.name, b"bad".to_vec())
            .unwrap();
        assert!(read(&invalid, || Ok(())).is_err());
        let mut payload = MAGIC.to_vec();
        crate::instances::write_name(&Name::from_components(["missing"]), &mut payload).unwrap();
        let dangling = environment
            .push_extension_entry(&descriptor.name, payload)
            .unwrap();
        assert!(read(&dangling, || Ok(())).is_err());
        assert!(read(&environment, || Ok(())).unwrap().is_empty());
    }

    #[test]
    fn oversized_rows_and_interrupted_reads_are_refusals() {
        let descriptor = descriptor();
        let environment = Environment::new()
            .register_extension(descriptor.clone())
            .unwrap();
        let oversized = environment
            .push_extension_entry(&descriptor.name, vec![0; MAX_ENTRY_BYTES + 1])
            .unwrap();
        assert!(matches!(
            read(&oversized, || Ok(())),
            Err(NatDefinitionElabError::Inference(
                SourceInferenceError::SimpSet(super::super::SimpSetError::Limit)
            ))
        ));
        let invalid = environment
            .push_extension_entry(&descriptor.name, MAGIC.to_vec())
            .unwrap();
        let problem = read(&invalid, || {
            Err(failure(SourceInferenceError::ResourceLimit))
        })
        .unwrap_err();
        assert!(matches!(
            problem,
            NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit)
        ));
    }
}
