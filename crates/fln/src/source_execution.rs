//! Admission-only source commands share the execution stream, but never acquire
//! fabricated VM results. Module visibility includes every generated constant,
//! constructor telescope, projection, recursor rule and retained theorem proof.
use super::*;
use fln_env::constants::ConstantVal;

enum Part<'a> {
    Declared(&'a Name),
    Expression(&'a Expr),
    Reference(&'a Name),
}

fn constant<'a>(
    base: &'a ConstantVal,
    visit: &mut impl FnMut(Part<'a>) -> Result<(), EngineExecutionError>,
) -> Result<(), EngineExecutionError> {
    visit(Part::Declared(&base.name))?;
    visit(Part::Expression(&base.type_))
}

/// Source currently emits definitions, theorems and inductive blocks. Cover the
/// complete declaration enum so adding another admission consumer cannot omit
/// its dependency edges or silently grant sibling-module access.
fn parts<'a>(
    declaration: &'a Declaration,
    visit: &mut impl FnMut(Part<'a>) -> Result<(), EngineExecutionError>,
) -> Result<(), EngineExecutionError> {
    match declaration {
        Declaration::Axiom(value) => constant(&value.base, visit)?,
        Declaration::Defn(value) => {
            constant(&value.base, visit)?;
            visit(Part::Expression(&value.value))?;
            for name in &value.all {
                visit(Part::Reference(name))?;
            }
        }
        Declaration::Thm(value) => {
            constant(&value.base, visit)?;
            visit(Part::Expression(&value.value))?;
            for name in &value.all {
                visit(Part::Reference(name))?;
            }
        }
        Declaration::Opaque(value) => {
            constant(&value.base, visit)?;
            visit(Part::Expression(&value.value))?;
            for name in &value.all {
                visit(Part::Reference(name))?;
            }
        }
        Declaration::Mutual(values) => {
            for value in values {
                constant(&value.base, visit)?;
                visit(Part::Expression(&value.value))?;
                for name in &value.all {
                    visit(Part::Reference(name))?;
                }
            }
        }
        Declaration::Quotient(values) => {
            for value in values {
                constant(&value.base, visit)?;
            }
        }
        Declaration::Inductive(block) => {
            for family in &block.types {
                constant(&family.base, visit)?;
                for name in family.all.iter().chain(&family.ctors) {
                    visit(Part::Reference(name))?;
                }
            }
            for constructor in &block.ctors {
                constant(&constructor.base, visit)?;
                visit(Part::Reference(&constructor.induct))?;
            }
            for recursor in &block.recursors {
                constant(&recursor.base, visit)?;
                for name in &recursor.all {
                    visit(Part::Reference(name))?;
                }
                for rule in &recursor.rules {
                    visit(Part::Reference(&rule.ctor))?;
                    visit(Part::Expression(&rule.rhs))?;
                }
            }
        }
    }
    Ok(())
}

/// Whether `declaration` mentions `sorryAx` anywhere, the pin's `Declaration.hasSorry`
/// (`Lean/Util/Sorry.lean`), which decides its "declaration uses `sorry`" warning
/// (`warnIfUsesSorry`, `Lean/AddDecl.lean`).
///
/// Unbudgeted, as the pin's is: the walk visits each distinct node of a declaration the
/// kernel already admitted once. It must not spend the command's ingress budget, or a
/// small one would stop here rather than at the preparation it bounds.
pub(super) fn uses_sorry(declaration: &Declaration) -> Result<bool, EngineExecutionError> {
    let limit = usize::MAX;
    let sorry = Name::from_components(["sorryAx"]);
    let mut found = false;
    let mut spent = 0;
    parts(declaration, &mut |part| {
        if let Part::Expression(expr) = part
            && !found
        {
            let mut references = BTreeSet::new();
            collect_constant_references(expr, &mut references, &mut spent, limit).map_err(
                |error| match error {
                    ConstantReferenceCollectionError::PresentationLimit { observed, limit } => {
                        EngineExecutionError::SourceDependencyPresentationLimit { observed, limit }
                    }
                    ConstantReferenceCollectionError::AllocationFailure { requested } => {
                        EngineExecutionError::AllocationFailure {
                            resource: "sorry detection worklist",
                            requested,
                        }
                    }
                },
            )?;
            found = references.contains(&sorry);
        }
        Ok(())
    })?;
    Ok(found)
}

/// Whether evaluating `declarations` depends on `sorryAx`: the pin's `collectAxioms` test before
/// `#eval` runs anything (`addAndCompileExprForEval`, vendored
/// `Lean/Elab/BuiltinEvalCommand.lean:104-113`). That walk follows every constant reached, through
/// an axiom's, a constructor's and a recursor's type, a definition's, theorem's and opaque's type
/// and value, and an inductive's type and constructors (`Lean/Util/CollectAxioms.lean:52-61`).
///
/// An imported constant is a leaf while every imported module belongs to the pinned library
/// (`Init`, `Std`, `Lean`, `Lake`). None of that library's 212,919 constants mentions `sorryAx`: the
/// pinned v4.32.0 under `import Lean` and `import Lake`, opaque values included, measured
/// 2026-10-22. Any other import is walked like this file's own constants. Unbudgeted, as
/// [`uses_sorry`] is.
pub(super) fn evaluation_depends_on_sorry<'a>(
    engine: &Engine,
    declarations: impl IntoIterator<Item = &'a Declaration>,
) -> Result<bool, EngineExecutionError> {
    let sorry = Name::from_components(["sorryAx"]);
    let library_only = engine.imported_modules().iter().all(|module| {
        let mut root = module.clone();
        while !root.parent().is_anonymous() {
            root = root.parent();
        }
        ["Init", "Std", "Lean", "Lake"]
            .iter()
            .any(|library| root == Name::from_components([*library]))
    });
    let imported = engine.imported_environment();
    let environment = engine.environment();
    let mut spent = 0;
    let mut pending = Vec::new();
    let mut references = |expr: &Expr, pending: &mut Vec<Name>| {
        let mut found = BTreeSet::new();
        collect_constant_references(expr, &mut found, &mut spent, usize::MAX).map_err(|error| {
            match error {
                ConstantReferenceCollectionError::PresentationLimit { observed, limit } => {
                    EngineExecutionError::SourceDependencyPresentationLimit { observed, limit }
                }
                ConstantReferenceCollectionError::AllocationFailure { requested } => {
                    EngineExecutionError::AllocationFailure {
                        resource: "evaluation sorry dependency worklist",
                        requested,
                    }
                }
            }
        })?;
        pending.extend(found);
        Ok::<(), EngineExecutionError>(())
    };
    for declaration in declarations {
        parts(declaration, &mut |part| match part {
            Part::Expression(expr) => references(expr, &mut pending),
            Part::Reference(name) => {
                pending.push(name.clone());
                Ok(())
            }
            Part::Declared(_) => Ok(()),
        })?;
    }
    let mut seen = BTreeSet::new();
    while let Some(name) = pending.pop() {
        if name == sorry {
            return Ok(true);
        }
        if !seen.insert(name.clone())
            || (library_only && imported.is_some_and(|imported| imported.contains(&name)))
        {
            continue;
        }
        match environment.find(&name) {
            Some(
                ConstantInfo::Axiom(fln_env::constants::AxiomVal { base, .. })
                | ConstantInfo::Ctor(fln_env::constants::ConstructorVal { base, .. })
                | ConstantInfo::Rec(fln_env::constants::RecursorVal { base, .. }),
            ) => references(&base.type_, &mut pending)?,
            Some(ConstantInfo::Defn(value)) => {
                references(&value.base.type_, &mut pending)?;
                references(&value.value, &mut pending)?;
            }
            Some(ConstantInfo::Thm(value)) => {
                references(&value.base.type_, &mut pending)?;
                references(&value.value, &mut pending)?;
            }
            Some(ConstantInfo::Opaque(value)) => {
                references(&value.base.type_, &mut pending)?;
                references(&value.value, &mut pending)?;
            }
            Some(ConstantInfo::Induct(value)) => {
                references(&value.base.type_, &mut pending)?;
                pending.extend(value.ctors.iter().cloned());
            }
            Some(ConstantInfo::Quot(_)) | None => {}
        }
    }
    Ok(false)
}

fn published(
    subjects: &SourceModuleVisibilitySubjects<'_>,
    visit: &mut impl FnMut(&Declaration, usize) -> Result<(), EngineExecutionError>,
) -> Result<(), EngineExecutionError> {
    for (execution, &owner) in subjects
        .completed
        .executions
        .iter()
        .zip(subjects.execution_owners)
    {
        visit(&execution.declaration, owner)?;
    }
    let mut previous = None;
    for command in &subjects.completed.source_admissions {
        if previous.is_some_and(|index| index >= command.command_index) {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "source admission indices are not strictly increasing",
            });
        }
        previous = Some(command.command_index);
        let Some(&owner) = subjects.command_owners.get(command.command_index) else {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "source admission escaped its command ownership table",
            });
        };
        for admission in &command.admission.admissions {
            visit(&admission.declaration, owner)?;
        }
    }
    Ok(())
}

fn tick(spent: &mut usize, limit: usize) -> Result<(), EngineExecutionError> {
    *spent = spent.saturating_add(1);
    if *spent > limit {
        Err(EngineExecutionError::SourceDependencyPresentationLimit {
            observed: *spent,
            limit,
        })
    } else {
        Ok(())
    }
}

pub(super) fn verify_declarations(
    modules: &[SourceModuleInput<'_>],
    subjects: SourceModuleVisibilitySubjects<'_>,
    visible: &[u64],
    words: usize,
    limit: usize,
) -> Result<(), EngineExecutionError> {
    let mut owners = BTreeMap::new();
    let mut spent = 0;
    published(&subjects, &mut |declaration, owner| {
        if owner >= modules.len() {
            return Err(EngineExecutionError::UnexpectedPublication {
                detail: "source admission names an unknown module",
            });
        }
        parts(declaration, &mut |part| {
            if let Part::Declared(name) = part {
                tick(&mut spent, limit)?;
                if owners.insert(name.clone(), owner).is_some() {
                    return Err(EngineExecutionError::UnexpectedPublication {
                        detail: "source stream published a duplicate constant",
                    });
                }
            }
            Ok(())
        })
    })?;
    let mut check = |declaration: &Declaration, owner: usize| {
        let mut name = None;
        let mut references = BTreeSet::new();
        parts(declaration, &mut |part| {
            match part {
                Part::Declared(current) => {
                    name.get_or_insert_with(|| current.clone());
                }
                Part::Reference(referenced) => {
                    tick(&mut spent, limit)?;
                    references.insert(referenced.clone());
                }
                Part::Expression(expr) => {
                    collect_constant_references(expr, &mut references, &mut spent, limit).map_err(
                        |error| match error {
                            ConstantReferenceCollectionError::PresentationLimit {
                                observed,
                                limit,
                            } => EngineExecutionError::SourceDependencyPresentationLimit {
                                observed,
                                limit,
                            },
                            ConstantReferenceCollectionError::AllocationFailure { requested } => {
                                EngineExecutionError::AllocationFailure {
                                    resource: "source declaration dependency worklist",
                                    requested,
                                }
                            }
                        },
                    )?;
                }
            }
            Ok(())
        })?;
        let name = name.ok_or(EngineExecutionError::UnexpectedPublication {
            detail: "source admission has no constants",
        })?;
        for referenced in references {
            let Some(&referenced_owner) = owners.get(&referenced) else {
                continue;
            };
            let bit = 1_u64 << (referenced_owner % u64::BITS as usize);
            if visible[owner * words + referenced_owner / u64::BITS as usize] & bit == 0 {
                return Err(EngineExecutionError::SourceModuleVisibility {
                    module: modules[owner].name.clone(),
                    declaration: name,
                    referenced,
                    owner: modules[referenced_owner].name.clone(),
                });
            }
        }
        Ok(())
    };
    published(&subjects, &mut check)?;
    for (query, &owner) in subjects.checks.iter().zip(subjects.check_owners) {
        check(&query.declaration, owner)?;
    }
    Ok(())
}

/// `native_decide`'s evaluator for one source command (`fln_elab::native`). The command's own
/// engine admits the elaborator's closed `Bool` definition into a scratch successor, compiles it
/// and runs it on Golem through the door `#eval`'s values use, and discards the successor: the
/// pin's `addAndCompile` and `evalConst` under `withoutModifyingEnv` (vendored
/// `Lean/Meta/Native.lean:43-69`). It decides nothing about the proposition itself.
pub(super) struct CommandEvaluator {
    engine: Engine,
    options: KVMap,
    limits: EngineExecutionLimits,
}

impl CommandEvaluator {
    /// The provider a command's scope carries, for `engine` as the command finds it.
    pub(super) fn provider(
        engine: &Engine,
        options: &KVMap,
        limits: EngineExecutionLimits,
    ) -> fln_elab::native::NativeProvider {
        fln_elab::native::NativeProvider(std::sync::Arc::new(Self {
            engine: engine.clone(),
            options: options.clone(),
            limits,
        }))
    }
}

impl fln_elab::native::NativeEvaluator for CommandEvaluator {
    fn evaluate_bool(
        &self,
        definition: &fln_env::constants::DefinitionVal,
    ) -> fln_elab::native::NativeEvaluation {
        use fln_elab::native::NativeEvaluation;
        let executed = self.engine.execute_definition_entry(
            Declaration::Defn(definition.clone()),
            &self.options,
            self.limits,
            source_evaluation::Entry::Value,
        );
        let execution = match executed {
            Ok(Outcome::Complete(execution)) => execution,
            Ok(Outcome::Inconclusive(reason)) => return NativeEvaluation::Inconclusive(reason),
            Ok(Outcome::InternalFault(fault)) => return NativeEvaluation::InternalFault(fault),
            // This engine's compiler covers a subset of the pin's: a refusal here is its own
            // limit, never the pin's `addAndCompile` error.
            Err(error) if source_check::classify(&error).0 == "internal-fault" => {
                return NativeEvaluation::InternalFault(InternalFault::new(
                    "native evaluation",
                    error.to_string(),
                ));
            }
            Err(error) => return NativeEvaluation::Unsupported(error.to_string()),
        };
        match &execution.exit {
            VmExit::Returned(_) => match closed_vm_value(&execution.exit) {
                Ok(Some(ClosedVmValue::Scalar(1))) => NativeEvaluation::Value(true),
                Ok(Some(ClosedVmValue::Scalar(0))) => NativeEvaluation::Value(false),
                other => NativeEvaluation::InternalFault(InternalFault::new(
                    "native evaluation",
                    format!("a closed `Bool` definition returned {other:?}"),
                )),
            },
            // The pin's `panic` reports and continues with the default value; Golem stops.
            VmExit::Panicked { message, .. } => NativeEvaluation::Unsupported(format!(
                "the evaluation panicked (`{message}`), which the pin reports and continues past"
            )),
            VmExit::Refused { refusal, .. } => {
                NativeEvaluation::Unsupported(format!("the VM refused the evaluation: {refusal}"))
            }
        }
    }
}
