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
