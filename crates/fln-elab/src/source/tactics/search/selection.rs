//! Selection is syntax, not a pre-instantiated proof. Replay supplied terms
//! inside each goal/choice context so one polymorphic rule can be used twice.
use super::*;

pub(in crate::source::tactics) struct Selection<'a> {
    pub all_goals: bool,
    pub defaults: bool,
    pub locals: bool,
    pub add: Vec<&'a Syntax>,
    pub remove: Vec<&'a Syntax>,
}

impl Default for Selection<'_> {
    fn default() -> Self {
        Self {
            all_goals: false,
            defaults: true,
            locals: true,
            add: Vec::new(),
            remove: Vec::new(),
        }
    }
}

fn kind(name: &str) -> Name {
    parser_kind(&["Tactic", "SolveByElim", name])
}

pub(in crate::source::tactics) fn selection(
    args: &[Syntax],
) -> Result<Selection<'_>, NatDefinitionElabError> {
    let [keyword, all_goals, config, only, arguments, using] = args else {
        return Err(error(TacticError::MalformedScript));
    };
    expect_atom(keyword, "solve_by_elim", "proof search tactic")?;
    let all_goals = match expect_null_args(all_goals, "proof search goal selection")? {
        [] => false,
        [atom] => {
            expect_atom(atom, "*", "proof search all-goals marker")?;
            true
        }
        _ => return Err(error(TacticError::MalformedScript)),
    };
    expect_default_config(config, "solve_by_elim configuration")?;
    expect_empty_null(using, "solve_by_elim label attributes")?;
    let only = match expect_null_args(only, "solve_by_elim only")? {
        [] => false,
        [keyword] => {
            expect_atom(keyword, "only", "proof search only keyword")?;
            true
        }
        _ => return Err(error(TacticError::MalformedScript)),
    };
    let mut result = Selection {
        all_goals,
        defaults: !only,
        locals: !only,
        ..Selection::default()
    };
    let parts = match expect_null_args(arguments, "proof search argument slot")? {
        [] => return Ok(result),
        [arguments] => expect_node(arguments, &kind("args"), 3, "proof search argument list")?,
        _ => return Err(error(TacticError::MalformedScript)),
    };
    expect_atom(&parts[0], "[", "proof search list opening")?;
    expect_atom(&parts[2], "]", "proof search list closing")?;
    let rows = expect_null_args(&parts[1], "proof search argument rows")?;
    let mut star = false;
    for (index, row) in rows.iter().enumerate() {
        if index % 2 == 1 {
            expect_atom(row, ",", "proof search argument separator")?;
            continue;
        }
        let [argument] = expect_node(row, &kind("arg"), 1, "proof search argument")? else {
            return Err(error(TacticError::MalformedScript));
        };
        if argument.kind() == Some(&kind("star")) {
            let [atom] = expect_node(argument, &kind("star"), 1, "proof search wildcard")? else {
                return Err(error(TacticError::MalformedScript));
            };
            expect_atom(atom, "*", "proof search wildcard")?;
            star = true;
        } else if argument.kind() == Some(&kind("erase")) {
            let [minus, term] = expect_node(argument, &kind("erase"), 2, "proof search erasure")?
            else {
                return Err(error(TacticError::MalformedScript));
            };
            expect_atom(minus, "-", "proof search erasure")?;
            result.remove.push(term);
        } else {
            result.add.push(argument);
        }
    }
    if star && !only {
        return Err(error(TacticError::InvalidSearchArguments(
            "`*` requires `only`",
        )));
    }
    if !result.remove.is_empty() && only && !star {
        return Err(error(TacticError::InvalidSearchArguments(
            "removing hypotheses with `only` requires `*`",
        )));
    }
    result.locals |= star;
    Ok(result)
}

#[derive(Clone)]
pub(super) enum Candidate<'a> {
    Local(LocalDecl),
    Explicit(&'a Syntax),
}

impl Context {
    pub(super) fn selected_search_candidates<'a>(
        &mut self,
        goal: &ProofGoal,
        selection: &Selection<'a>,
    ) -> Result<Vec<Candidate<'a>>, NatDefinitionElabError> {
        self.txn.lctx = goal.lctx.clone();
        let mut excluded = Vec::new();
        for syntax in &selection.remove {
            self.tick()?;
            let term = self.term(syntax, None)?;
            excluded.push(self.instantiate(&term.value)?);
        }
        // Even unused supplied terms must be well-formed: an available local
        // cannot hide an unknown name or a resource stop in the argument list.
        // Discard these probe assignments, then elaborate the chosen term in
        // the candidate's own snapshot (including its own instance obligations).
        let snapshot = self.clone();
        let validated = (|| {
            for syntax in &selection.add {
                self.tick()?;
                self.term(syntax, None)?;
                restore(self, &snapshot);
            }
            Ok(())
        })();
        restore(self, &snapshot);
        validated?;
        let mut candidates = Vec::new();
        if selection.locals {
            for local in goal.lctx.decls().iter().rev() {
                self.tick()?;
                if !self.is_matrix_hypothesis(local)
                    && !excluded.contains(&Expr::fvar(local.id.clone()))
                {
                    candidates.push(Candidate::Local(local.clone()));
                }
            }
        }
        candidates.extend(
            selection
                .add
                .iter()
                .map(|syntax| Candidate::Explicit(syntax)),
        );
        Ok(candidates)
    }
}
