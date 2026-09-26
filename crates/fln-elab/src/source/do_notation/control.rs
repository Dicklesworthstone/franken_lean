//! Local loop exits are ordinary ForInStep values, never VM jumps.
use super::*;

pub(super) struct LoopTargets {
    accumulator: Syntax,
}
impl LoopTargets {
    /// `expand_for_loop` supplies exactly `pure (ForInStep.yield accumulator)`.
    /// Validate that private handoff before deriving the other exit. The
    /// accumulator is one fresh identifier, not an action to clone or rerun.
    pub(super) fn new(normal: &Syntax) -> Result<Self, NatDefinitionElabError> {
        let pure = expect_node(normal, &parser_kind(&["Term", "nativeDoPure"]), 1, "loop exit")?;
        let app = expect_node(&pure[0], &parser_kind(&["Term", "app"]), 2, "loop step")?;
        if !matches!(&app[0], Syntax::Ident {val,..}
            if val == &Name::from_components(["_root_", "ForInStep", "yield"]))
        {
            return Err(invalid());
        }
        let [accumulator] = expect_null_args(&app[1], "loop accumulator")? else {
            return Err(invalid());
        };
        if !matches!(accumulator, Syntax::Ident {val,..}
            if !val.is_anonymous() && val.parent().is_anonymous())
        {
            return Err(invalid());
        }
        Ok(Self { accumulator: accumulator.clone() })
    }
    fn exit(&self, stop: bool) -> Syntax {
        let constructor = ident(Name::from_components([
            "_root_", "ForInStep", if stop { "done" } else { "yield" },
        ]));
        let step = Syntax::node(
            parser_kind(&["Term", "app"]),
            vec![constructor, null(vec![self.accumulator.clone()])],
        );
        call(false, vec![step])
    }
}

pub(super) fn is_jump(element: &Syntax) -> bool {
    element.kind().is_some_and(|kind|
        kind == &parser_kind(&["Term", "doBreak"])
            || kind == &parser_kind(&["Term", "doContinue"]))
}

pub(super) fn jump(
    element: Syntax,
    targets: Option<&LoopTargets>,
) -> Result<Syntax, NatDefinitionElabError> {
    let stop = element.kind() == Some(&parser_kind(&["Term", "doBreak"]));
    let parts = node(element, if stop { "doBreak" } else { "doContinue" }, 1)?;
    expect_atom(&parts[0], if stop { "break" } else { "continue" }, "loop control keyword")?;
    Ok(targets.ok_or_else(invalid)?.exit(stop))
}

#[cfg(test)]
mod tests {
    use super::*;
    fn term(kind: &str, args: Vec<Syntax>) -> Syntax {
        Syntax::node(parser_kind(&["Term", kind]), args)
    }
    fn sequence(elements: Vec<Syntax>) -> Syntax {
        term("doSeqIndent", vec![null(elements.into_iter()
            .map(|element| term("doSeqItem", vec![element, null(vec![])]))
            .collect())])
    }
    fn context() -> Context {
        Context::new(&Environment::new(), Budget::for_stack_bytes(2 * 1024 * 1024))
    }
    fn normal() -> Syntax {
        LoopTargets { accumulator: ident(Name::num(Name::anonymous(), 99)) }.exit(false)
    }
    fn keyword(stop: bool) -> Syntax {
        term(if stop { "doBreak" } else { "doContinue" },
            vec![atom(if stop { "break" } else { "continue" })])
    }
    #[test]
    fn break_and_continue_have_distinct_checked_step_constructors() {
        for stop in [false, true] {
            let targets = LoopTargets::new(&normal()).unwrap();
            let result = context().expand_do_sequence(sequence(vec![keyword(stop)]), Some(normal())).unwrap();
            assert_eq!(result, targets.exit(stop));
        }
        assert_ne!(LoopTargets::new(&normal()).unwrap().exit(false),
            LoopTargets::new(&normal()).unwrap().exit(true));
    }
    #[test]
    fn missing_loop_scope_and_unreachable_suffix_fail_closed() {
        for stop in [false, true] {
            assert!(context().expand_do_sequence(sequence(vec![keyword(stop)]), None).is_err());
            let body = sequence(vec![keyword(stop), term("doExpr", vec![ident(Name::from_components(["bad"]))])]);
            assert!(context().expand_do_sequence(body, Some(normal())).is_err());
            let nested = term("do", vec![atom("do"), sequence(vec![keyword(stop)])]);
            assert!(context().expand_do_node(nested, false).is_err());
        }
    }
    #[test]
    fn malformed_control_and_noncanonical_exit_handoffs_fail_closed() {
        let targets = LoopTargets::new(&normal()).unwrap();
        for invalid in [term("doBreak", vec![]), term("doBreak", vec![atom("continue")]),
            term("doContinue", vec![atom("continue"), atom("extra")])] {
            assert!(jump(invalid, Some(&targets)).is_err());
        }
        assert!(LoopTargets::new(&atom("untrusted")).is_err());
        let invalid = call(false, vec![term("app", vec![ident(Name::from_components(["yield"])), null(vec![atom("x")])])]);
        assert!(LoopTargets::new(&invalid).is_err());
    }
    #[test]
    fn prefix_actions_stay_before_the_exit_and_resource_stops_recover() {
        let action = term("doExpr", vec![ident(Name::from_components(["effect"]))]);
        let body = sequence(vec![action, keyword(true)]);
        let result = context().expand_do_sequence(body.clone(), Some(normal())).unwrap();
        assert_eq!(result.kind(), Some(&parser_kind(&["Term", "nativeDoBind"])));
        let mut stopped = context();
        stopped.txn.budget.max_heartbeats = 1;
        assert!(matches!(stopped.expand_do_sequence(body.clone(), Some(normal())),
            Err(NatDefinitionElabError::Inference(SourceInferenceError::ResourceLimit))));
        assert!(context().expand_do_sequence(body, Some(normal())).is_ok());
    }
}
