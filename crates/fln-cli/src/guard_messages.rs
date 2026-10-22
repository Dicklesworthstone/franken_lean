//! Route captured diagnostics before display, preserving command order.
use fln_parse::command_scope::guard_spec::{Action, GuardSpec, Severity};

pub(super) struct Buffer<'a> {
    pub spec: &'a GuardSpec,
    pub checked: Vec<String>,
    pub from_check: bool,
    /// A checked trace has an actual producer; an expected trace alone does not.
    pub has_trace: bool,
}

pub(super) type Guards<'a> = std::collections::BTreeMap<usize, Buffer<'a>>;

impl<'a> Buffer<'a> {
    pub fn new(spec: &'a GuardSpec) -> Self {
        Self {
            spec,
            checked: Vec::new(),
            from_check: false,
            has_trace: false,
        }
    }

    /// False delegates to the original positioned/import-aware warning sink.
    pub fn warning(&mut self, message: &str) -> bool {
        match self.spec.action(Severity::Warning) {
            Action::Check => {
                self.checked.push(super::guard_message("warning", message));
                true
            }
            Action::Drop => true,
            Action::Pass => false,
        }
    }

    /// An error the engine logged for this guard's command, which it logs only when the
    /// guard checks errors and expects one; a mismatch against it is a non-answer.
    pub fn error(&mut self, message: &str) -> bool {
        match self.spec.action(Severity::Error) {
            Action::Check => {
                self.checked.push(super::guard_message("error", message));
                true
            }
            Action::Drop | Action::Pass => false,
        }
    }

    /// `line` is the original display line, including its final newline.
    pub fn info(&mut self, line: &str, from_check: bool, stdout: &mut String) {
        match self.spec.action(Severity::Info) {
            Action::Check => {
                self.checked
                    .push(super::guard_message("info", line.trim_end_matches('\n')));
                self.from_check |= from_check;
            }
            Action::Drop => {}
            Action::Pass => stdout.push_str(line),
        }
    }

    /// All three policies traverse the bounded formatter. Dropping a message
    /// must not bypass malformed-value checks or formatted-output resource limits.
    pub fn evaluation_target<'b>(
        &'b mut self,
        discarded: &'b mut Vec<String>,
    ) -> Option<&'b mut Vec<String>> {
        match self.spec.action(Severity::Info) {
            Action::Check => Some(&mut self.checked),
            Action::Drop => Some(discarded),
            Action::Pass => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use fln_parse::command_scope::guard_spec::Filter;

    fn spec(action: Action) -> GuardSpec {
        GuardSpec {
            filters: vec![Filter {
                action,
                severity: Some(Severity::Info),
            }],
            ..GuardSpec::default()
        }
    }

    #[test]
    fn check_rendering_uncertainty_belongs_only_to_checked_messages() {
        for action in [Action::Check, Action::Drop, Action::Pass] {
            let spec = spec(action);
            let mut buffer = Buffer::new(&spec);
            let mut stdout = "before\n".to_owned();
            buffer.info("x : Nat\n", true, &mut stdout);
            stdout.push_str("after\n");
            assert_eq!(buffer.from_check, action == Action::Check);
            assert_eq!(buffer.checked.len(), usize::from(action == Action::Check));
            assert_eq!(
                stdout,
                if action == Action::Pass {
                    "before\nx : Nat\nafter\n"
                } else {
                    "before\nafter\n"
                }
            );
        }
    }

    #[test]
    fn dropping_formatted_messages_still_charges_the_output_budget() {
        let spec = spec(Action::Drop);
        let mut buffer = Buffer::new(&spec);
        let mut discarded = Vec::new();
        let mut stdout = String::new();
        let mut budget = crate::source_evaluation::FormattedOutputBudget::new(1);
        let result = budget.append(
            "a message too large",
            &mut stdout,
            buffer.evaluation_target(&mut discarded),
        );
        assert!(result.is_err());
        assert!(stdout.is_empty() && buffer.checked.is_empty());
    }
}
