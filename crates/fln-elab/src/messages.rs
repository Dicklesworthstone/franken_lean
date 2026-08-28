//! Message log and diagnostic recording for Athanor (plan §10.1).

use fln_core::pos::Position;

/// Severity of an elaboration diagnostic message.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum MessageSeverity {
    Information,
    Warning,
    Error,
}

/// An elaboration diagnostic message (Lean.Message).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Message {
    pub severity: MessageSeverity,
    pub pos: Option<Position>,
    pub end_pos: Option<Position>,
    pub caption: String,
    pub text: String,
}

impl Message {
    pub fn info(text: impl Into<String>) -> Self {
        Self {
            severity: MessageSeverity::Information,
            pos: None,
            end_pos: None,
            caption: String::new(),
            text: text.into(),
        }
    }

    pub fn warning(text: impl Into<String>) -> Self {
        Self {
            severity: MessageSeverity::Warning,
            pos: None,
            end_pos: None,
            caption: String::new(),
            text: text.into(),
        }
    }

    pub fn error(text: impl Into<String>) -> Self {
        Self {
            severity: MessageSeverity::Error,
            pos: None,
            end_pos: None,
            caption: String::new(),
            text: text.into(),
        }
    }

    pub fn with_pos(mut self, pos: Position) -> Self {
        self.pos = Some(pos);
        self
    }
}

/// A collection of messages produced during elaboration.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct MessageLog {
    messages: Vec<Message>,
}

impl MessageLog {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn is_empty(&self) -> bool {
        self.messages.is_empty()
    }

    pub fn len(&self) -> usize {
        self.messages.len()
    }

    pub fn messages(&self) -> &[Message] {
        &self.messages
    }

    pub fn add(&mut self, msg: Message) {
        self.messages.push(msg);
    }

    pub fn has_errors(&self) -> bool {
        self.messages
            .iter()
            .any(|m| m.severity == MessageSeverity::Error)
    }

    pub fn has_warnings(&self) -> bool {
        self.messages
            .iter()
            .any(|m| m.severity == MessageSeverity::Warning)
    }

    pub fn append(&mut self, other: &mut MessageLog) {
        self.messages.append(&mut other.messages);
    }

    pub fn truncate(&mut self, checkpoint: usize) {
        self.messages.truncate(checkpoint);
    }
}
