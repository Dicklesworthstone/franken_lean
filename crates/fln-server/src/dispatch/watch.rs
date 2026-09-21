//! One bounded, capability-negotiated client watcher registration per session.
use super::*;
use json::{RegistrationReply, registration_reply, supports_file_registration};

const REQUEST_ID: &str = "frankenLean/source-watch/1";

#[derive(Default)]
pub(super) struct Registration {
    supported: bool,
    requested: bool,
    pending: bool,
}
impl Registration {
    pub(super) fn configure(&mut self, params: RawField<'_>, enabled: bool) {
        self.supported = enabled && supports_file_registration(params);
    }
    pub(super) fn start(&mut self, output: &mut dyn Write) -> io::Result<()> {
        if !self.supported || self.requested {
            return Ok(());
        }
        self.requested = true;
        self.pending = true;
        write_protocol_message(
            output,
            format!(
                r#"{{"jsonrpc":"2.0","id":"{REQUEST_ID}","method":"client/registerCapability","params":{{"registrations":[{{"id":"{REQUEST_ID}","method":"workspace/didChangeWatchedFiles","registerOptions":{{"watchers":[{{"globPattern":"**/*.lean","kind":7}}]}}}}]}}}}"#,
            ),
        )
    }
    pub(super) fn stop(&mut self) {
        self.pending = false;
    }

    /// This response is in the server->client request namespace. A client
    /// request with the same id and an actual method is never consumed here.
    /// Malformed/duplicate/late replies cannot cause a response loop or mark a
    /// document checked; they only produce a bounded warning.
    pub(super) fn consume(
        &mut self,
        output: &mut dyn Write,
        message: &str,
        envelope: &Envelope<'_>,
    ) -> io::Result<bool> {
        if envelope.method != DecodedField::Missing
            || !matches!(&envelope.id, RequestIdField::Valid(RequestId::Text(id)) if id == REQUEST_ID)
        {
            return Ok(false);
        }
        if !self.pending {
            write_warning(
                output,
                "FrankenLean ignored an unsolicited or duplicate file-watcher registration response",
            )?;
            return Ok(true);
        }
        self.pending = false;
        match registration_reply(message) {
            RegistrationReply::Accepted => {}
            RegistrationReply::Rejected => write_warning(
                output,
                "Client declined Lean source file watching; editor buffer checking remains available",
            )?,
            RegistrationReply::Malformed => write_warning(
                output,
                "Client sent a malformed file-watcher registration response; watching is not confirmed",
            )?,
        }
        Ok(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const CAPS: &str =
        r#"{"capabilities":{"workspace":{"didChangeWatchedFiles":{"dynamicRegistration":true}}}}"#;
    fn reply(value: &str) -> String {
        format!(r#"{{"jsonrpc":"2.0","id":"{REQUEST_ID}",{value}}}"#)
    }
    #[test]
    fn registration_is_capability_gated_and_sent_once() {
        let mut state = Registration::default();
        let mut out = Vec::new();
        state.start(&mut out).unwrap();
        assert!(out.is_empty());
        state.configure(RawField::Value(CAPS), false);
        state.start(&mut out).unwrap();
        assert!(out.is_empty());
        state.configure(RawField::Value(CAPS), true);
        state.start(&mut out).unwrap();
        let once = out.clone();
        state.start(&mut out).unwrap();
        assert_eq!(once, out);
        let body = transport::read_message(&mut std::io::Cursor::new(out))
            .unwrap()
            .unwrap();
        let body = String::from_utf8(body).unwrap();
        assert_eq!(
            parse_envelope(&body).unwrap().method,
            DecodedField::Valid("client/registerCapability".to_owned())
        );
        assert!(body.contains(r#""globPattern":"**/*.lean","kind":7"#));
    }
    #[test]
    fn response_ids_roles_and_completion_are_not_document_authority() {
        let mut state = Registration::default();
        state.configure(RawField::Value(CAPS), true);
        state.start(&mut Vec::new()).unwrap();
        let mut out = Vec::new();
        for body in [
            reply(r#""method":"textDocument/hover","params":{}"#),
            r#"{"jsonrpc":"2.0","id":"other","result":null}"#.to_owned(),
        ] {
            assert!(
                !state
                    .consume(&mut out, &body, &parse_envelope(&body).unwrap())
                    .unwrap()
            );
            assert!(state.pending);
        }
        let body = reply(r#""result":null"#);
        assert!(
            state
                .consume(&mut out, &body, &parse_envelope(&body).unwrap())
                .unwrap()
        );
        assert!(!state.pending && out.is_empty());
        assert!(
            state
                .consume(&mut out, &body, &parse_envelope(&body).unwrap())
                .unwrap()
        );
        let out = String::from_utf8(out).unwrap();
        assert!(out.contains("duplicate file-watcher"));
        assert!(!out.contains("\"result\"") && !out.contains("publishDiagnostics"));
    }
    #[test]
    fn rejected_malformed_and_shutdown_replies_do_not_retry_or_break_the_session() {
        for value in [
            r#""error":{"code":-32601,"message":"no"}"#,
            r#""result":{}"#,
            r#""result":null,"error":{}"#,
        ] {
            let mut state = Registration::default();
            state.configure(RawField::Value(CAPS), true);
            state.start(&mut Vec::new()).unwrap();
            let body = reply(value);
            let mut out = Vec::new();
            assert!(
                state
                    .consume(&mut out, &body, &parse_envelope(&body).unwrap())
                    .unwrap()
            );
            assert!(!state.pending);
            let size = out.len();
            state.start(&mut out).unwrap();
            assert_eq!(size, out.len());
        }
        let mut state = Registration::default();
        state.configure(RawField::Value(CAPS), true);
        state.start(&mut Vec::new()).unwrap();
        state.stop();
        let body = reply(r#""result":null"#);
        let mut out = Vec::new();
        assert!(
            state
                .consume(&mut out, &body, &parse_envelope(&body).unwrap())
                .unwrap()
        );
        assert!(String::from_utf8(out).unwrap().contains("unsolicited"));
    }
}
