//! Pinned character terms use the global Char.ofNat and a raw natural literal.
//!
//! This is ordinary typed application construction. It installs no Char model,
//! changes no numeric instance, and grants no execution or admission authority.

use super::*;

fn invalid() -> NatDefinitionElabError {
    NatDefinitionElabError::UnexpectedSyntax {
        expected: "one valid character literal atom",
    }
}

fn decode_character(spelling: &str) -> Result<char, NatDefinitionElabError> {
    use fln_syntax::literal::{LiteralKind, lex_literal, starts_literal};
    use fln_syntax::source::SourceText;

    let text = SourceText::from_utf8(spelling.as_bytes()).map_err(|_| invalid())?;
    // The pin's decoder assumes a parser-validated token. Recheck that contract
    // for externally supplied syntax, including the two-quote dispatch rule.
    if !spelling.starts_with('\'') || !starts_literal(&text, BytePos(0)) {
        return Err(invalid());
    }
    let token = lex_literal(&text, BytePos(0)).map_err(|_| invalid())?;
    if token.kind != LiteralKind::Char || token.extent.end().0 != spelling.len() {
        return Err(invalid());
    }
    // Char and String use the same quoted-character decoder. The Char lexer
    // above has already refused string gaps and multiple characters. Reusing
    // the existing decoder also preserves Char.ofNat's surrogate-to-NUL rule.
    let content = &spelling[1..spelling.len() - 1];
    let Literal::Str(decoded) = decode_string(&format!("\"{content}\"")).map_err(|_| invalid())?
    else {
        return Err(invalid());
    };
    let mut characters = decoded.chars();
    let character = characters.next().ok_or_else(invalid)?;
    if characters.next().is_some() {
        return Err(invalid());
    }
    Ok(character)
}

impl Context {
    pub(super) fn character_literal(
        &mut self,
        syntax: &Syntax,
    ) -> Result<Option<Typed>, NatDefinitionElabError> {
        let Syntax::Node { kind, args, .. } = syntax else {
            return Ok(None);
        };
        if kind != &Name::from_components(["char"]) {
            return Ok(None);
        }
        let [Syntax::Atom { val: spelling, .. }] = args.as_slice() else {
            return Err(invalid());
        };
        for _ in spelling.as_bytes() {
            self.tick()?;
        }
        let character = decode_character(spelling)?;
        // Lean.Elab.BuiltinTerm.elabCharLit builds this exact global constant,
        // bypassing local/namespace resolution just like _root_.Char.ofNat.
        // Its argument is a raw Nat: ordinary numeral notation would consult
        // OfNat instances and could change the meaning of a character literal.
        let function = self.constant(&Name::from_components(["Char", "ofNat"]))?;
        let signature = self.whnf(&function.type_)?;
        let ExprNode::ForallE {
            binder_type, body, ..
        } = signature.node()
        else {
            return Err(failure(SourceInferenceError::ExpectedFunction));
        };
        self.constrain_type(&nat_const(), binder_type)?;
        let number = Expr::lit(Literal::Nat(fln_core::expr::NatLit::from_u64(u64::from(
            u32::from(character),
        ))));
        let type_ = self.substitute(body, &number)?;
        Ok(Some(Typed {
            value: Expr::app(function.value, number),
            type_,
        }))
    }
}

#[cfg(test)]
mod tests;
