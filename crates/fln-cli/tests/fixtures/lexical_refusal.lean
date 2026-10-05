-- A source the pinned Reference refuses at its lexer (bead fln-vokf): `§` is not a token at
-- v4.32.0, so `lean` reports `4:22: error: expected token`. Tests that need a frontend
-- refusal from the lexer use this file; it must stay unlexable at the pin.
def broken : Nat := 1 § 2
