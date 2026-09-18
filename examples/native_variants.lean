-- Payload layouts and case dispatch are derived from admitted declarations.
inductive Response where
  | missing
  | text (message : String)
  | value (count : Nat)

structure Envelope where
  payload : Response
  label : String

def score (response : Response) : Nat := match response with
  | .missing => 0
  | .text message => String.length message
  | .value count => count

def advance (n : Nat) (response : Response) : Response := match n with
  | .zero => response
  | .succ k => advance k (Response.value (score response + 1))

def answer : Nat :=
  let pack (response : Response) : Envelope := { payload := response, label := "hello" };
  let envelope : Envelope := pack (advance 7 (Response.value 30));
  score envelope.payload + String.length envelope.label

theorem score_value : score (Response.value 42) = 42 := by rfl
