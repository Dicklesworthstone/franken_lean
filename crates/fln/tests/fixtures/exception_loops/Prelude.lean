
structure Prod (A B : Type) where
  fst : A
  snd : B
class Pure (m : Type -> Type) where
  pure : {A : Type} -> A -> m A
class Bind (m : Type -> Type) where
  bind : {A B : Type} -> m A -> (A -> m B) -> m B
class Functor (m : Type -> Type) where
  map : {A B : Type} -> (A -> B) -> m A -> m B
class MonadExcept (E : outParam Type) (m : Type -> Type) where
  throw : {A : Type} -> E -> m A
  tryCatch : {A : Type} -> m A -> (E -> m A) -> m A
class MonadFinally (m : Type -> Type) where
  tryFinally' : {A B : Type} -> m A -> (Option A -> m B) -> m (Prod A B)
def tryFinally {m : Type -> Type} {A B : Type} [fin : MonadFinally m] [mapping : Functor m] (x : m A) (cleanup : m B) : m A :=
  @Functor.map m mapping (Prod A B) A (fun (p : Prod A B) => p.fst) (@MonadFinally.tryFinally' m fin A B x (fun _ => cleanup))
inductive Attempt (E A : Type) where
  | ok (value : A)
  | error (value : E)
structure Report (A : Type) where
  output : Attempt Nat A
  state : Nat
def Logged (A : Type) : Type := Nat -> Report A
def loggedBind {A B : Type} (x : Logged A) (f : A -> Logged B) : Logged B := fun s =>
  let r := x s
  match r.output with
  | Attempt.ok a => f a r.state
  | Attempt.error e => Report.mk (Attempt.error e) r.state
def loggedCatch {A : Type} (x : Logged A) (f : Nat -> Logged A) : Logged A := fun s =>
  let r := x s
  match r.output with
  | Attempt.ok a => Report.mk (Attempt.ok a) r.state
  | Attempt.error e => f e r.state
def loggedMap {A B : Type} (f : A -> B) (x : Logged A) : Logged B := fun s =>
  let r := x s
  match r.output with
  | Attempt.ok a => Report.mk (Attempt.ok (f a)) r.state
  | Attempt.error e => Report.mk (Attempt.error e) r.state
def loggedFinally {A B : Type} (x : Logged A) (f : Option A -> Logged B) : Logged (Prod A B) := fun s =>
  let r := x s
  match r.output with
  | Attempt.ok a =>
    let c := f (Option.some a) r.state
    match c.output with
    | Attempt.ok b => Report.mk (Attempt.ok (Prod.mk a b)) c.state
    | Attempt.error e => Report.mk (Attempt.error e) c.state
  | Attempt.error e =>
    let c := f Option.none r.state
    match c.output with
    | Attempt.ok b => Report.mk (Attempt.error e) c.state
    | Attempt.error other => Report.mk (Attempt.error other) c.state
instance loggedPure : Pure Logged := Pure.mk (fun a s => Report.mk (Attempt.ok a) s)
instance loggedBinding : Bind Logged := Bind.mk (fun a f => loggedBind a f)
instance loggedFunctor : Functor Logged := Functor.mk (fun f a => loggedMap f a)
instance loggedException : MonadExcept Nat Logged := MonadExcept.mk (fun {A : Type} (e : Nat) (s : Nat) => @Report.mk A (@Attempt.error Nat A e) s) (fun {A : Type} (x : Logged A) (f : Nat -> Logged A) => @loggedCatch A x f)
instance loggedFinalizer : MonadFinally Logged := MonadFinally.mk (fun x f => loggedFinally x f)
def succeed {A : Type} (a : A) : Logged A := @Pure.pure Logged loggedPure A a
def raise {A : Type} (e : Nat) : Logged A := @MonadExcept.throw Nat Logged loggedException A e
def mark (n : Nat) : Logged Nat := fun s => Report.mk (Attempt.ok n) (s * 10 + n)
def observed (action : Logged Nat) : Nat :=
  let r := action 0
  match r.output with
  | Attempt.ok n => r.state * 1000 + n
  | Attempt.error e => r.state * 1000 + 100 + e
inductive ForInStep (A : Type) where
  | done (value : A)
  | yield (value : A)
class ForIn (m : Type -> Type) (R : Type) (A : outParam Type) where
  forIn : {B : Type} -> R -> B -> (A -> B -> m (ForInStep B)) -> m B
structure Two where
  first : Nat
  second : Nat
def stepValue {A : Type} (step : ForInStep A) : A :=
  match step with
  | ForInStep.done value => value
  | ForInStep.yield value => value
def finishTwo {B : Type} (n : Nat) (f : Nat -> B -> Logged (ForInStep B)) (step : ForInStep B) : Logged B :=
  match step with
  | ForInStep.done value => succeed value
  | ForInStep.yield value => loggedBind (f n value) (fun last => succeed (stepValue last))
def forTwo {B : Type} (xs : Two) (b : B) (f : Nat -> B -> Logged (ForInStep B)) : Logged B :=
  loggedBind (f xs.first b) (fun step => finishTwo xs.second f step)
instance loggedTwoFor : ForIn Logged Two Nat := ForIn.mk (fun xs b f => forTwo xs b f)
def items : Two := Two.mk 1 2
def note (n : Nat) : Logged PUnit := fun s => Report.mk (Attempt.ok PUnit.unit) (s * 10 + n)
