prelude
import Init.Prelude
import Init.Tactics

-- Every dictionary uses actual imported class declarations. All flattened
-- fields are explicit so parent activation is tested independently of defaults.
structure ImportedRecordBox (A : Type) where
  value : A

def importedRecordPure {A : Type} (value : A) : ImportedRecordBox A :=
  ImportedRecordBox.mk value

def importedRecordMap {A B : Type} (transform : A -> B)
    (input : ImportedRecordBox A) : ImportedRecordBox B :=
  ImportedRecordBox.mk (transform input.value)

def importedRecordMapConst {A B : Type} (value : A)
    (input : ImportedRecordBox B) : ImportedRecordBox A :=
  ImportedRecordBox.mk value

def importedRecordBind {A B : Type} (input : ImportedRecordBox A)
    (continuation : A -> ImportedRecordBox B) : ImportedRecordBox B :=
  continuation input.value

def importedRecordSeq {A B : Type} (transform : ImportedRecordBox (A -> B))
    (argument : Unit -> ImportedRecordBox A) : ImportedRecordBox B :=
  ImportedRecordBox.mk (transform.value (argument Unit.unit).value)

def importedRecordSeqLeft {A B : Type} (left : ImportedRecordBox A)
    (right : Unit -> ImportedRecordBox B) : ImportedRecordBox A := left

def importedRecordSeqRight {A B : Type} (left : ImportedRecordBox A)
    (right : Unit -> ImportedRecordBox B) : ImportedRecordBox B := right Unit.unit

def importedPureDictionary : Pure ImportedRecordBox :=
  { pure := @importedRecordPure }

def importedBindDictionary : Bind ImportedRecordBox :=
  { bind := @importedRecordBind }

def importedFunctorDictionary : Functor ImportedRecordBox :=
  { map := @importedRecordMap, mapConst := @importedRecordMapConst }

def importedSeqDictionary : Seq ImportedRecordBox :=
  { seq := @importedRecordSeq }

def importedSeqLeftDictionary : SeqLeft ImportedRecordBox :=
  { seqLeft := @importedRecordSeqLeft }

def importedSeqRightDictionary : SeqRight ImportedRecordBox :=
  { seqRight := @importedRecordSeqRight }

def importedApplicativeDictionary : Applicative ImportedRecordBox :=
  { map := @importedRecordMap, mapConst := @importedRecordMapConst,
    pure := @importedRecordPure, seq := @importedRecordSeq,
    seqLeft := @importedRecordSeqLeft, seqRight := @importedRecordSeqRight }

def importedMonadDictionary : Monad ImportedRecordBox :=
  { map := @importedRecordMap, mapConst := @importedRecordMapConst,
    pure := @importedRecordPure, seq := @importedRecordSeq,
    seqLeft := @importedRecordSeqLeft, seqRight := @importedRecordSeqRight,
    bind := @importedRecordBind }

def importedMonadParts : Monad ImportedRecordBox :=
  { toApplicative := importedApplicativeDictionary, toBind := importedBindDictionary }

def importedMonadMixed : Monad ImportedRecordBox :=
  { toApplicative := importedApplicativeDictionary, bind := @importedRecordBind }

def importedPureRun (n : Nat) : Nat :=
  (@Pure.pure ImportedRecordBox importedPureDictionary Nat n).value

def importedBindRun (n : Nat) : Nat :=
  (@Bind.bind ImportedRecordBox importedBindDictionary Nat Nat
    (ImportedRecordBox.mk n) (fun value => ImportedRecordBox.mk (value + 2))).value

def importedFunctorRun (n : Nat) : Nat :=
  (@Functor.map ImportedRecordBox importedFunctorDictionary Nat Nat
    (fun value => value + 1) (ImportedRecordBox.mk n)).value

def importedMapConstRun (n : Nat) : Nat :=
  (@Functor.mapConst ImportedRecordBox importedFunctorDictionary Nat Nat n
    (ImportedRecordBox.mk 99)).value

def importedSeqRun (n : Nat) : Nat :=
  (@Seq.seq ImportedRecordBox importedSeqDictionary Nat Nat
    (ImportedRecordBox.mk (fun value => value + 2))
    (fun unit => ImportedRecordBox.mk n)).value

def importedSeqLeftRun (n : Nat) : Nat :=
  (@SeqLeft.seqLeft ImportedRecordBox importedSeqLeftDictionary Nat Nat
    (ImportedRecordBox.mk n) (fun unit => ImportedRecordBox.mk 99)).value

def importedSeqRightRun (n : Nat) : Nat :=
  (@SeqRight.seqRight ImportedRecordBox importedSeqRightDictionary Nat Nat
    (ImportedRecordBox.mk 99) (fun unit => ImportedRecordBox.mk n)).value

def importedApplicativeRun (n : Nat) : Nat :=
  (@Pure.pure ImportedRecordBox
    (@Applicative.toPure ImportedRecordBox importedApplicativeDictionary) Nat n).value

def importedMonadPureRun (n : Nat) : Nat :=
  (@Pure.pure ImportedRecordBox
    (@Applicative.toPure ImportedRecordBox
      (@Monad.toApplicative ImportedRecordBox importedMonadDictionary)) Nat n).value

def importedMonadBindRun (n : Nat) : Nat :=
  (@Bind.bind ImportedRecordBox
    (@Monad.toBind ImportedRecordBox importedMonadDictionary) Nat Nat
    (ImportedRecordBox.mk n) (fun value => ImportedRecordBox.mk (value + 2))).value

def importedMonadPartsRun (n : Nat) : Nat :=
  (@Bind.bind ImportedRecordBox
    (@Monad.toBind ImportedRecordBox importedMonadParts) Nat Nat
    (ImportedRecordBox.mk n) (fun value => ImportedRecordBox.mk (value + 2))).value

def importedMonadMixedRun (n : Nat) : Nat :=
  (@Bind.bind ImportedRecordBox
    (@Monad.toBind ImportedRecordBox importedMonadMixed) Nat Nat
    (ImportedRecordBox.mk n) (fun value => ImportedRecordBox.mk (value + 2))).value

-- Observable dictionary methods distinguish defaults, overrides and supplied
-- parent instances without imposing any Monad laws.
structure ImportedTagged (A : Type) where
  value : A
  stamp : Nat

def importedTaggedPure {A : Type} (value : A) : ImportedTagged A :=
  ImportedTagged.mk value 7

def importedTaggedBind {A B : Type} (input : ImportedTagged A)
    (continuation : A -> ImportedTagged B) : ImportedTagged B :=
  let result := continuation input.value
  ImportedTagged.mk result.value (input.stamp * 10 + result.stamp)

def importedTaggedMap {A B : Type} (transform : A -> B)
    (input : ImportedTagged A) : ImportedTagged B :=
  ImportedTagged.mk (transform input.value) 99

def importedTaggedMapConst {A B : Type} (value : A)
    (input : ImportedTagged B) : ImportedTagged A :=
  ImportedTagged.mk value 88

def importedTaggedGlobalMapConst {A B : Type} (value : A)
    (input : ImportedTagged B) : ImportedTagged A :=
  ImportedTagged.mk value 77

def importedDefaultMonad : Monad ImportedTagged :=
  { pure := @importedTaggedPure, bind := @importedTaggedBind }

def importedReorderedMonad : Monad ImportedTagged :=
  { bind := @importedTaggedBind, pure := @importedTaggedPure }

def importedOverrideMonad : Monad ImportedTagged :=
  { bind := @importedTaggedBind, map := @importedTaggedMap,
    pure := @importedTaggedPure }

def importedTaggedFunctor (dictionary : Monad ImportedTagged) : Functor ImportedTagged :=
  @Applicative.toFunctor ImportedTagged
    (@Monad.toApplicative ImportedTagged dictionary)

def importedTaggedSeq (dictionary : Monad ImportedTagged) : Seq ImportedTagged :=
  @Applicative.toSeq ImportedTagged
    (@Monad.toApplicative ImportedTagged dictionary)

def importedDefaultMap (n : Nat) : ImportedTagged Nat :=
  @Functor.map ImportedTagged (importedTaggedFunctor importedDefaultMonad) Nat Nat
    (fun value => value + 2) (ImportedTagged.mk n 3)

def importedReorderedMap (n : Nat) : ImportedTagged Nat :=
  @Functor.map ImportedTagged (importedTaggedFunctor importedReorderedMonad) Nat Nat
    (fun value => value + 2) (ImportedTagged.mk n 3)

def importedOverrideMap (n : Nat) : ImportedTagged Nat :=
  @Functor.map ImportedTagged (importedTaggedFunctor importedOverrideMonad) Nat Nat
    (fun value => value + 2) (ImportedTagged.mk n 3)

def importedDefaultMapConst (n : Nat) : ImportedTagged Nat :=
  @Functor.mapConst ImportedTagged (importedTaggedFunctor importedDefaultMonad) Nat Nat
    n (ImportedTagged.mk 99 3)

def importedOverrideMapConst (n : Nat) : ImportedTagged Nat :=
  @Functor.mapConst ImportedTagged (importedTaggedFunctor importedOverrideMonad) Nat Nat
    n (ImportedTagged.mk 99 3)

def importedDefaultSeq (n : Nat) : ImportedTagged Nat :=
  @Seq.seq ImportedTagged (importedTaggedSeq importedDefaultMonad) Nat Nat
    (ImportedTagged.mk (fun value => value + 2) 2)
    (fun unit => ImportedTagged.mk n 3)

def importedOverrideSeq (n : Nat) : ImportedTagged Nat :=
  @Seq.seq ImportedTagged (importedTaggedSeq importedOverrideMonad) Nat Nat
    (ImportedTagged.mk (fun value => value + 2) 2)
    (fun unit => ImportedTagged.mk n 3)

def importedDefaultSeqLeft (n : Nat) : ImportedTagged Nat :=
  @SeqLeft.seqLeft ImportedTagged
    (@Applicative.toSeqLeft ImportedTagged
      (@Monad.toApplicative ImportedTagged importedDefaultMonad)) Nat Nat
    (ImportedTagged.mk n 2) (fun unit => ImportedTagged.mk 99 3)

def importedDefaultSeqRight (n : Nat) : ImportedTagged Nat :=
  @SeqRight.seqRight ImportedTagged
    (@Applicative.toSeqRight ImportedTagged
      (@Monad.toApplicative ImportedTagged importedDefaultMonad)) Nat Nat
    (ImportedTagged.mk 99 2) (fun unit => ImportedTagged.mk n 3)

def importedDefaultPure (n : Nat) : ImportedTagged Nat :=
  @Pure.pure ImportedTagged
    (@Applicative.toPure ImportedTagged
      (@Monad.toApplicative ImportedTagged importedDefaultMonad)) Nat n

def importedSuppliedFunctor : Functor ImportedTagged :=
  { map := @importedTaggedMap, mapConst := @importedTaggedMapConst }

def importedLocalParentMonad [Functor ImportedTagged] : Monad ImportedTagged :=
  { pure := @importedTaggedPure, bind := @importedTaggedBind }

instance importedGlobalFunctor : Functor ImportedTagged :=
  { map := @importedTaggedMap, mapConst := @importedTaggedGlobalMapConst }

def importedGlobalParentMonad : Monad ImportedTagged :=
  { pure := @importedTaggedPure, bind := @importedTaggedBind }

def importedLocalParentMapConst (n : Nat) : ImportedTagged Nat :=
  @Functor.mapConst ImportedTagged
    (importedTaggedFunctor (@importedLocalParentMonad importedSuppliedFunctor)) Nat Nat
    n (ImportedTagged.mk 99 3)

def importedGlobalParentMapConst (n : Nat) : ImportedTagged Nat :=
  @Functor.mapConst ImportedTagged
    (importedTaggedFunctor importedGlobalParentMonad) Nat Nat
    n (ImportedTagged.mk 99 3)

theorem importedPureValue : importedPureRun 42 = 42 := by rfl
theorem importedBindValue : importedBindRun 40 = 42 := by rfl
theorem importedFunctorValue : importedFunctorRun 41 = 42 := by rfl
theorem importedMapConstValue : importedMapConstRun 42 = 42 := by rfl
theorem importedSeqValue : importedSeqRun 40 = 42 := by rfl
theorem importedSeqLeftValue : importedSeqLeftRun 42 = 42 := by rfl
theorem importedSeqRightValue : importedSeqRightRun 42 = 42 := by rfl
theorem importedApplicativeValue : importedApplicativeRun 42 = 42 := by rfl
theorem importedMonadPureValue : importedMonadPureRun 42 = 42 := by rfl
theorem importedMonadBindValue : importedMonadBindRun 40 = 42 := by rfl
theorem importedMonadPartsValue : importedMonadPartsRun 40 = 42 := by rfl
theorem importedMonadMixedValue : importedMonadMixedRun 40 = 42 := by rfl
theorem importedDefaultMapValue : (importedDefaultMap 40).value = 42 := by rfl
theorem importedDefaultMapStamp : (importedDefaultMap 40).stamp = 37 := by rfl
theorem importedReorderedMapStamp : (importedReorderedMap 40).stamp = 37 := by rfl
theorem importedOverrideMapValue : (importedOverrideMap 40).value = 42 := by rfl
theorem importedOverrideMapStamp : (importedOverrideMap 40).stamp = 99 := by rfl
theorem importedDefaultMapConstStamp : (importedDefaultMapConst 42).stamp = 37 := by rfl
theorem importedOverrideMapConstStamp : (importedOverrideMapConst 42).stamp = 99 := by rfl
theorem importedDefaultSeqValue : (importedDefaultSeq 40).value = 42 := by rfl
theorem importedDefaultSeqStamp : (importedDefaultSeq 40).stamp = 57 := by rfl
theorem importedOverrideSeqStamp : (importedOverrideSeq 40).stamp = 119 := by rfl
theorem importedDefaultSeqLeftStamp : (importedDefaultSeqLeft 42).stamp = 57 := by rfl
theorem importedDefaultSeqRightStamp : (importedDefaultSeqRight 42).stamp = 23 := by rfl
theorem importedDefaultPureStamp : (importedDefaultPure 42).stamp = 7 := by rfl
theorem importedLocalParentStamp : (importedLocalParentMapConst 42).stamp = 88 := by rfl
theorem importedGlobalParentStamp : (importedGlobalParentMapConst 42).stamp = 77 := by rfl
