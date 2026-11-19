import Proofs.Cpp.Gen.MonoidLazy

open Proofs.Cpp Proofs.Cpp.Gen

namespace MonoidLazyDraft

structure CustomScalar where
  value : Int
structure LeftProduct where
  value : Int
structure RightProduct where
  value : Int

@[instance_reducible] def countTimes : MulResult Int CustomScalar where
  Value := LeftProduct
  mul n v := ⟨n * v.value + 1⟩

@[instance_reducible] def timesCount : MulResult CustomScalar Int where
  Value := RightProduct
  mul v n := ⟨n * v.value - 1⟩

@[instance_reducible] def addProduct :
    AddResult CustomScalar (@MulResult.Value Int CustomScalar countTimes) where
  Value := CustomScalar
  add x p := ⟨x.value + p.value⟩

@[instance_reducible] def assignProduct :
    AssignResult CustomScalar (@MulResult.Value CustomScalar Int timesCount) where
  assign x p := ⟨x.value + p.value⟩

example :
    (@cp.RangeAddRangeSum_RangeAdd.apply CustomScalar countTimes addProduct ⟨id⟩
      ⟨⟨5⟩⟩ ⟨⟨8⟩, 3⟩).run 0 = some ((⟨⟨24⟩, 3⟩, ⟨⟨5⟩⟩), 2) := rfl

example :
    (@cp.RangeSetRangeSum_RangeSet.apply CustomScalar timesCount assignProduct
      ⟨⟨5⟩, false⟩ ⟨⟨8⟩, 3⟩).run 0 = some ((⟨⟨22⟩, 3⟩, ⟨⟨5⟩, false⟩), 1) := rfl

end MonoidLazyDraft

namespace MonoidLazyDraft

structure CustomInput where
  stored : Int

structure CustomField where
  value : Int

structure CustomSum where
  value : Int

@[instance_reducible] def customRead : ReadField "x" CustomInput where
  Value := CustomField
  read x := ⟨x.stored⟩

@[instance_reducible] def customAdd : AddResult (@ReadField.Value "x" CustomInput customRead) Int where
  Value := CustomSum
  add x v := ⟨2 * x.value + v⟩

@[instance_reducible] def customCast : Conv (@AddResult.Value _ Int customAdd) CustomInput where
  conv x := ⟨3 * x.value⟩

example :
    (@cp.RangeAddRangeMaxMin_RangeAdd.apply Int CustomInput customRead customAdd customCast ⟨7⟩ (⟨5⟩ : CustomInput)).run 0 =
      some ((⟨51⟩, ⟨7⟩), 1) := rfl

/-- The exercised inputs here are nonnegative and fit in UInt64. -/
@[instance_reducible] def arithmeticConditional : ConditionalResult Int Float where
  Value := Float
  left x := (UInt64.ofInt x).toFloat
  right := id

@[instance_reducible] def arithmeticCast : Conv (@ConditionalResult.Value _ _ arithmeticConditional) Int where
  conv x := x.toUInt64.toNat

def exampleOutputs : IO Unit := do
  match (@cp.RangeAddRangeMaxMin_RangeAdd.apply Int CustomInput customRead customAdd customCast ⟨7⟩ (⟨5⟩ : CustomInput)).run 0 with
  | some ((x, _), _) => IO.println x.stored
  | none => throw (IO.userError "dependent addition did not complete")
  for (x, v, noop) in ([(9007199254740993, 0.0, true), (3, 7.5, false)] : List (Int × Float × Bool)) do
    match (@cp.RangeSetRangeMaxMin_RangeSet.apply Float Int arithmeticConditional arithmeticCast ⟨v, noop⟩ x).run 0 with
    | some ((value, _), _) => IO.println value
    | none => throw (IO.userError "dependent conditional did not complete")

end MonoidLazyDraft

open Proofs.Cpp.Gen MonoidLazyDraft

def main : IO Unit := do
  exampleOutputs
  match (@cp.RangeAddRangeSum_RangeAdd.apply CustomScalar countTimes addProduct ⟨id⟩
      ⟨⟨5⟩⟩ ⟨⟨8⟩, 3⟩).run 0 with
  | some ((row, _), _) => IO.println row.x.value
  | none => throw (IO.userError "mixed addition failed")
  match (@cp.RangeSetRangeSum_RangeSet.apply CustomScalar timesCount assignProduct
      ⟨⟨5⟩, false⟩ ⟨⟨8⟩, 3⟩).run 0 with
  | some ((row, _), _) => IO.println row.x.value
  | none => throw (IO.userError "mixed assignment failed")
