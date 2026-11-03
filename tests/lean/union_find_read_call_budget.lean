namespace UfReadCallBudgetExamples
open Proofs.UfReadPrepareBudget UfReadCallExamples
open Proofs.CppMoveContext

example (w : Bool) := Proofs.UfReadPrepareBudget.size_call (input w) object (receiver w) data rfl id forest
  (by decide +kernel) weights 1 (by decide +kernel) (.variable Proofs.DoublingNested.i32 3) rfl rfl rfl
  (readable w) (unique w) (covered w) (allocations w) rfl (by change 0 ≤ _; omega) (contexts w)
example (w : Bool) := Proofs.UfReadPrepareBudget.same_call (input w) object (receiver w) data rfl id forest
  (by decide +kernel) 1 3 (by decide +kernel) (by decide +kernel)
  (.variable Proofs.DoublingNested.i32 3) (.variable Proofs.DoublingNested.i32 4) (twoArgs w)
  (readable w) (unique w) (covered w) (allocations w) rfl (by change 0 ≤ _; omega) (contexts w)
example (w : Bool) := Proofs.UfReadPrepareBudget.counter_call (input w) object (receiver w)
  (readable w) (unique w) (covered w) (allocations w) rfl (by change 0 ≤ _; omega) (contexts w)

example (s : Context) (n history heapPeak : Nat) :
    scalarBudget {s with peak := history,objects := {s.objects with heap := {s.objects.heap with peak := heapPeak}}} n =
      scalarBudget s n := rfl
example (s : Context) (n : Nat) :
    scalarBudget s n ≤ max s.scalars.peak (scalarLive s+n+s.slots.length+49) := scalar_bound s n
end UfReadCallBudgetExamples
