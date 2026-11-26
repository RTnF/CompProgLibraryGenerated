import Proofs.Cpp.FlowResidualView

open Proofs.Cpp Proofs.Cpp.FlowResidualSlots Proofs.Cpp.FlowResidualView
open Proofs.FlowResidual

namespace Proofs.Cpp.FlowPairLayout

variable {E : Type} [Inhabited E] [Field "cap" E Int] [Field "to" E Int]
  [Field "cost" E Int] [Field "rev" E Int]

abbrev ArcOf (adj : Array (Array E)) := {a : Slot // InBounds adj a}

/-- Conditions on mutable row contents for all real residual slots. -/
structure PairedRows (adj : Array (Array E)) : Prop where
  to_nonnegative : ∀ a, InBounds adj a → 0 ≤ dest (readSlot adj a)
  rev_nonnegative : ∀ a, InBounds adj a → 0 ≤ revIdx (readSlot adj a)
  rev_valid : ∀ a, InBounds adj a → InBounds adj (reverseSlot adj a)
  rev_distinct : ∀ a, InBounds adj a → reverseSlot adj a ≠ a
  rev_symmetric : ∀ a, InBounds adj a → reverseSlot adj (reverseSlot adj a) = a
  cost_antisym : ∀ a, InBounds adj a → price (readSlot adj (reverseSlot adj a)) = -price (readSlot adj a)

omit [Field "cap" E Int] in
def PairedRows.network {adj : Array (Array E)} (pair : PairedRows adj) : Network (ArcOf adj) Nat where
  tail := fun a => a.val.1
  head := fun a => (dest (readSlot adj a.val)).toNat
  reverse := fun a => ⟨reverseSlot adj a.val, pair.rev_valid a.val a.property⟩
  reverse_reverse := fun a => Subtype.ext (pair.rev_symmetric a.val a.property)
  reverse_ne := fun a h => pair.rev_distinct a.val a.property (congrArg Subtype.val h)
  reverse_tail := fun _ => rfl
  reverse_head := fun a => congrArg Prod.fst (pair.rev_symmetric a.val a.property)
  cost := fun a => price (readSlot adj a.val)
  reverse_cost := fun a => pair.cost_antisym a.val a.property

omit [Field "cap" E Int] in
theorem PairedRows.represents {adj : Array (Array E)} (pair : PairedRows adj) :
    Represents pair.network adj Subtype.val := by
  refine ⟨Subtype.val_injective, fun a => a.property, fun _ => rfl, ?_, fun _ => rfl, fun _ => rfl⟩
  intro a
  exact (Int.toNat_of_nonneg (pair.to_nonnegative a.val a.property)).symm

variable [WriteField "cap" E Int]

theorem PairedRows.adjust {adj : Array (Array E)} (pair : PairedRows adj) (laws : CapLaws (E := E))
    (a : ArcOf adj) (d : Int) : PairedRows (FlowResidualSlots.adjust adj a.val d) := by
  let out := FlowResidualSlots.adjust adj a.val d
  have bound (b : Slot) : InBounds out b ↔ InBounds adj b :=
    adjust_bounds laws adj a.val d a.property (pair.rev_valid _ a.property) b
  have fields (b : Slot) := adjust_metadata laws adj a.val d a.property (pair.rev_valid _ a.property)
    (pair.rev_distinct _ a.property) b
  have rev (b : Slot) : reverseSlot out b = reverseSlot adj b := by
    unfold reverseSlot
    rw [(fields b).1, (fields b).2.1]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b hb
    exact (fields b).1 ▸ pair.to_nonnegative b ((bound b).mp hb)
  · intro b hb
    exact (fields b).2.1 ▸ pair.rev_nonnegative b ((bound b).mp hb)
  · intro b hb
    change InBounds out (reverseSlot out b)
    rw [rev, bound]
    exact pair.rev_valid b ((bound b).mp hb)
  · intro b hb
    change reverseSlot out b ≠ b
    rw [rev]
    exact pair.rev_distinct b ((bound b).mp hb)
  · intro b hb
    change reverseSlot out (reverseSlot out b) = b
    rw [rev, rev]
    exact pair.rev_symmetric b ((bound b).mp hb)
  · intro b hb
    change price (readSlot out (reverseSlot out b)) = -price (readSlot out b)
    rw [rev, (fields _).2.2, (fields b).2.2]
    exact pair.cost_antisym b ((bound b).mp hb)

end Proofs.Cpp.FlowPairLayout
