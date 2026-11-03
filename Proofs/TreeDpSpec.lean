import Proofs.TreeDpAlg

namespace Proofs.TreeDpSpec
open Proofs.TreeDpAlg

/-- The arcs leaving `v`. -/
def arcs (head : List Nat) (v : Nat) : List Nat := List.range' (head.getD v 0) (head.getD (v + 1) 0 - head.getD v 0)

/-- The head of the arc `p`. -/
def tgt (target : List Nat) (p : Nat) : Nat := target.getD p 0

/-- The neighbours of `v`, in the order of the arcs. -/
def nbs (head target : List Nat) (v : Nat) : List Nat := (arcs head v).map (tgt target)

/-- Folding `Option`-valued steps; `none` is absorbing. -/
def optFold (M : CM) (g : Nat → Option Int) (xs : List Nat) (acc : Option Int) : Option Int :=
  xs.foldl (fun a x => a.bind fun a' => (g x).bind fun b => some (M.op a' b)) acc

theorem optFold_none (M : CM) (g : Nat → Option Int) (xs : List Nat) : optFold M g xs none = none := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [optFold] using ih

theorem optFold_cons (M : CM) (g : Nat → Option Int) (x : Nat) (xs : List Nat) (acc : Option Int) :
    optFold M g (x :: xs) acc = optFold M g xs (acc.bind fun a' => (g x).bind fun b => some (M.op a' b)) := rfl

/-- The DP value of the component of `w` entered from `u` (fuel `f`): `sum_up` of the product of the values of the
neighbours of `w` other than `u`. -/
def Ef (M : CM) (head target : List Nat) : Nat → Nat → Nat → Option Int
  | 0, _, _ => none
  | f + 1, u, w =>
    (optFold M (Ef M head target f w) ((nbs head target w).filter fun x => decide (x ≠ u)) (some M.e)).map M.su

theorem optFold_mono (M : CM) (g g' : Nat → Option Int) (xs : List Nat) (hg : ∀ x ∈ xs, ∀ y, g x = some y → g' x = some y) :
    ∀ (acc : Option Int) (r : Int), optFold M g xs acc = some r → optFold M g' xs acc = some r := by
  induction xs with
  | nil => intro acc r h; exact h
  | cons x xs ih =>
    intro acc r h
    rw [optFold_cons] at h ⊢
    cases hacc : acc with
    | none => rw [hacc] at h; simp at h; rw [optFold_none] at h; exact absurd h (by simp)
    | some a =>
      rw [hacc] at h
      cases hgx : g x with
      | none => simp [hgx] at h; rw [optFold_none] at h; exact absurd h (by simp)
      | some b =>
        simp only [hgx, Option.bind_some] at h
        have hg' := hg x (List.mem_cons_self ..) b hgx
        simp only [hg', Option.bind_some]
        exact ih (fun y hy => hg y (List.mem_cons_of_mem _ hy)) _ r h

theorem Ef_mono (M : CM) (head target : List Nat) : ∀ (f u w : Nat) (r : Int),
    Ef M head target f u w = some r → Ef M head target (f + 1) u w = some r := by
  intro f
  induction f with
  | zero => intro u w r h; simp [Ef] at h
  | succ f ih =>
    intro u w r h
    simp only [Ef, Option.map_eq_some_iff] at h ⊢
    obtain ⟨r', hr', hr⟩ := h
    exact ⟨r', optFold_mono M _ _ _ (fun x _ y hy => ih w x y hy) _ _ hr', hr⟩

theorem Ef_le (M : CM) (head target : List Nat) (f f' u w : Nat) (r : Int) (hf : f ≤ f')
    (h : Ef M head target f u w = some r) : Ef M head target f' u w = some r := by
  induction hf with
  | refl => exact h
  | step _ ih => exact Ef_mono M head target _ u w r ih

/-- If every element has a derivation, the folded value is derivable (with a common fuel). -/
theorem optFold_of_vals (M : CM) (head target : List Nat) (w : Nat) (val : Nat → Int) :
    ∀ (xs : List Nat), (∀ x ∈ xs, ∃ f, Ef M head target f w x = some (val x)) →
      ∃ f, ∀ (a : Int), optFold M (Ef M head target f w) xs (some a) = some (xs.foldl (fun acc x => M.op acc (val x)) a)
  | [], _ => ⟨0, fun a => rfl⟩
  | x :: xs, h => by
    obtain ⟨f1, hf1⟩ := h x (List.mem_cons_self ..)
    obtain ⟨f2, hf2⟩ := optFold_of_vals M head target w val xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    refine ⟨max f1 f2, fun a => ?_⟩
    have e1 : Ef M head target (max f1 f2) w x = some (val x) := Ef_le M head target f1 _ w x _ (Nat.le_max_left _ _) hf1
    rw [optFold_cons]
    simp only [Option.bind_some, e1]
    simp only [List.foldl_cons]
    have := hf2 (M.op a (val x))
    have key : optFold M (Ef M head target (max f1 f2) w) xs (some (M.op a (val x))) =
        some (xs.foldl (fun acc x => M.op acc (val x)) (M.op a (val x))) := by
      have hm : ∀ z ∈ xs, ∀ y, Ef M head target f2 w z = some y → Ef M head target (max f1 f2) w z = some y :=
        fun z _ y hy => Ef_le M head target f2 _ w z y (Nat.le_max_right _ _) hy
      exact optFold_mono M _ _ xs hm _ _ this
    exact key

theorem ef_succ_of_vals (M : CM) (head target : List Nat) (u w : Nat) (val : Nat → Int)
    (h : ∀ x ∈ (nbs head target w).filter (fun x => decide (x ≠ u)), ∃ f, Ef M head target f w x = some (val x)) :
    ∃ f, Ef M head target (f + 1) u w =
      some (M.su (fold M (((nbs head target w).filter (fun x => decide (x ≠ u))).map val))) := by
  obtain ⟨f, hf⟩ := optFold_of_vals M head target w val _ h
  refine ⟨f, ?_⟩
  simp only [Ef, hf, Option.map_some]
  congr 2
  simp [fold, List.foldl_map]

end Proofs.TreeDpSpec
