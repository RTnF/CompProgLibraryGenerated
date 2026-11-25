import Proofs.Cpp.Prelude

/-! # Parent chains (`ListGraph::shortest_path`)

`Chain P cur L`: following the parents `P` from `cur` gives the vertices `L` (from `cur`) until `-1`. -/

namespace Proofs.ParentChain

open Proofs.Cpp

/-- The parent chain `cur, P[cur], P[P[cur]], …` up to (not including) `-1`. -/
inductive Chain (P : Array Int) : Int → List Int → Prop
  | stop : Chain P (-1) []
  | step (cur : Int) (L : List Int) : cur ≠ -1 → Chain P (Cpp.get P cur) L → Chain P cur (cur :: L)

theorem chain_det {P : Array Int} {c : Int} {L L' : List Int} (h : Chain P c L) (h' : Chain P c L') : L = L' := by
  induction h generalizing L' with
  | stop => cases h' with
    | stop => rfl
    | step _ _ hne _ => exact absurd rfl hne
  | step cur L hne _ ih => cases h' with
    | stop => exact absurd rfl hne
    | step _ L2 _ h2 => rw [ih h2]

theorem chain_cons {P : Array Int} {c : Int} {L : List Int} (h : Chain P c L) (hc : c ≠ -1) :
    ∃ L', L = c :: L' ∧ Chain P (Cpp.get P c) L' := by
  cases h with
  | stop => exact absurd rfl hc
  | step _ L' _ h' => exact ⟨L', rfl, h'⟩

open Classical in
/-- The length of the chain from `c` (0 when there is none). -/
noncomputable def clen (P : Array Int) (c : Int) : Nat :=
  if h : ∃ L, Chain P c L then (Classical.choose h).length else 0

theorem clen_of {P : Array Int} {c : Int} {L : List Int} (h : Chain P c L) : clen P c = L.length := by
  have hex : ∃ L, Chain P c L := ⟨L, h⟩
  unfold clen
  rw [dite_cond_eq_true (eq_true hex), chain_det (Classical.choose_spec hex) h]

end Proofs.ParentChain
