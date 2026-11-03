import Proofs.BeatsHeap4
namespace Proofs.BeatsModel

/-- `update(k)` on the heap: recompute the summary of node `k` from its two children (the tag is left alone). -/
def updateH (H : Heap) (k : Nat) : Heap := H.set k (mergeNd (H (2 * k + 1)).1 (H (2 * k + 2)).1, (H k).2)

/-- The up phase: apply `update` to the entered nodes, most recently entered first. -/
def upPhase (E : List Nat) (H : Heap) : Heap := E.foldl updateH H

theorem upPhase_cons (e : Nat) (E : List Nat) (H : Heap) : upPhase (e :: E) H = upPhase E (updateH H e) := rfl

theorem upPhase_append (E1 E2 : List Nat) (H : Heap) : upPhase (E1 ++ E2) H = upPhase E2 (upPhase E1 H) := by
  unfold upPhase; rw [List.foldl_append]

/-- Two heaps agree on the subtree rooted at `c`. -/
def EqOn (c : Nat) (H G : Heap) : Prop := ∀ j, descN c j → H j = G j

theorem agree_of_eqOn {H G : Heap} {t : BT} {k : Nat} (h : Agree H t k) (e : EqOn k H G) : Agree G t k := by
  intro j nd otg hj
  have := h j nd otg hj
  rw [← e j (sub2_desc t k j _ hj)]
  exact this

theorem eqOn_refl (c : Nat) (H : Heap) : EqOn c H H := fun _ _ => rfl
theorem eqOn_symm {c : Nat} {H G : Heap} (h : EqOn c H G) : EqOn c G H := fun j hj => (h j hj).symm
theorem eqOn_trans {c : Nat} {H G K : Heap} (h1 : EqOn c H G) (h2 : EqOn c G K) : EqOn c H K :=
  fun j hj => (h1 j hj).trans (h2 j hj)
theorem eqOn_mono {c d : Nat} (hcd : ∀ j, descN d j → descN c j) {H G : Heap} (h : EqOn c H G) : EqOn d H G :=
  fun j hj => h j (hcd j hj)

theorem descN_trans {a b j : Nat} (hab : descN a b) (hbj : descN b j) : descN a j := by
  induction hbj with
  | self => exact hab
  | step j h1 h2 ih => exact descN.step j (Nat.lt_of_le_of_lt (descN_ge _ _ hab) h1) ih

/-- `update` at a node in the region only writes inside the region and only reads inside it. -/
theorem updateH_frame (H : Heap) (e c j : Nat) (he : descN c e) (hj : ¬ descN c j) : updateH H e j = H j := by
  unfold updateH
  have : j ≠ e := fun h => hj (h ▸ he)
  rw [Heap.set_ne _ _ _ _ this]

theorem upPhase_frame (E : List Nat) (c : Nat) (hE : ∀ e ∈ E, descN c e) :
    ∀ (H : Heap) (j : Nat), ¬ descN c j → upPhase E H j = H j := by
  induction E with
  | nil => intro H j _; rfl
  | cons e E ih =>
    intro H j hj
    rw [upPhase_cons, ih (fun x hx => hE x (List.mem_cons_of_mem _ hx)) _ _ hj]
    exact updateH_frame H e c j (hE e List.mem_cons_self) hj

theorem updateH_local (H G : Heap) (e c : Nat) (he : descN c e) (h : EqOn c H G) : EqOn c (updateH H e) (updateH G e) := by
  intro j hj
  unfold updateH
  by_cases hje : j = e
  · subst hje
    rw [Heap.set_eq, Heap.set_eq]
    have h1 := h (2 * j + 1) (descN_trans he (descN_child j _ (by exact descN.self) |> fun _ => descN.step _ (by omega) (by
      have : (2 * j + 1 - 1) / 2 = j := by omega
      rw [this]; exact descN.self)))
    have h2 := h (2 * j + 2) (descN_trans he (descN.step _ (by omega) (by
      have : (2 * j + 2 - 1) / 2 = j := by omega
      rw [this]; exact descN.self)))
    have h0 := h j hj
    rw [h1, h2, h0]
  · rw [Heap.set_ne _ _ _ _ hje, Heap.set_ne _ _ _ _ hje]
    exact h j hj

theorem upPhase_local (E : List Nat) (c : Nat) (hE : ∀ e ∈ E, descN c e) :
    ∀ (H G : Heap), EqOn c H G → EqOn c (upPhase E H) (upPhase E G) := by
  induction E with
  | nil => intro H G h; exact h
  | cons e E ih =>
    intro H G h
    rw [upPhase_cons, upPhase_cons]
    exact ih (fun x hx => hE x (List.mem_cons_of_mem _ hx)) _ _ (updateH_local H G e c (hE e List.mem_cons_self) h)

end Proofs.BeatsModel
