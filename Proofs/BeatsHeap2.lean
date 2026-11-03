import Proofs.BeatsHeap
namespace Proofs.BeatsModel

/-- A heap cell: the node summary and its pending tag. -/
abbrev Cellh := Nd × Tag
abbrev Heap := Nat → Cellh

/-- The cells of `t` placed at heap index `k`; a leaf's tag is not constrained. -/
def sub2 : BT → Nat → Nat → Option (Nd × Option Tag)
  | .leaf nd, k, j => if j = k then some (nd, none) else none
  | .node nd tg l r, k, j =>
    if j = k then some (nd, some tg)
    else match sub2 l (2 * k + 1) j with
      | some v => some v
      | none => sub2 r (2 * k + 2) j

theorem sub2_desc : ∀ (t : BT) (k j : Nat) (v : Nd × Option Tag), sub2 t k j = some v → descN k j
  | .leaf nd, k, j, v, h => by
    unfold sub2 at h
    split at h
    · rename_i e; subst e; exact descN_self _
    · simp at h
  | .node nd tg l r, k, j, v, h => by
    unfold sub2 at h
    split at h
    · rename_i e; subst e; exact descN_self _
    · split at h
      · rename_i w hw; exact descN_child k j (sub2_desc l _ j w hw)
      · exact descN_child2 k j (sub2_desc r _ j v h)

def Agree (H : Heap) (t : BT) (k : Nat) : Prop :=
  ∀ j nd otg, sub2 t k j = some (nd, otg) → (H j).1 = nd ∧ ∀ tg, otg = some tg → (H j).2 = tg

theorem agree_node (H : Heap) (nd : Nd) (tg : Tag) (l r : BT) (k : Nat) :
    Agree H (.node nd tg l r) k ↔ H k = (nd, tg) ∧ Agree H l (2 * k + 1) ∧ Agree H r (2 * k + 2) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · have := h k nd (some tg) (by simp [sub2])
      exact Prod.ext this.1 (this.2 tg rfl)
    · intro j nd' otg hj
      have hd := sub2_desc l _ j _ hj
      have hne : j ≠ k := by have := descN_ge _ _ hd; omega
      apply h j nd' otg
      simp [sub2, hne, hj]
    · intro j nd' otg hj
      have hd := sub2_desc r _ j _ hj
      have hne : j ≠ k := by have := descN_ge _ _ hd; omega
      have hnl : sub2 l (2 * k + 1) j = none := by
        cases hl : sub2 l (2 * k + 1) j with
        | none => rfl
        | some w => exact (descN_disjoint k j (sub2_desc l _ j _ hl) hd).elim
      apply h j nd' otg
      simp [sub2, hne, hnl, hj]
  · rintro ⟨h1, h2, h3⟩ j nd' otg hj
    unfold sub2 at hj
    by_cases hjk : j = k
    · rw [if_pos hjk] at hj
      simp only [Option.some.injEq, Prod.mk.injEq] at hj
      obtain ⟨e1, e2⟩ := hj
      subst hjk
      refine ⟨by rw [h1, e1], ?_⟩
      intro tg' h'; rw [h1]; rw [← e2] at h'; simp at h'; rw [h']
    · rw [if_neg hjk] at hj
      split at hj
      · rename_i w hw
        simp only [Option.some.injEq] at hj
        subst hj
        exact h2 j _ _ hw
      · exact h3 j nd' otg hj

/-- Write one heap cell. -/
def Heap.set (H : Heap) (i : Nat) (c : Cellh) : Heap := fun j => if j = i then c else H j

theorem Heap.set_ne (H : Heap) (i j : Nat) (c : Cellh) (h : j ≠ i) : H.set i c j = H j := by simp [Heap.set, h]
theorem Heap.set_eq (H : Heap) (i : Nat) (c : Cellh) : H.set i c i = c := by simp [Heap.set]

theorem agree_frame (H : Heap) (t : BT) (k : Nat) (h : Agree H t k) (i : Nat) (c : Cellh) (hi : ¬ descN k i) :
    Agree (H.set i c) t k := by
  intro j nd otg hj
  have hd := sub2_desc t k j _ hj
  have hne : j ≠ i := fun e => hi (e ▸ hd)
  rw [Heap.set_ne H i j c hne]
  exact h j nd otg hj

end Proofs.BeatsModel
