import Proofs.BeatsHeap3
namespace Proofs.BeatsModel

theorem Heap.set_set (H : Heap) (i : Nat) (c1 c2 : Cellh) : (H.set i c1).set i c2 = H.set i c2 := by
  funext j; by_cases h : j = i <;> simp [Heap.set, h]

def Cellh.applyTagC (tg : Tag) (nd : Nd) (len : Int) (c : Cellh) : Cellh :=
  match tg.lval with
  | some v => Cellh.setC len v c
  | none => Cellh.capMinC nd.mn (Cellh.capMaxC nd.mx (Cellh.addC tg.ladd c))

theorem agree_applyTag (H : Heap) (t : BT) (k : Nat) (tg : Tag) (nd : Nd) (h : Agree H t k) :
    Agree (H.set k (Cellh.applyTagC tg nd (t.size : Int) (H k))) (applyTag tg nd t) k := by
  unfold applyTag Cellh.applyTagC
  cases hl : tg.lval with
  | some v => exact agree_setBT H t k v h
  | none =>
    have h1 := agree_addBT H t k tg.ladd h
    have h2 := agree_capMaxBT _ _ k nd.mx h1
    have h3 := agree_capMinBT _ _ k nd.mn h2
    rw [Heap.set_eq, Heap.set_set] at h3
    rw [Heap.set_eq, Heap.set_set] at h3
    exact h3

/-- `push(k)` on the heap, with the lengths of the two children. -/
def pushH (H : Heap) (k : Nat) (lenL lenR : Int) : Heap :=
  let nd := (H k).1
  let tg := (H k).2
  let H1 := H.set (2 * k + 1) (Cellh.applyTagC tg nd lenL (H (2 * k + 1)))
  let H2 := H1.set (2 * k + 2) (Cellh.applyTagC tg nd lenR (H (2 * k + 2)))
  H2.set k (nd, noTag)

theorem not_desc_left (k i : Nat) (h : i = k ∨ i = 2 * k + 2) : ¬ descN (2 * k + 1) i := by
  intro hd
  rcases h with h | h
  · have := descN_ge _ _ hd; omega
  · subst h; exact descN_disjoint k _ hd descN.self

theorem not_desc_right (k i : Nat) (h : i = k ∨ i = 2 * k + 1) : ¬ descN (2 * k + 2) i := by
  intro hd
  have := descN_ge _ _ hd
  rcases h with h | h <;> omega

theorem agree_pushBT (H : Heap) (nd : Nd) (tg : Tag) (l r : BT) (k : Nat) (h : Agree H (.node nd tg l r) k) :
    Agree (pushH H k (l.size : Int) (r.size : Int)) (pushBT (.node nd tg l r)) k := by
  rw [agree_node] at h
  obtain ⟨h1, h2, h3⟩ := h
  simp only [pushBT]
  rw [agree_node]
  have hk : (H k).1 = nd := by rw [h1]
  have hk2 : (H k).2 = tg := by rw [h1]
  unfold pushH
  simp only [hk, hk2]
  refine ⟨Heap.set_eq _ _ _, ?_, ?_⟩
  · have a1 := agree_applyTag H l (2 * k + 1) tg nd h2
    have a2 := agree_frame _ _ _ a1 (2 * k + 2) (Cellh.applyTagC tg nd (r.size : Int) (H (2 * k + 2)))
      (not_desc_left k _ (Or.inr rfl))
    exact agree_frame _ _ _ a2 k _ (not_desc_left k _ (Or.inl rfl))
  · have b0 := agree_frame H r _ h3 (2 * k + 1) (Cellh.applyTagC tg nd (l.size : Int) (H (2 * k + 1)))
      (not_desc_right k _ (Or.inr rfl))
    have b1 := agree_applyTag (H.set (2 * k + 1) (Cellh.applyTagC tg nd (l.size : Int) (H (2 * k + 1)))) r (2 * k + 2) tg nd b0
    rw [Heap.set_ne _ (2 * k + 1) (2 * k + 2) _ (by omega)] at b1
    exact agree_frame _ _ _ b1 k _ (not_desc_right k _ (Or.inl rfl))

end Proofs.BeatsModel
