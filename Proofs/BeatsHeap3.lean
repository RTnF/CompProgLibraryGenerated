import Proofs.BeatsHeap2
namespace Proofs.BeatsModel

def Cellh.addC (x : Int) (c : Cellh) : Cellh := (addNd c.1 x, tagAdd c.2 x)
def Cellh.setC (len : Int) (x : Int) (c : Cellh) : Cellh := (setNd len x, tagSet x)
def Cellh.capMaxC (x : Int) (c : Cellh) : Cellh := if x < c.1.mx then (updMax c.1 x, tagMax c.2 x) else c
def Cellh.capMinC (x : Int) (c : Cellh) : Cellh := if c.1.mn < x then (updMin c.1 x, tagMin c.2 x) else c

theorem agree_leaf (H : Heap) (nd : Nd) (k : Nat) : Agree H (.leaf nd) k ↔ (H k).1 = nd := by
  constructor
  · intro h
    exact (h k nd none (by simp [sub2])).1
  · intro h j nd' otg hj
    unfold sub2 at hj
    split at hj
    · rename_i e
      simp only [Option.some.injEq, Prod.mk.injEq] at hj
      obtain ⟨e1, e2⟩ := hj
      subst e; subst e1
      exact ⟨h, by intro tg h'; rw [← e2] at h'; simp at h'⟩
    · simp at hj

/-- Updating a single cell at the root of a subtree corresponds to the operation on the tree. -/
theorem agree_setBT (H : Heap) (t : BT) (k : Nat) (v : Int) (h : Agree H t k) :
    Agree (H.set k (Cellh.setC (t.size : Int) v (H k))) (setBT v t) k := by
  cases t with
  | leaf nd =>
    simp only [setBT]
    rw [agree_leaf]; simp [Heap.set_eq, Cellh.setC, BT.size]
  | node nd tg l r =>
    rw [agree_node] at h
    simp only [setBT]
    rw [agree_node]
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · rw [Heap.set_eq]; simp [Cellh.setC, BT.size, h1]
    · exact agree_frame H l _ h2 k _ (fun hd => by have := descN_ge _ _ hd; omega)
    · exact agree_frame H r _ h3 k _ (fun hd => by have := descN_ge _ _ hd; omega)

theorem agree_addBT (H : Heap) (t : BT) (k : Nat) (x : Int) (h : Agree H t k) :
    Agree (H.set k (Cellh.addC x (H k))) (addBT x t) k := by
  cases t with
  | leaf nd =>
    rw [agree_leaf] at h
    simp only [addBT]
    rw [agree_leaf]; simp [Heap.set_eq, Cellh.addC, h]
  | node nd tg l r =>
    rw [agree_node] at h
    simp only [addBT]
    rw [agree_node]
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · rw [Heap.set_eq]; simp [Cellh.addC, h1]
    · exact agree_frame H l _ h2 k _ (fun hd => by have := descN_ge _ _ hd; omega)
    · exact agree_frame H r _ h3 k _ (fun hd => by have := descN_ge _ _ hd; omega)

theorem agree_capMaxBT (H : Heap) (t : BT) (k : Nat) (x : Int) (h : Agree H t k) :
    Agree (H.set k (Cellh.capMaxC x (H k))) (capMaxBT x t) k := by
  cases t with
  | leaf nd =>
    rw [agree_leaf] at h
    unfold capMaxBT Cellh.capMaxC
    by_cases hc : x < nd.mx
    · have hc' : x < (H k).1.mx := by rw [h]; exact hc
      simp only [BT.nd, hc, hc', if_true]
      rw [agree_leaf]; simp [Heap.set_eq, h]
    · have hc' : ¬ x < (H k).1.mx := by rw [h]; exact hc
      simp only [BT.nd, hc, hc', if_false]
      rw [agree_leaf]; simp [Heap.set_eq, h]
  | node nd tg l r =>
    rw [agree_node] at h
    obtain ⟨h1, h2, h3⟩ := h
    unfold capMaxBT Cellh.capMaxC
    by_cases hc : x < nd.mx
    · have hc' : x < (H k).1.mx := by rw [h1]; exact hc
      simp only [BT.nd, hc, hc', if_true]
      rw [agree_node]
      refine ⟨?_, ?_, ?_⟩
      · rw [Heap.set_eq, h1]
      · exact agree_frame H l _ h2 k _ (fun hd => by have := descN_ge _ _ hd; omega)
      · exact agree_frame H r _ h3 k _ (fun hd => by have := descN_ge _ _ hd; omega)
    · have hc' : ¬ x < (H k).1.mx := by rw [h1]; exact hc
      simp only [BT.nd, hc, hc', if_false]
      rw [agree_node]
      refine ⟨?_, ?_, ?_⟩
      · rw [Heap.set_eq, h1]
      · exact agree_frame H l _ h2 k _ (fun hd => by have := descN_ge _ _ hd; omega)
      · exact agree_frame H r _ h3 k _ (fun hd => by have := descN_ge _ _ hd; omega)

theorem agree_capMinBT (H : Heap) (t : BT) (k : Nat) (x : Int) (h : Agree H t k) :
    Agree (H.set k (Cellh.capMinC x (H k))) (capMinBT x t) k := by
  cases t with
  | leaf nd =>
    rw [agree_leaf] at h
    unfold capMinBT Cellh.capMinC
    by_cases hc : nd.mn < x
    · have hc' : (H k).1.mn < x := by rw [h]; exact hc
      simp only [BT.nd, hc, hc', if_true]
      rw [agree_leaf]; simp [Heap.set_eq, h]
    · have hc' : ¬ (H k).1.mn < x := by rw [h]; exact hc
      simp only [BT.nd, hc, hc', if_false]
      rw [agree_leaf]; simp [Heap.set_eq, h]
  | node nd tg l r =>
    rw [agree_node] at h
    obtain ⟨h1, h2, h3⟩ := h
    unfold capMinBT Cellh.capMinC
    by_cases hc : nd.mn < x
    · have hc' : (H k).1.mn < x := by rw [h1]; exact hc
      simp only [BT.nd, hc, hc', if_true]
      rw [agree_node]
      refine ⟨?_, ?_, ?_⟩
      · rw [Heap.set_eq, h1]
      · exact agree_frame H l _ h2 k _ (fun hd => by have := descN_ge _ _ hd; omega)
      · exact agree_frame H r _ h3 k _ (fun hd => by have := descN_ge _ _ hd; omega)
    · have hc' : ¬ (H k).1.mn < x := by rw [h1]; exact hc
      simp only [BT.nd, hc, hc', if_false]
      rw [agree_node]
      refine ⟨?_, ?_, ?_⟩
      · rw [Heap.set_eq, h1]
      · exact agree_frame H l _ h2 k _ (fun hd => by have := descN_ge _ _ hd; omega)
      · exact agree_frame H r _ h3 k _ (fun hd => by have := descN_ge _ _ hd; omega)

end Proofs.BeatsModel
