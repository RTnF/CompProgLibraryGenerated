import Proofs.BeatsLoop2
namespace Proofs.BeatsModel

structure Fr where
  k : Nat
  lo : Nat
  hi : Nat

structure St where
  H : Heap
  stk : List Fr
  E : List Nat

/-- One iteration of the explicit-stack loop (`pop`, then skip / act on the whole node / push and descend). -/
def stepF (cls : Nd → Nat → Nat → Cls) (actC : Fr → Cellh → Cellh) : St → St
  | ⟨H, [], E⟩ => ⟨H, [], E⟩
  | ⟨H, f :: S, E⟩ =>
    match cls (H f.k).1 f.lo f.hi with
    | Cls.stop => ⟨H, S, E⟩
    | Cls.whole => ⟨H.set f.k (actC f (H f.k)), S, E⟩
    | Cls.down =>
      ⟨pushH H f.k (((f.lo + f.hi) / 2 - f.lo : Nat) : Int) ((f.hi - (f.lo + f.hi) / 2 : Nat) : Int),
        ⟨2 * f.k + 1, f.lo, (f.lo + f.hi) / 2⟩ :: ⟨2 * f.k + 2, (f.lo + f.hi) / 2, f.hi⟩ :: S, f.k :: E⟩

inductive Star {α : Type} (f : α → α) : α → α → Prop
  | refl (a : α) : Star f a a
  | step (a b c : α) : b = f a → Star f b c → Star f a c

theorem Star.trans {α : Type} {f : α → α} {a b c : α} (h1 : Star f a b) (h2 : Star f b c) : Star f a c := by
  induction h1 with
  | refl => exact h2
  | step a b' c' hb _ ih => exact Star.step _ _ _ hb (ih h2)

theorem Star.one {α : Type} {f : α → α} {a b : α} (h : b = f a) : Star f a b := Star.step a b b h (Star.refl b)

def LeafOK : BT → Prop
  | .leaf nd => nd.smx = -INF ∧ nd.smn = INF ∧ nd.mn = nd.mx
  | .node _ _ l r => LeafOK l ∧ LeafOK r


theorem LeafOK_setBT (v : Int) (t : BT) (h : LeafOK t) : LeafOK (setBT v t) := by
  cases t with
  | leaf nd => exact ⟨rfl, rfl, rfl⟩
  | node nd tg l r => exact h

theorem LeafOK_addBT (x : Int) (t : BT) (h : LeafOK t) : LeafOK (addBT x t) := by
  cases t with
  | leaf nd =>
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨?_, ?_, ?_⟩
    · show (if nd.smx = -INF then nd.smx else nd.smx + x) = -INF
      rw [if_pos h1]; exact h1
    · show (if nd.smn = INF then nd.smn else nd.smn + x) = INF
      rw [if_pos h2]; exact h2
    · show nd.mn + x = nd.mx + x
      rw [h3]
  | node nd tg l r => exact h

theorem LeafOK_capMaxBT (x : Int) (t : BT) (h : LeafOK t) : LeafOK (capMaxBT x t) := by
  cases t with
  | leaf nd =>
    obtain ⟨h1, h2, h3⟩ := h
    unfold capMaxBT
    by_cases hc : x < nd.mx
    · simp only [BT.nd, hc, if_true]
      refine ⟨?_, ?_, ?_⟩
      · show (updMax nd x).smx = -INF
        rw [updMax_smx]; exact h1
      · show (updMax nd x).smn = INF
        rw [updMax_smn]
        by_cases hm : nd.mx = nd.mn
        · rw [if_pos hm]; exact h2
        · exact absurd h3.symm hm
      · show (updMax nd x).mn = (updMax nd x).mx
        rw [updMax_mn, updMax_mx, if_pos h3.symm]
    · simp only [BT.nd, hc, if_false]
      exact ⟨h1, h2, h3⟩
  | node nd tg l r =>
    unfold capMaxBT
    split <;> exact h

theorem updMin_smx (nd : Nd) (x : Int) :
    (updMin nd x).smx = if nd.mx = nd.mn then nd.smx else if nd.mn = nd.smx then x else nd.smx := by
  unfold updMin negNd
  simp only [updMax_smn]
  by_cases h : nd.mx = nd.mn
  · have : -nd.mn = -nd.mx := by omega
    simp [h, this]
  · have : ¬ (-nd.mn = -nd.mx) := by omega
    by_cases h2 : nd.mn = nd.smx
    · have : -nd.mn = -nd.smx := by omega
      have h4 : ¬ nd.smx = nd.mx := by omega
      have h5 : ¬ nd.mx = nd.smx := by omega
      simp [h, h2, this, h4, h5]
    · have : ¬ (-nd.mn = -nd.smx) := by omega
      simp [h, h2, this]

theorem LeafOK_capMinBT (x : Int) (t : BT) (h : LeafOK t) : LeafOK (capMinBT x t) := by
  cases t with
  | leaf nd =>
    obtain ⟨h1, h2, h3⟩ := h
    unfold capMinBT
    by_cases hc : nd.mn < x
    · simp only [BT.nd, hc, if_true]
      refine ⟨?_, ?_, ?_⟩
      · show (updMin nd x).smx = -INF
        rw [updMin_smx, if_pos h3.symm]; exact h1
      · show (updMin nd x).smn = INF
        rw [updMin_smn]; exact h2
      · show (updMin nd x).mn = (updMin nd x).mx
        rw [updMin_mn, updMin_mx, if_pos h3.symm]
    · simp only [BT.nd, hc, if_false]
      exact ⟨h1, h2, h3⟩
  | node nd tg l r =>
    unfold capMinBT
    split <;> exact h


theorem LeafOK_applyTag (tg : Tag) (nd : Nd) (t : BT) (h : LeafOK t) : LeafOK (applyTag tg nd t) := by
  unfold applyTag
  cases tg.lval with
  | some v => exact LeafOK_setBT v t h
  | none => exact LeafOK_capMinBT _ _ (LeafOK_capMaxBT _ _ (LeafOK_addBT _ _ h))

end Proofs.BeatsModel
