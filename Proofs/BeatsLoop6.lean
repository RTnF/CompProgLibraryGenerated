import Proofs.BeatsLoop5
namespace Proofs.BeatsModel

def clsMax (a b : Nat) (x : Int) (nd : Nd) (lo hi : Nat) : Cls :=
  if b ≤ lo ∨ hi ≤ a ∨ x ≤ nd.mn then Cls.stop
  else if a ≤ lo ∧ hi ≤ b ∧ x < nd.smn then Cls.whole else Cls.down

def clsRange (a b : Nat) (nd : Nd) (lo hi : Nat) : Cls :=
  if b ≤ lo ∨ hi ≤ a then Cls.stop else if a ≤ lo ∧ hi ≤ b then Cls.whole else Cls.down

theorem chmaxBT_eq (a b : Nat) (x : Int) :
    ∀ (t : BT) (lo hi : Nat), chmaxBT a b x t lo hi = travBT (clsMax a b x) (capMinBT x) t lo hi
  | .leaf nd, lo, hi => by
    unfold chmaxBT travBT clsMax
    by_cases hc : b ≤ lo ∨ hi ≤ a ∨ x ≤ nd.mn
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
      have : nd.mn < x := by omega
      by_cases hc2 : a ≤ lo ∧ hi ≤ b ∧ x < nd.smn
      · simp only [if_pos hc2]; simp [capMinBT, BT.nd, this]
      · simp only [if_neg hc2]; simp [capMinBT, BT.nd, this]
  | .node nd tg l r, lo, hi => by
    have ih1 := chmaxBT_eq a b x (applyTag tg nd l) lo ((lo + hi) / 2)
    have ih2 := chmaxBT_eq a b x (applyTag tg nd r) ((lo + hi) / 2) hi
    unfold chmaxBT
    rw [ih1, ih2]
    rw [travBT]
    by_cases hc : b ≤ lo ∨ hi ≤ a ∨ x ≤ nd.mn
    · have : clsMax a b x nd lo hi = Cls.stop := by simp [clsMax, hc]
      rw [if_pos hc, this]
    · by_cases hc2 : a ≤ lo ∧ hi ≤ b ∧ x < nd.smn
      · have : clsMax a b x nd lo hi = Cls.whole := by simp [clsMax, hc, hc2]
        rw [if_neg hc, if_pos hc2, this]
      · have : clsMax a b x nd lo hi = Cls.down := by simp [clsMax, hc, hc2]
        rw [if_neg hc, if_neg hc2, this]
termination_by t _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)

theorem chmax_loop (a b : Nat) (x : Int) (hx : x < INF) (t : BT) (n : Nat) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) :
    ∃ H' E, Star (stepF (clsMax a b x) (fun _ => Cellh.capMinC x)) ⟨H, [⟨0, 0, n⟩], []⟩ ⟨H', [], E⟩ ∧
      Agree (upPhase E H') (chmaxBT a b x t 0 n) 0 := by
  rw [chmaxBT_eq]
  exact loop_whole (clsMax a b x) (fun _ => Cellh.capMinC x) (capMinBT x)
    (fun H t k lo hi _ h => agree_capMinBT H t k x h)
    (fun nd lo hi hhi h1 h2 h3 => by
      intro hd
      unfold clsMax at hd
      by_cases hc : b ≤ lo ∨ hi ≤ a ∨ x ≤ nd.mn
      · rw [if_pos hc] at hd; cases hd
      · rw [if_neg hc] at hd
        by_cases hc2 : a ≤ lo ∧ hi ≤ b ∧ x < nd.smn
        · rw [if_pos hc2] at hd; cases hd
        · exact hc2 ⟨by omega, by omega, by omega⟩)
    (fun t h => LeafOK_capMinBT x t h) t n H hag hsh hlf

theorem addRec_eq (a b : Nat) (x : Int) :
    ∀ (t : BT) (lo hi : Nat), addRec a b x t lo hi = travBT (clsRange a b) (addBT x) t lo hi
  | .leaf nd, lo, hi => by
    unfold addRec travBT clsRange
    by_cases hc : b ≤ lo ∨ hi ≤ a
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
      by_cases hc2 : a ≤ lo ∧ hi ≤ b
      · simp only [if_pos hc2]
      · simp only [if_neg hc2]
  | .node nd tg l r, lo, hi => by
    have ih1 := addRec_eq a b x (applyTag tg nd l) lo ((lo + hi) / 2)
    have ih2 := addRec_eq a b x (applyTag tg nd r) ((lo + hi) / 2) hi
    unfold addRec
    rw [ih1, ih2]
    rw [travBT]
    by_cases hc : b ≤ lo ∨ hi ≤ a
    · have : clsRange a b nd lo hi = Cls.stop := by simp [clsRange, hc]
      rw [if_pos hc, this]
    · by_cases hc2 : a ≤ lo ∧ hi ≤ b
      · have : clsRange a b nd lo hi = Cls.whole := by simp [clsRange, hc, hc2]
        rw [if_neg hc, if_pos hc2, this]
      · have : clsRange a b nd lo hi = Cls.down := by simp [clsRange, hc, hc2]
        rw [if_neg hc, if_neg hc2, this]
termination_by t _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)

theorem setRec_eq (a b : Nat) (x : Int) :
    ∀ (t : BT) (lo hi : Nat), setRec a b x t lo hi = travBT (clsRange a b) (setBT x) t lo hi
  | .leaf nd, lo, hi => by
    unfold setRec travBT clsRange
    by_cases hc : b ≤ lo ∨ hi ≤ a
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
      by_cases hc2 : a ≤ lo ∧ hi ≤ b
      · simp only [if_pos hc2]
      · simp only [if_neg hc2]
  | .node nd tg l r, lo, hi => by
    have ih1 := setRec_eq a b x (applyTag tg nd l) lo ((lo + hi) / 2)
    have ih2 := setRec_eq a b x (applyTag tg nd r) ((lo + hi) / 2) hi
    unfold setRec
    rw [ih1, ih2]
    rw [travBT]
    by_cases hc : b ≤ lo ∨ hi ≤ a
    · have : clsRange a b nd lo hi = Cls.stop := by simp [clsRange, hc]
      rw [if_pos hc, this]
    · by_cases hc2 : a ≤ lo ∧ hi ≤ b
      · have : clsRange a b nd lo hi = Cls.whole := by simp [clsRange, hc, hc2]
        rw [if_neg hc, if_pos hc2, this]
      · have : clsRange a b nd lo hi = Cls.down := by simp [clsRange, hc, hc2]
        rw [if_neg hc, if_neg hc2, this]
termination_by t _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)

theorem clsRange_leaf (a b : Nat) (nd : Nd) (lo hi : Nat) (hhi : hi = lo + 1) : clsRange a b nd lo hi ≠ Cls.down := by
  intro hd
  unfold clsRange at hd
  by_cases hc : b ≤ lo ∨ hi ≤ a
  · rw [if_pos hc] at hd; cases hd
  · rw [if_neg hc] at hd
    by_cases hc2 : a ≤ lo ∧ hi ≤ b
    · rw [if_pos hc2] at hd; cases hd
    · exact hc2 ⟨by omega, by omega⟩

theorem add_loop (a b : Nat) (x : Int) (t : BT) (n : Nat) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) :
    ∃ H' E, Star (stepF (clsRange a b) (fun _ => Cellh.addC x)) ⟨H, [⟨0, 0, n⟩], []⟩ ⟨H', [], E⟩ ∧
      Agree (upPhase E H') (addRec a b x t 0 n) 0 := by
  rw [addRec_eq]
  exact loop_whole (clsRange a b) (fun _ => Cellh.addC x) (addBT x)
    (fun H t k lo hi _ h => agree_addBT H t k x h)
    (fun nd lo hi hhi _ _ _ => clsRange_leaf a b nd lo hi hhi)
    (fun t h => LeafOK_addBT x t h) t n H hag hsh hlf

theorem set_loop (a b : Nat) (x : Int) (t : BT) (n : Nat) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) :
    ∃ H' E, Star (stepF (clsRange a b) (fun f c => Cellh.setC ((f.hi - f.lo : Nat) : Int) x c)) ⟨H, [⟨0, 0, n⟩], []⟩ ⟨H', [], E⟩ ∧
      Agree (upPhase E H') (setRec a b x t 0 n) 0 := by
  rw [setRec_eq]
  exact loop_whole (clsRange a b) (fun f c => Cellh.setC ((f.hi - f.lo : Nat) : Int) x c) (setBT x)
    (fun H t k lo hi hs h => by
      have := agree_setBT H t k x h
      have e : (t.size : Int) = ((hi - lo : Nat) : Int) := by rw [BT.size_skel, hs.size]
      rw [e] at this
      exact this)
    (fun nd lo hi hhi _ _ _ => clsRange_leaf a b nd lo hi hhi)
    (fun t h => LeafOK_setBT x t h) t n H hag hsh hlf

end Proofs.BeatsModel
