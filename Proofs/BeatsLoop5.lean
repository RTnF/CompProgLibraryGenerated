import Proofs.BeatsLoop4
namespace Proofs.BeatsModel

/-- The whole `chmin` loop: from the root, run the down phase, then the up phase. -/
theorem loop_whole (cls : Nd → Nat → Nat → Cls) (actC : Fr → Cellh → Cellh) (actBT : BT → BT)
    (hact : ∀ (H : Heap) (t : BT) (k lo hi : Nat), Shape lo hi t.skel → Agree H t k → Agree (H.set k (actC ⟨k, lo, hi⟩ (H k))) (actBT t) k)
    (hleafcls : ∀ nd lo hi, hi = lo + 1 → nd.smx = -INF → nd.smn = INF → nd.mn = nd.mx → cls nd lo hi ≠ Cls.down)
    (hactLeaf : ∀ t, LeafOK t → LeafOK (actBT t)) (t : BT) (n : Nat) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) :
    ∃ H' Enew, Star (stepF cls actC) ⟨H, [⟨0, 0, n⟩], []⟩ ⟨H', [], Enew⟩ ∧
      Agree (upPhase Enew H') (travBT cls actBT t 0 n) 0 := by
  obtain ⟨H', Enew, st, _, _, hag'⟩ := down_frame cls actC actBT hact hleafcls hactLeaf t 0 0 n H [] [] hag hsh hlf
  exact ⟨H', Enew, by simpa using st, hag'⟩

def clsMin (a b : Nat) (x : Int) (nd : Nd) (lo hi : Nat) : Cls :=
  if b ≤ lo ∨ hi ≤ a ∨ nd.mx ≤ x then Cls.stop
  else if a ≤ lo ∧ hi ≤ b ∧ nd.smx < x then Cls.whole else Cls.down

theorem chminBT_eq (a b : Nat) (x : Int) :
    ∀ (t : BT) (lo hi : Nat), chminBT a b x t lo hi = travBT (clsMin a b x) (capMaxBT x) t lo hi
  | .leaf nd, lo, hi => by
    unfold chminBT travBT clsMin
    by_cases hc : b ≤ lo ∨ hi ≤ a ∨ nd.mx ≤ x
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
      by_cases hc2 : a ≤ lo ∧ hi ≤ b ∧ nd.smx < x
      · simp only [if_pos hc2]
        have : x < nd.mx := by omega
        simp [capMaxBT, BT.nd, this]
      · simp only [if_neg hc2]
        have : x < nd.mx := by omega
        simp [capMaxBT, BT.nd, this]
  | .node nd tg l r, lo, hi => by
    have ih1 := chminBT_eq a b x (applyTag tg nd l) lo ((lo + hi) / 2)
    have ih2 := chminBT_eq a b x (applyTag tg nd r) ((lo + hi) / 2) hi
    unfold chminBT
    rw [ih1, ih2]
    rw [travBT]
    by_cases hc : b ≤ lo ∨ hi ≤ a ∨ nd.mx ≤ x
    · have : clsMin a b x nd lo hi = Cls.stop := by simp [clsMin, hc]
      rw [if_pos hc, this]
    · by_cases hc2 : a ≤ lo ∧ hi ≤ b ∧ nd.smx < x
      · have : clsMin a b x nd lo hi = Cls.whole := by simp [clsMin, hc, hc2]
        rw [if_neg hc, if_pos hc2, this]
      · have : clsMin a b x nd lo hi = Cls.down := by simp [clsMin, hc, hc2]
        rw [if_neg hc, if_neg hc2, this]
termination_by t _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)


theorem chmin_loop (a b : Nat) (x : Int) (hx : -INF < x) (t : BT) (n : Nat) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) :
    ∃ H' E, Star (stepF (clsMin a b x) (fun _ => Cellh.capMaxC x)) ⟨H, [⟨0, 0, n⟩], []⟩ ⟨H', [], E⟩ ∧
      Agree (upPhase E H') (chminBT a b x t 0 n) 0 := by
  rw [chminBT_eq]
  exact loop_whole (clsMin a b x) (fun _ => Cellh.capMaxC x) (capMaxBT x)
    (fun H t k lo hi _ h => agree_capMaxBT H t k x h)
    (fun nd lo hi hhi h1 h2 h3 => by
      intro hd
      unfold clsMin at hd
      by_cases hc : b ≤ lo ∨ hi ≤ a ∨ nd.mx ≤ x
      · rw [if_pos hc] at hd; cases hd
      · rw [if_neg hc] at hd
        by_cases hc2 : a ≤ lo ∧ hi ≤ b ∧ nd.smx < x
        · rw [if_pos hc2] at hd; cases hd
        · exact hc2 ⟨by omega, by omega, by omega⟩)
    (fun t h => LeafOK_capMaxBT x t h) t n H hag hsh hlf

end Proofs.BeatsModel
