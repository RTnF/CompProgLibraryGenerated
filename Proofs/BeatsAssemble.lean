import Proofs.BeatsLoop8
namespace Proofs.BeatsModel

/-- The end of the proof of `down_frame`: the two children have been processed, the node is updated on the way up. -/
theorem down_assemble (cls : Nd → Nat → Nat → Cls) (actC : Fr → Cellh → Cellh) (actBT : BT → BT)
    (nd : Nd) (tg : Tag) (l r : BT) (k lo hi : Nat) (H H0 H1 H2 : Heap) (S : List Fr) (E E1 E2 : List Nat)
    (hH0 : H0 = pushH H k (((lo + hi) / 2 - lo : Nat) : Int) ((hi - (lo + hi) / 2 : Nat) : Int))
    (hstep : stepF cls actC ⟨H, ⟨k, lo, hi⟩ :: S, E⟩ =
      ⟨H0, ⟨2 * k + 1, lo, (lo + hi) / 2⟩ :: ⟨2 * k + 2, (lo + hi) / 2, hi⟩ :: S, k :: E⟩)
    (hp2 : Agree H0 (.node nd noTag (applyTag tg nd l) (applyTag tg nd r)) k)
    (st1 : Star (stepF cls actC) ⟨H0, ⟨2 * k + 1, lo, (lo + hi) / 2⟩ :: ⟨2 * k + 2, (lo + hi) / 2, hi⟩ :: S, k :: E⟩
      ⟨H1, ⟨2 * k + 2, (lo + hi) / 2, hi⟩ :: S, E1 ++ k :: E⟩)
    (hE1 : ∀ e ∈ E1, descN (2 * k + 1) e) (hfr1 : ∀ j, ¬ descN (2 * k + 1) j → H1 j = H0 j)
    (hag1 : Agree (upPhase E1 H1) (travBT cls actBT (applyTag tg nd l) lo ((lo + hi) / 2)) (2 * k + 1))
    (st2 : Star (stepF cls actC) ⟨H1, ⟨2 * k + 2, (lo + hi) / 2, hi⟩ :: S, E1 ++ k :: E⟩ ⟨H2, S, E2 ++ (E1 ++ k :: E)⟩)
    (hE2 : ∀ e ∈ E2, descN (2 * k + 2) e) (hfr2 : ∀ j, ¬ descN (2 * k + 2) j → H2 j = H1 j)
    (hag2' : Agree (upPhase E2 H2) (travBT cls actBT (applyTag tg nd r) ((lo + hi) / 2) hi) (2 * k + 2))
    (hc : cls nd lo hi = Cls.down) (hroot : (H k).1 = nd) :
    Star (stepF cls actC) ⟨H, ⟨k, lo, hi⟩ :: S, E⟩ ⟨H2, S, (E2 ++ E1 ++ [k]) ++ E⟩ ∧
    (∀ e ∈ E2 ++ E1 ++ [k], descN k e) ∧ (∀ j, ¬ descN k j → H2 j = H j) ∧
    Agree (upPhase (E2 ++ E1 ++ [k]) H2) (travBT cls actBT (.node nd tg l r) lo hi) k := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := Star.trans (Star.one hstep.symm) (Star.trans st1 st2)
    simpa [List.append_assoc] using this
  · intro e he
    simp only [List.mem_append, List.mem_singleton] at he
    rcases he with (he | he) | he
    · exact descN_child2 k e (hE2 e he)
    · exact descN_child k e (hE1 e he)
    · subst he; exact descN_self _
  · intro j hj
    have hjl : ¬ descN (2 * k + 1) j := fun hd => hj (descN_child k j hd)
    have hjr : ¬ descN (2 * k + 2) j := fun hd => hj (descN_child2 k j hd)
    rw [hfr2 j hjr, hfr1 j hjl]
    have hjk : j ≠ k := fun e => hj (e ▸ descN_self _)
    have hj1 : j ≠ 2 * k + 1 := fun e => hj (descN_child k j (e ▸ descN_self _))
    have hj2 : j ≠ 2 * k + 2 := fun e => hj (descN_child2 k j (e ▸ descN_self _))
    rw [hH0]
    unfold pushH
    rw [Heap.set_ne _ _ _ _ hjk, Heap.set_ne _ _ _ _ hj2, Heap.set_ne _ _ _ _ hj1]
  · have hup : upPhase (E2 ++ E1 ++ [k]) H2 = updateH (upPhase E1 (upPhase E2 H2)) k := by
      rw [upPhase_append, upPhase_append]; rfl
    rw [hup]
    have hlnot : ∀ j, descN (2 * k + 1) j → ¬ descN (2 * k + 2) j := fun j h1 h2 => descN_disjoint k j h1 h2
    have hrnot : ∀ j, descN (2 * k + 2) j → ¬ descN (2 * k + 1) j := fun j h2 h1 => descN_disjoint k j h1 h2
    have hG2 : EqOn (2 * k + 1) H1 (upPhase E2 H2) := by
      intro j hj
      rw [upPhase_frame E2 (2 * k + 2) hE2 H2 j (hlnot j hj), hfr2 j (hlnot j hj)]
    have hagL : Agree (upPhase E1 (upPhase E2 H2)) (travBT cls actBT (applyTag tg nd l) lo ((lo + hi) / 2)) (2 * k + 1) :=
      agree_of_eqOn hag1 (upPhase_local E1 (2 * k + 1) hE1 _ _ hG2)
    have hagR : Agree (upPhase E1 (upPhase E2 H2)) (travBT cls actBT (applyTag tg nd r) ((lo + hi) / 2) hi) (2 * k + 2) :=
      agree_of_eqOn hag2' (fun j hj => (upPhase_frame E1 (2 * k + 1) hE1 _ j (hrnot j hj)).symm)
    have hkk : upPhase E1 (upPhase E2 H2) k = (nd, noTag) := by
      have n1 : ¬ descN (2 * k + 1) k := fun hd => by have := descN_ge _ _ hd; omega
      have n2 : ¬ descN (2 * k + 2) k := fun hd => by have := descN_ge _ _ hd; omega
      rw [upPhase_frame E1 (2 * k + 1) hE1 _ k n1, upPhase_frame E2 (2 * k + 2) hE2 _ k n2, hfr2 k n2, hfr1 k n1]
      exact (agree_node _ nd noTag _ _ k |>.mp hp2).1
    unfold travBT
    rw [hc]
    exact agree_updateBT _ nd _ _ k ((agree_node _ nd noTag _ _ k).mpr ⟨hkk, hagL, hagR⟩)

theorem chminSafe_down (a b : Nat) (x : Int) (nd : Nd) (tg : Tag) (l r : BT) (lo hi : Nat)
    (hc : clsMin a b x nd lo hi = Cls.down) (h : chminSafe a b x (.node nd tg l r) lo hi) :
    PushSafe (.node nd tg l r) ∧ chminSafe a b x (applyTag tg nd l) lo ((lo + hi) / 2) ∧
      chminSafe a b x (applyTag tg nd r) ((lo + hi) / 2) hi := by
  unfold clsMin at hc
  by_cases h1 : b ≤ lo ∨ hi ≤ a ∨ nd.mx ≤ x
  · rw [if_pos h1] at hc; cases hc
  · rw [if_neg h1] at hc
    by_cases h2 : a ≤ lo ∧ hi ≤ b ∧ nd.smx < x
    · rw [if_pos h2] at hc; cases hc
    · unfold chminSafe at h
      rw [if_neg h1, if_neg h2] at h
      exact h

end Proofs.BeatsModel
