import Proofs.BeatsLoop7
namespace Proofs.BeatsModel

theorem calc_frame_min (a b : Nat) :
    ∀ (t : BT) (k lo hi : Nat) (H : Heap) (S : List Fr) (r : Int),
      r ≤ INF → Agree H t k → Shape lo hi t.skel → LeafOK t →
      ∃ H', Star (stepCalc (clsRange a b) (fun nd => nd.mn) min) ⟨H, ⟨k, lo, hi⟩ :: S, r⟩
          ⟨H', S, min r (calcMinBT a b t lo hi).2⟩ ∧
        (∀ j, ¬ descN k j → H' j = H j) ∧ Agree H' (calcMinBT a b t lo hi).1 k
  | .leaf nd, k, lo, hi, H, S, r, hr, hag, hsh, hlf => by
    have hhi : hi = lo + 1 := hsh
    have hroot := agree_root H _ k hag
    simp only [BT.nd] at hroot
    unfold calcMinBT
    by_cases hc : b ≤ lo ∨ hi ≤ a
    · rw [if_pos hc]
      refine ⟨H, Star.one ?_, fun _ _ => rfl, hag⟩
      have e : min r INF = r := Int.min_eq_left hr
      rw [e]
      simp [stepCalc, hroot, clsRange, hc]
    · rw [if_neg hc]
      refine ⟨H, Star.one ?_, fun _ _ => rfl, hag⟩
      have : clsRange a b nd lo hi = Cls.whole := by simp [clsRange, hc]; omega
      simp [stepCalc, hroot, this]
  | .node nd tg l r', k, lo, hi, H, S, r, hr, hag, hsh, hlf => by
    have hroot := agree_root H _ k hag
    simp only [BT.nd] at hroot
    unfold calcMinBT
    by_cases hc : b ≤ lo ∨ hi ≤ a
    · rw [if_pos hc]
      refine ⟨H, Star.one ?_, fun _ _ => rfl, hag⟩
      have e : min r INF = r := Int.min_eq_left hr
      rw [e]
      simp [stepCalc, hroot, clsRange, hc]
    · rw [if_neg hc]
      by_cases hc2 : a ≤ lo ∧ hi ≤ b
      · rw [if_pos hc2]
        refine ⟨H, Star.one ?_, fun _ _ => rfl, hag⟩
        have : clsRange a b nd lo hi = Cls.whole := by simp [clsRange, hc, hc2]
        simp [stepCalc, hroot, this]
      · rw [if_neg hc2]
        obtain ⟨hlo, hshl, hshr⟩ := hsh
        obtain ⟨hlfl, hlfr⟩ := hlf
        have hag2 := (agree_node H nd tg l r' k).mp hag
        have hlsize : ((lo + hi) / 2 - lo : Nat) = l.size := by rw [BT.size_skel, hshl.size]
        have hrsize : (hi - (lo + hi) / 2 : Nat) = r'.size := by rw [BT.size_skel, hshr.size]
        have hpush := agree_pushBT H nd tg l r' k hag
        rw [← hlsize, ← hrsize] at hpush
        simp only [pushBT] at hpush
        have hp2 := (agree_node _ nd noTag _ _ k).mp hpush
        have hcd : clsRange a b nd lo hi = Cls.down := by simp [clsRange, hc, hc2]
        have hstep : stepCalc (clsRange a b) (fun nd => nd.mn) min ⟨H, ⟨k, lo, hi⟩ :: S, r⟩ =
            ⟨pushH H k (((lo + hi) / 2 - lo : Nat) : Int) ((hi - (lo + hi) / 2 : Nat) : Int),
              ⟨2 * k + 1, lo, (lo + hi) / 2⟩ :: ⟨2 * k + 2, (lo + hi) / 2, hi⟩ :: S, r⟩ := by
          simp [stepCalc, hroot, hcd]
        obtain ⟨H0, hH0⟩ : ∃ H0, H0 = pushH H k (((lo + hi) / 2 - lo : Nat) : Int) ((hi - (lo + hi) / 2 : Nat) : Int) := ⟨_, rfl⟩
        rw [← hH0] at hstep hp2 hpush
        have hshl' : Shape lo ((lo + hi) / 2) (applyTag tg nd l).skel := by rw [skel_applyTag]; exact hshl
        have hshr' : Shape ((lo + hi) / 2) hi (applyTag tg nd r').skel := by rw [skel_applyTag]; exact hshr
        obtain ⟨H1, st1, hfr1, hag1⟩ := calc_frame_min a b (applyTag tg nd l) (2 * k + 1) lo ((lo + hi) / 2) H0
          (⟨2 * k + 2, (lo + hi) / 2, hi⟩ :: S) r hr hp2.2.1 hshl' (LeafOK_applyTag tg nd l hlfl)
        have hag_r : Agree H1 (applyTag tg nd r') (2 * k + 2) :=
          agree_of_eqOn hp2.2.2 (fun j hj => (hfr1 j (fun hd => descN_disjoint k j hd hj)).symm)
        obtain ⟨H2, st2, hfr2, hag2'⟩ := calc_frame_min a b (applyTag tg nd r') (2 * k + 2) ((lo + hi) / 2) hi H1 S
          (min r (calcMinBT a b (applyTag tg nd l) lo ((lo + hi) / 2)).2) (Int.le_trans (Int.min_le_left _ _) hr)
          hag_r hshr' (LeafOK_applyTag tg nd r' hlfr)
        refine ⟨H2, ?_, ?_, ?_⟩
        · have := Star.trans (Star.one hstep.symm) (Star.trans st1 st2)
          have e : min (min r (calcMinBT a b (applyTag tg nd l) lo ((lo + hi) / 2)).2)
              (calcMinBT a b (applyTag tg nd r') ((lo + hi) / 2) hi).2 =
              min r (min (calcMinBT a b (applyTag tg nd l) lo ((lo + hi) / 2)).2
                (calcMinBT a b (applyTag tg nd r') ((lo + hi) / 2) hi).2) := by omega
          rw [e] at this
          exact this
        · intro j hj
          have hjl : ¬ descN (2 * k + 1) j := fun hd => hj (descN_child k j hd)
          have hjr : ¬ descN (2 * k + 2) j := fun hd => hj (descN_child2 k j hd)
          have hjk : j ≠ k := fun e => hj (e ▸ descN_self _)
          have hj1 : j ≠ 2 * k + 1 := fun e => hj (descN_child k j (e ▸ descN_self _))
          have hj2 : j ≠ 2 * k + 2 := fun e => hj (descN_child2 k j (e ▸ descN_self _))
          rw [hfr2 j hjr, hfr1 j hjl, hH0]
          unfold pushH
          rw [Heap.set_ne _ _ _ _ hjk, Heap.set_ne _ _ _ _ hj2, Heap.set_ne _ _ _ _ hj1]
        · have hlnot : ∀ j, descN (2 * k + 1) j → ¬ descN (2 * k + 2) j := fun j h1 h2 => descN_disjoint k j h1 h2
          have hagL : Agree H2 (calcMinBT a b (applyTag tg nd l) lo ((lo + hi) / 2)).1 (2 * k + 1) :=
            agree_of_eqOn hag1 (fun j hj => by rw [hfr2 j (hlnot j hj)])
          have hkk : H2 k = (nd, noTag) := by
            have n1 : ¬ descN (2 * k + 1) k := fun hd => by have := descN_ge _ _ hd; omega
            have n2 : ¬ descN (2 * k + 2) k := fun hd => by have := descN_ge _ _ hd; omega
            rw [hfr2 k n2, hfr1 k n1]
            exact hp2.1
          exact (agree_node _ nd noTag _ _ k).mpr ⟨hkk, hagL, hag2'⟩
termination_by t _ _ _ _ _ _ _ _ _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)

end Proofs.BeatsModel
