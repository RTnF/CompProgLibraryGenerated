import Proofs.BeatsLoop3
namespace Proofs.BeatsModel

theorem down_frame (cls : Nd → Nat → Nat → Cls) (actC : Fr → Cellh → Cellh) (actBT : BT → BT)
    (hact : ∀ (H : Heap) (t : BT) (k lo hi : Nat), Shape lo hi t.skel → Agree H t k → Agree (H.set k (actC ⟨k, lo, hi⟩ (H k))) (actBT t) k)
    (hleafcls : ∀ nd lo hi, hi = lo + 1 → nd.smx = -INF → nd.smn = INF → nd.mn = nd.mx → cls nd lo hi ≠ Cls.down)
    (hactLeaf : ∀ t, LeafOK t → LeafOK (actBT t)) :
    ∀ (t : BT) (k lo hi : Nat) (H : Heap) (S : List Fr) (E : List Nat),
      Agree H t k → Shape lo hi t.skel → LeafOK t →
      ∃ H' Enew, Star (stepF cls actC) ⟨H, ⟨k, lo, hi⟩ :: S, E⟩ ⟨H', S, Enew ++ E⟩ ∧
        (∀ e ∈ Enew, descN k e) ∧ (∀ j, ¬ descN k j → H' j = H j) ∧
        Agree (upPhase Enew H') (travBT cls actBT t lo hi) k
  | .leaf nd, k, lo, hi, H, S, E, hag, hsh, hlf => by
    have hhi : hi = lo + 1 := hsh
    have hroot := agree_root H _ k hag
    simp only [BT.nd] at hroot
    unfold travBT
    cases hc : cls nd lo hi with
    | stop =>
      refine ⟨H, [], Star.one ?_, by simp, fun _ _ => rfl, ?_⟩
      · simp [stepF, hroot, hc]
      · simpa [upPhase] using hag
    | whole =>
      refine ⟨H.set k (actC ⟨k, lo, hi⟩ (H k)), [], Star.one ?_, by simp, ?_, ?_⟩
      · simp [stepF, hroot, hc]
      · intro j hj
        have : j ≠ k := fun e => hj (e ▸ descN_self _)
        exact Heap.set_ne _ _ _ _ this
      · simpa [upPhase] using hact H _ k lo hi hsh hag
    | down =>
      exact absurd hc (hleafcls nd lo hi hhi hlf.1 hlf.2.1 hlf.2.2)
  | .node nd tg l r, k, lo, hi, H, S, E, hag, hsh, hlf => by
    have hroot := agree_root H _ k hag
    simp only [BT.nd] at hroot
    unfold travBT
    cases hc : cls nd lo hi with
    | stop =>
      refine ⟨H, [], Star.one ?_, by simp, fun _ _ => rfl, ?_⟩
      · simp [stepF, hroot, hc]
      · simpa [upPhase] using hag
    | whole =>
      refine ⟨H.set k (actC ⟨k, lo, hi⟩ (H k)), [], Star.one ?_, by simp, ?_, ?_⟩
      · simp [stepF, hroot, hc]
      · intro j hj
        have : j ≠ k := fun e => hj (e ▸ descN_self _)
        exact Heap.set_ne _ _ _ _ this
      · simpa [upPhase] using hact H _ k lo hi hsh hag
    | down =>
      obtain ⟨hlo, hshl, hshr⟩ := hsh
      obtain ⟨hlfl, hlfr⟩ := hlf
      have hag2 := (agree_node H nd tg l r k).mp hag
      have hlsize : ((lo + hi) / 2 - lo : Nat) = l.size := by
        rw [BT.size_skel, hshl.size]
      have hrsize : (hi - (lo + hi) / 2 : Nat) = r.size := by
        rw [BT.size_skel, hshr.size]
      have hpush := agree_pushBT H nd tg l r k hag
      rw [← hlsize, ← hrsize] at hpush
      simp only [pushBT] at hpush
      have hp2 := (agree_node _ nd noTag _ _ k).mp hpush
      -- one step: push and descend
      have hstep : stepF cls actC ⟨H, ⟨k, lo, hi⟩ :: S, E⟩ =
          ⟨pushH H k (((lo + hi) / 2 - lo : Nat) : Int) ((hi - (lo + hi) / 2 : Nat) : Int),
            ⟨2 * k + 1, lo, (lo + hi) / 2⟩ :: ⟨2 * k + 2, (lo + hi) / 2, hi⟩ :: S, k :: E⟩ := by
        simp [stepF, hroot, hc]
      obtain ⟨H0, hH0⟩ : ∃ H0, H0 = pushH H k (((lo + hi) / 2 - lo : Nat) : Int) ((hi - (lo + hi) / 2 : Nat) : Int) := ⟨_, rfl⟩
      rw [← hH0] at hstep hp2 hpush
      have hshl' : Shape lo ((lo + hi) / 2) (applyTag tg nd l).skel := by rw [skel_applyTag]; exact hshl
      have hshr' : Shape ((lo + hi) / 2) hi (applyTag tg nd r).skel := by rw [skel_applyTag]; exact hshr
      obtain ⟨H1, E1, st1, hE1, hfr1, hag1⟩ :=
        down_frame cls actC actBT hact hleafcls hactLeaf (applyTag tg nd l) (2 * k + 1) lo ((lo + hi) / 2) H0
          (⟨2 * k + 2, (lo + hi) / 2, hi⟩ :: S) (k :: E) hp2.2.1 hshl' (LeafOK_applyTag tg nd l hlfl)
      have hag_r : Agree H1 (applyTag tg nd r) (2 * k + 2) :=
        agree_of_eqOn hp2.2.2 (fun j hj => (hfr1 j (fun hd => descN_disjoint k j hd hj)).symm)
      obtain ⟨H2, E2, st2, hE2, hfr2, hag2'⟩ :=
        down_frame cls actC actBT hact hleafcls hactLeaf (applyTag tg nd r) (2 * k + 2) ((lo + hi) / 2) hi H1
          S (E1 ++ k :: E) hag_r hshr' (LeafOK_applyTag tg nd r hlfr)
      refine ⟨H2, E2 ++ E1 ++ [k], ?_, ?_, ?_, ?_⟩
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
      · have hE1' : ∀ e ∈ E1, descN (2 * k + 1) e := hE1
        have hE2' : ∀ e ∈ E2, descN (2 * k + 2) e := hE2
        have hup : upPhase (E2 ++ E1 ++ [k]) H2 = updateH (upPhase E1 (upPhase E2 H2)) k := by
          rw [upPhase_append, upPhase_append]; rfl
        rw [hup]
        have hlnot : ∀ j, descN (2 * k + 1) j → ¬ descN (2 * k + 2) j := fun j h1 h2 => descN_disjoint k j h1 h2
        have hrnot : ∀ j, descN (2 * k + 2) j → ¬ descN (2 * k + 1) j := fun j h2 h1 => descN_disjoint k j h1 h2
        have hG2 : EqOn (2 * k + 1) H1 (upPhase E2 H2) := by
          intro j hj
          rw [upPhase_frame E2 (2 * k + 2) hE2' H2 j (hlnot j hj), hfr2 j (hlnot j hj)]
        have hagL : Agree (upPhase E1 (upPhase E2 H2)) (travBT cls actBT (applyTag tg nd l) lo ((lo + hi) / 2)) (2 * k + 1) :=
          agree_of_eqOn hag1 (upPhase_local E1 (2 * k + 1) hE1' _ _ hG2)
        have hagR : Agree (upPhase E1 (upPhase E2 H2)) (travBT cls actBT (applyTag tg nd r) ((lo + hi) / 2) hi) (2 * k + 2) :=
          agree_of_eqOn hag2' (fun j hj => (upPhase_frame E1 (2 * k + 1) hE1' _ j (hrnot j hj)).symm)
        have hkk : upPhase E1 (upPhase E2 H2) k = (nd, noTag) := by
          have n1 : ¬ descN (2 * k + 1) k := fun hd => by have := descN_ge _ _ hd; omega
          have n2 : ¬ descN (2 * k + 2) k := fun hd => by have := descN_ge _ _ hd; omega
          rw [upPhase_frame E1 (2 * k + 1) hE1' _ k n1, upPhase_frame E2 (2 * k + 2) hE2' _ k n2, hfr2 k n2, hfr1 k n1]
          exact hp2.1
        exact agree_updateBT _ nd _ _ k ((agree_node _ nd noTag _ _ k).mpr ⟨hkk, hagL, hagR⟩)
termination_by t _ _ _ _ _ _ _ _ _ => t.height
decreasing_by
  all_goals simp_wf
  all_goals (rw [height_applyTag]; simp [BT.height]; omega)

end Proofs.BeatsModel
