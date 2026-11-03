import Proofs.BeatsSlotRun
import Proofs.BeatsWideCtorLoop
import Proofs.BeatsIndexHeight
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.BellmanFordExec
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
theorem inner_children_lt_four_n (n e : Nat) (inner : isInnerAt n e) :
    2*e+2 < 4*n := by
  have hinner : (rngOf n e).1+1 < (rngOf n e).2 := inner
  have bound := rngOf_index n e (by omega)
  have mul := Nat.mul_le_mul_left (e+2) (by omega : 1 ≤ (rngOf n e).2-(rngOf n e).1-1)
  simp only [Nat.mul_one] at mul
  omega

abbrev WideCtorCmd (o : Nat) : Command :=
  .sequence (.primitive (.declare s64 true (.literal s64 4000000000000000000)))
   (.sequence (.primitive (.declare i32 true (.cast i32 (.size (.integer s64) (.local 15)))))
    (.sequence (.primitive (.write (.local 10) i32 (.cast u64 (.literal i32 0)) (.variable i32 (o + 1))))
     (.sequence (.primitive (.declare i32 true (.literal i32 0)))
      (.sequence (.primitive (.declare i32 true (.literal i32 0)))
       (.sequence (WideCtLoop1 o) (.sequence (CtULoop o) Sk))))))

theorem ct_exec_wide {S : Nat} (mv : MV) (hnv : mv.nv = 16) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64)
    (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (hty15 : mv.ty 15 = s64) (P : List Cell)
    (a : List Int) (n L : Nat) (hn : 1 ≤ n) (hL8 : 8 * n + 8 ≤ L) (hRange : 4*n < M31) (hAlen : a.length = n) (hAr : InRange a)
    (b0 : BS) (hV0 : ValidOK b0) (hLens0 : CapS S b0 L) (hlo0 : L ≤ b0.lo.length) (hhi0 : L ≤ b0.hi.length)
    (h0 : ∀ j, b0.mxv.getD j 0 = 0) (h1 : ∀ j, b0.smx.getD j 0 = 0) (h2 : ∀ j, b0.mxc.getD j 0 = 0) (h3 : ∀ j, b0.mnv.getD j 0 = 0)
    (h4 : ∀ j, b0.smn.getD j 0 = 0) (h5 : ∀ j, b0.mnc.getD j 0 = 0) (h6 : ∀ j, b0.len.getD j 0 = 0) (h7 : ∀ j, b0.ladd.getD j 0 = 0)
    (h8 : ∀ j, j < b0.lval.length → b0.lval.getD j 0 = INF) (h9 : ∀ j, b0.lo.getD j 0 = 0) (h10 : ∀ j, b0.hi.getD j 0 = 0) :
    ∃ (bf : BS) (Hf : Heap) (F : Nat) (r : PRM),
      pexecM mv F (WideCtorCmd (mv.nv + pre.length)) (gS P (pre ++ [])) (VVA a b0) = some r ∧ r.ret = none ∧
      r.ps = gS P (pre ++ CtCells INF n 0 (4 * n)) ∧ r.vv = VVA a bf ∧
      HRel INF bf Hf ∧ Agree Hf (buildBT a 0 n) 0 ∧ ValidOK bf ∧ CapS S bf L ∧ L ≤ bf.lo.length ∧ L ≤ bf.hi.length ∧
      LenOK bf (buildBT a 0 n) 0 0 n ∧ r.cost ≤ 4 * n * 45414 + 100 ∧ r.wk ≤ 4 * n * 18 + 10 := by
  classical
  have hM : M31 = 2147483648 := rfl
  have hinfV : s64.valid INF = true := s64_valid_of_bounds _ (by unfold INF; omega) (by unfold INF; omega)
  have hninfV : s64.valid (-INF) = true := s64_valid_of_bounds _ (by unfold INF; omega) (by unfold INF; omega)
  have hAv : ∀ w ∈ a, s64.valid w = true := fun w hw => s64_valid_of_bounds _ (by have := (hAr w hw).1; unfold INF at *; omega) (by have := (hAr w hw).2; unfold INF at *; omega)
  have hhl : 0 < b0.hi.length := by omega
  have hI1 := ct_init_inv a n INF hn b0 hhl h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  obtain ⟨b1, hb1⟩ : ∃ b1 : BS, b1 = { b0 with hi := b0.hi.set 0 (n : Int) } := ⟨_, rfl⟩
  rw [← hb1] at hI1
  have hV1 : ValidOK b1 := by
    subst hb1
    refine ⟨hV0.v0, hV0.v1, hV0.v2, hV0.v3, hV0.v4, hV0.v5, hV0.v6, hV0.v7, hV0.v8, hV0.v9, ?_, hV0.v11, hV0.v12, hV0.v13, hV0.v14⟩
    exact valid_set (fun w => i32.valid w = true) _ _ _ hV0.v10 (Proofs.BellmanFordExec.i32_valid_nat n (by omega))
  have hLens1 : CapS S b1 L := by
    subst hb1
    exact ⟨hLens0.l0, hLens0.l1, hLens0.l2, hLens0.l3, hLens0.l4, hLens0.l5, hLens0.l6, hLens0.l7, hLens0.l8, hLens0.lsk, hLens0.lsl, hLens0.lsr, hLens0.lent⟩
  have hlo1 : L ≤ b1.lo.length := by subst hb1; exact hlo0
  have hhi1 : L ≤ b1.hi.length := by subst hb1; show L ≤ (b0.hi.set 0 (n : Int)).length; rw [List.length_set]; exact hhi0
  obtain ⟨bf, nef, F1, r1, hF1, hl1, hr1, hp1, hv1, hc1, hw1, hIf, hVf, hLf, hlof, hhif⟩ :=
    ct_loop_wide mv hnv pre hty hty32 hty15 P INF rfl a n L hn hL8 hRange hAlen hAv (4 * n) 0 0 b1 (by omega) hI1 hV1 hLens1 hlo1 hhi1
  -- the update loop
  have hl8 := hLf.l8
  have hLv : 4 * n ≤ bf.lval.length := by omega
  have hHR := ct_hrel a n INF rfl hn bf nef hIf hLv
  let C := min L 2147483647
  have hCL : C ≤ L := Nat.min_le_left _ _
  have hCM : C < M31 := by have := Nat.min_le_right L 2147483647; omega
  have hCF : 4*n ≤ C := by dsimp [C]; omega
  have hEcap : ∀ e ∈ LLr n (4 * n), 2 * e + 2 < C := fun e he =>
    Nat.lt_of_lt_of_le (inner_children_lt_four_n n e (mem_LLr n _ e he).1) hCF
  have hEmem : ∀ e ∈ LLr n (4 * n), 2 * e + 2 < L := fun e he => Nat.lt_of_lt_of_le (hEcap e he) hCL
  have hne : nef ≤ C := by have := hIf.hent.1; have := LLr_length_le n (4 * n); omega
  have hSC := phase2_sums a n hn hAr hAlen (by omega) (4 * n) 0 (by omega)
  rw [XX_zero] at hSC
  have hS := SumsOK_lift bf.lval.length (LLr n (4 * n)) (C0 a n) (fun e he => by have := hEmem e he; omega) hSC
  obtain ⟨b2, F2, hF2, hrun2, hH2, hV2, hSL2, hsk2, hsl2, hsr2⟩ :=
    ct_upd_all_separate mv hnv pre hty hty32 hty15 P INF n (4 * n) a hinfV (by omega) (by omega) C hCM (LLr n (4 * n)) bf nef _ hIf.hent hVf (Capacities.shrink hLf hCL) hEcap hne hS hHR
  obtain ⟨r2, h2, hr2, hp2, hv2, hc2, hw2⟩ := hrun2
  have h1' := pexecM_mono mv _ _ _ r1 F1 F2 hl1
  have h2' := pexecM_mono mv _ _ _ r2 F2 F1 h2
  rw [Nat.add_comm F2 F1] at h2'
  have h2'' : pexecM mv (F1 + F2) (CtULoop (mv.nv + pre.length)) r1.ps r1.vv = some r2 := by rw [hp1, hv1]; exact h2'
  have hseq6 := seqM_some h2'' hr2 (pexecM_skip mv (F1 + F2) r2.ps r2.vv)
  have hseq5 := seqM_some h1' hr1 hseq6
  obtain ⟨R5, hR5, hR5ret, hR5ps, hR5vv, hR5c, hR5w⟩ : ∃ R : PRM, pexecM mv (F1 + F2)
      (.sequence (WideCtLoop1 (mv.nv + pre.length)) (.sequence (CtULoop (mv.nv + pre.length)) Sk)) (gS P (pre ++ CtCells INF n 0 0)) (VVA a b1) = some R ∧
      R.ret = none ∧ R.ps = r2.ps ∧ R.vv = r2.vv ∧ R.cost ≤ r1.cost + r2.cost ∧ R.wk ≤ r1.wk + r2.wk :=
    ⟨_, hseq5, by simp, rfl, rfl, by simp, by simp⟩
  -- the initialisation statements (innermost first)
  have hFF : (0 : Nat) = 0 := rfl
  obtain ⟨R4, hR4, hR4ret, hR4ps, hR4vv, hR4c, -, hR4w⟩ := seq_decl mv (F1 + F2) P (pre ++ [cs INF, ci n, ci 0]) (VVA a b1) i32 (.literal i32 0) 0 0
    (den_lit32 mv _ _ 0 (by decide)) (conv_i32 0 (by decide)) _ _ (by rw [List.append_assoc]; exact hR5) hR5ret
  obtain ⟨R3, hR3, hR3ret, hR3ps, hR3vv, hR3c, -, hR3w⟩ := seq_decl mv (F1 + F2) P (pre ++ [cs INF, ci n]) (VVA a b1) i32 (.literal i32 0) 0 0
    (den_lit32 mv _ _ 0 (by decide)) (conv_i32 0 (by decide)) _ _ (by rw [List.append_assoc]; exact hR4) hR4ret
  have hv15 : VVA a b0 15 = a := VVA_get15 a b0
  have hvx : vdenM mv (VVA a b0) (penvN mv.nv (gS P (pre ++ [cs INF, ci n]))) (.variable i32 (mv.nv + pre.length + 1)) = some (n : Int) :=
    den_cellvar_t mv P _ i32 (pre.length + 1) _ (by omega) (n : Int) (cell_at0 pre [cs INF, ci n] 1 (ci n) rfl)
      (Proofs.BellmanFordExec.i32_valid_nat n (by omega)) (VVA a b0)
  obtain ⟨Rw, hRw, hRwret, hRwps, hRwvv, hRwc, -, hRww⟩ := seq_write mv (F1 + F2) (gS P (pre ++ [cs INF, ci n])) (VVA a b0) 10 (by omega) i32
    (hty32 10 (by decide) (by decide)) (.cast u64 (.literal i32 0)) (.variable i32 (mv.nv + pre.length + 1)) (n : Int) 0 hvx
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact den_idx_lit0 mv P _)
    (by rw [VVA_get10]; omega) (Proofs.BellmanFordExec.i32_valid_nat n (by omega)) _ _
    (by rw [VVA_get10, VVA_upd10, ← hb1]; exact hR3) hR3ret _ le_rfl _ le_rfl
  obtain ⟨R1, hR1, hR1ret, hR1ps, hR1vv, hR1c, -, hR1w⟩ := seq_decl mv (F1 + F2) P (pre ++ [cs INF]) (VVA a b0) i32
    (.cast i32 (.size (.integer s64) (.local 15))) (n : Int) (n : Int)
    (by have := ct_size_val mv hnv hty15 (VVA a b0) (penvN mv.nv (gS P (pre ++ [cs INF]))) (by rw [hv15]; omega)
        rw [hv15, hAlen] at this; exact this)
    (conv_i32 _ (Proofs.BellmanFordExec.i32_valid_nat n (by omega))) _ _ (by rw [List.append_assoc]; exact hRw) hRwret
  obtain ⟨R0, hR0, hR0ret, hR0ps, hR0vv, hR0c, -, hR0w⟩ := seq_decl mv (F1 + F2) P (pre ++ []) (VVA a b0) s64
    (.literal s64 4000000000000000000) INF INF
    (by rw [vdenM_scalar _ _ _ _ rfl, den_literal, ite_eq_left (show s64.valid 4000000000000000000 = true from hinfV)]; rfl) (conv_s64 _ hinfV) _ _ (by rw [List.append_assoc]; exact hR1) hR1ret
  have hT := buildBT_spec a hAr n 0 n (by omega) (by omega) (by omega)
  have h0rng : rngOf n 0 = (0, n) := by simp [rngOf]
  have hsub : ∀ j nd otg, sub2 (buildBT a 0 n) 0 j = some (nd, otg) → j < bf.lval.length := by
    intro j nd otg hj
    obtain ⟨hs, -, -⟩ := sub2_build a n (n - 0) 0 n 0 rfl (by omega) h0rng j nd otg hj
    have := skel_lt n hn j hs
    omega
  have hAg := agree_lift bf.lval.length _ _ (agree_final a n hn) hsub
  refine ⟨b2, upPhase (LLr n (4 * n)) (Hlift bf.lval.length (C0 a n)), F1 + F2, R0, hR0, hR0ret, ?_, ?_, hH2, ?_, hV2, Capacities.of_same hLf hSL2, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hR0ps, hR1ps, hRwps, hR3ps, hR4ps, hR5ps, hp2]
  · rw [hR0vv, hR1vv, hRwvv, hR3vv, hR4vv, hR5vv, hv2]
  · rw [upPhase_lift _ _ _ (fun e he => by have := hEmem e he; omega)]; exact hAg
  · have := hSL2.l9; omega
  · have := hSL2.l10; omega
  · have hsk : Shape 0 n (buildBT a 0 n).skel := hT.2
    exact LenOKs_of_eq hSL2.leneq _ _ _ _ (lenOK_build n hn a INF bf nef hIf _ 0 0 n hsk h0rng)

  · have hl := LLr_length_le n (4 * n)
    obtain ⟨m, hm⟩ : ∃ m, m = (LLr n (4 * n)).length := ⟨_, rfl⟩
    have h3 : m * 24794 ≤ 4 * n * 24794 := Nat.mul_le_mul_right _ (hm ▸ hl)
    rw [← hm] at hc2
    have e1 : (vwp (NExpr.cast i32 (.size (.integer s64) (.local 15)))).1 ≤ 10 := by decide
    have e2 : 4 * n * 45414 = 4 * n * 20620 + 4 * n * 24794 := by omega
    have e3 : (vwp (NExpr.literal i32 0)).1 ≤ 5 := by decide
    have e4 : (vwp (NExpr.variable i32 (mv.nv + pre.length + 1))).1 ≤ 5 := by simp [vwp, NExpr.nodes]
    have e5 : (vwp (NExpr.cast u64 (NExpr.literal i32 0))).1 ≤ 5 := by decide
    have e6 : (vwp (NExpr.literal s64 4000000000000000000)).1 ≤ 5 := by decide
    omega
  · have hl := LLr_length_le n (4 * n)
    obtain ⟨m, hm⟩ : ∃ m, m = (LLr n (4 * n)).length := ⟨_, rfl⟩
    have h3 : m * 6 ≤ 4 * n * 6 := Nat.mul_le_mul_right _ (hm ▸ hl)
    rw [← hm] at hw2
    have e2 : 4 * n * 18 = 4 * n * 12 + 4 * n * 6 := by omega
    omega




theorem wide_ctor_wf : Wf (WideCtorCmd 16) = true := by decide
theorem wide_ctor_nb : Nb (WideCtorCmd 16) ≤ 100 := by
  simp [Nb, grC, grS, exS, vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]

theorem ctor_rep_wide {S : Nat} (mv : MV) (hnv : mv.nv = 16) (hty : ∀ v, v < 9 → mv.ty v = s64)
    (hty32 : ∀ v, 9 ≤ v → v < 15 → mv.ty v = i32) (hty15 : mv.ty 15 = s64) (P : List Cell)
    (a : List Int) (n L : Nat) (hn : 1 ≤ n) (hL8 : 8 * n + 8 ≤ L) (hRange : 4*n < M31) (hAlen : a.length = n) (hAr : InRange a)
    (hS : 34 ≤ S) (b0 : BS) (hV0 : ValidOK b0) (hLens0 : CapS S b0 L) (hlo0 : L ≤ b0.lo.length) (hhi0 : L ≤ b0.hi.length)
    (h0 : ∀ j, b0.mxv.getD j 0 = 0) (h1 : ∀ j, b0.smx.getD j 0 = 0) (h2 : ∀ j, b0.mxc.getD j 0 = 0) (h3 : ∀ j, b0.mnv.getD j 0 = 0)
    (h4 : ∀ j, b0.smn.getD j 0 = 0) (h5 : ∀ j, b0.mnc.getD j 0 = 0) (h6 : ∀ j, b0.len.getD j 0 = 0) (h7 : ∀ j, b0.ladd.getD j 0 = 0)
    (h8 : ∀ j, j < b0.lval.length → b0.lval.getD j 0 = INF) (h9 : ∀ j, b0.lo.getD j 0 = 0) (h10 : ∀ j, b0.hi.getD j 0 = 0) :
    ∃ (bf : BS) (Hf : Heap) (F : Nat) (r : PRM),
      pexecM mv F (WideCtorCmd 16) (gS P []) (VVA a b0) = some r ∧ r.ret = none ∧
      r.ps = gS P (CtCells INF n 0 (4 * n)) ∧ r.vv = VVA a bf ∧
      r.cost ≤ 4 * n * 45414 + 100 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ 4 * n * 18 + 10 ∧
      BRepS n L S a bf (buildBT a 0 n) Hf := by
  obtain ⟨bf, Hf, F, r, h1', h2', h3', h4', hH, hAg, hV, hLn, hlo, hhi, hLen, hc, hw⟩ :=
    ct_exec_wide mv hnv [] hty hty32 hty15 P a n L hn hL8 hRange hAlen hAr b0 hV0 hLens0 hlo0 hhi0 h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  have hT := buildBT_spec a hAr n 0 n (by omega) (by omega) (by omega)
  have h0rng : rngOf n 0 = (0, n) := by simp [rngOf]
  have hexec : pexecM mv F (WideCtorCmd 16) (gS P []) (VVA a b0) = some r := by
    simpa [hnv] using h1'
  have hnd := (cmd_need mv _ wide_ctor_wf F _ (VVA a b0) r hexec).1
  have hdrop : (a.drop 0).take (n - 0) = a := by simp; rw [← hAlen]; exact List.take_length
  refine ⟨bf, Hf, F, r, hexec, h2', h3', h4', hc, ?_, hw, ?_⟩
  · simp [szP, gS] at hnd; have := wide_ctor_nb; omega
  · have hsh : Shape 0 n (buildBT a 0 n).skel := hT.2
    have hin := innerS_eq hsh
    have hhl := Proofs.BeatsModel.height_le_power_width 31 (buildBT a 0 n) 0 n hsh
      (by change n - 0 ≤ 2147483648; have hM : M31 = 2147483648 := rfl; omega)
    refine ⟨hAg, hsh, leafOK_build a n 0 n (by omega), by rw [hdrop] at hT; exact hT.1, hH, hV, hLn,
      idxOK_build n hn L hL8 _ 0 0 n hsh h0rng, hLen, ?_, ?_, ?_⟩
    · omega
    · unfold innerOf; omega
    · omega



theorem wide_ctor_core : Proofs.BeatsSlotCycle.CoreCommand (WideCtorCmd 16) = true := by decide

theorem wide_ctor_cycle_runFuel (fuel : Nat) (s : NState) (long : 16 ≤ s.slots.length) :
    Proofs.BeatsSlotCycle.outcomeView
      (runFuel fuel (Proofs.CppSlotRename.command Proofs.BeatsSlotCycle.cycle (WideCtorCmd 16)) s) =
      runFuel fuel (WideCtorCmd 16) (Proofs.BeatsSlotCycle.permute s) :=
  Proofs.BeatsSlotCycle.run_permute fuel (WideCtorCmd 16) s wide_ctor_core long

end Proofs.BeatsRep
