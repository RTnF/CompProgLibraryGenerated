import Proofs.BeatsCalcApply
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
set_option maxRecDepth 100000

abbrev CalcOpCmd2 (o : Nat) : Command :=
  CInitc0 o (.sequence (CLoop o) (.sequence (.primitive (.declare s64 true (.variable s64 (o + 5)))) (.sequence (.primitive (.ret (.variable s64 (o + 7)))) Sk)))

theorem calc_exec2 {mv : MV} {pre P : List Cell} {inf : Int} {n op qa qb L : Nat} (Ev0 : Env mv pre P inf n op qa qb 0 L)
    (sp_ : CSpec qa qb) (hW : WholeStep mv pre P inf n op qa qb L sp_)
    (hinit : (if (op : Int) = 1 then inf else -inf) = sp_.idv) (hvidv : s64.valid sp_.idv = true) (hRB0 : sp_.RB sp_.idv)
    (t : BT) (ys : List Int) (b : BS) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) (hinv : BeatsModel.Inv t ys) (hsafe : calcSafe qa qb t 0 n)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : Lens b L) (hidx : IdxOK t 0 L) (hlen : LenOK b t 0 0 n)
    (hsp : 1 + t.height + 2 ≤ L) (hlh : 0 ≤ n ∧ 2 * n < M31) :
    ∃ (bf : BS) (Hf : Heap) (xf : Int) (F : Nat) (r : PRM),
      pexecM mv F (CalcOpCmd2 (mv.nv + pre.length)) (gS P (pre ++ [cs inf, ci n, ci op, ci qa, ci qb])) (VVB b) = some r ∧
      r.ret = some xf ∧ r.ps = gS P (pre ++ CCells inf n op qa qb xf 0 ++ [cs xf]) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 72254 + 4 + 5000 + 16 ∧ r.wk ≤ nodesOf t * 24 + 3 ∧
      HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf (sp_.calcF t 0 n).1 0 ∧ xf = sp_.comb sp_.idv (sp_.calcF t 0 n).2 ∧ s64.valid xf = true := by
  have hL0 : 0 < L := by omega
  have hlk : 0 < b.sk.length := by have := hLens.lsk; omega
  have hll : 0 < b.sl.length := by have := hLens.lsl; omega
  have hlr : 0 < b.sr.length := by have := hLens.lsr; omega
  have hHI : HRel inf (initC b n) H := HRel_stable inf b (initC b n) H hH (fun i => ⟨rfl, rfl⟩) rfl
  have hlenI : LenOK (initC b n) t 0 0 n := LenOKs_of_eq (b := b) (b' := initC b n) rfl _ _ _ _ hlen
  have hSLI := initC_sameLen b n
  have hLensI := Lens_of_same hLens hSLI
  have hVI := initC_valid b n Ev0.hnM hV
  have key := frameC_all Ev0 sp_ hW (fun bf xf => ∃ H' : Heap, HRel inf bf H' ∧ ValidOK bf ∧ SameLen (initC b n) bf ∧
      Agree H' (sp_.calcF t 0 n).1 0 ∧ xf = sp_.comb sp_.idv (sp_.calcF t 0 n).2 ∧ s64.valid xf = true) t.height t (le_refl _) 1 4 0
  obtain ⟨bf, xf, F, hF, hRun, H', hHR', hVf, hSLf, hAg, hxf, hvf⟩ :=
    key 0 0 n ys (initC b n) 1 [] H sp_.idv hag hsh hlf hinv hsafe hHI hVI hLensI hidx hlenI (initC_stk b n hlk hll hlr) hsp hlh hvidv hRB0
      (by
        intro bK H' rK hHR hS hV' hSL hst hfr hAg hrK hvK
        exact ⟨bK, rK, 1, le_refl _, runsC_exit mv Ev0.hnv 0 P pre inf n op qa qb rK bK, H', hHR, hV', hSL, hAg, hrK, hvK⟩)
  obtain ⟨r1, h1, hr1, hp1, hv1, hc1, hw1⟩ := hRun
  have hvret : vdenM mv r1.vv (penvN mv.nv r1.ps) (.variable s64 (mv.nv + pre.length + 5)) = some xf := by
    rw [hp1]
    exact den_cellvar_t mv P _ s64 (pre.length + 5) _ (by omega) xf (cell_at0 pre (CCells inf n op qa qb xf 0) 5 (cs xf) rfl) hvf r1.vv
  have hd := gSM_decl mv P (pre ++ CCells inf n op qa qb xf 0) r1.vv s64 (.variable s64 (mv.nv + pre.length + 5)) xf xf
    (by rw [← hp1]; exact hvret) (conv_signed s64 rfl rfl _ hvf)
  rw [← hp1] at hd
  have hd' := (pexecM_prim mv F (.declare s64 true (.variable s64 (mv.nv + pre.length + 5))) r1.ps r1.vv).trans hd
  have hvret2 : vdenM mv r1.vv (penvN mv.nv (gS P (pre ++ CCells inf n op qa qb xf 0 ++ [cs xf]))) (.variable s64 (mv.nv + pre.length + 7)) = some xf := by
    rw [List.append_assoc]
    exact den_cellvar_t mv P _ s64 (pre.length + 7) (mv.nv + pre.length + 7) (by omega) xf (cell_at0 pre (CCells inf n op qa qb xf 0 ++ [cs xf]) 7 (cs xf) rfl) hvf r1.vv
  have hr2 := pstmtM_ret_ok mv (gS P (pre ++ CCells inf n op qa qb xf 0 ++ [cs xf])) r1.vv _ xf hvret2
  have hex2 := seqM_ret (b := Sk) (fu := F) ((pexecM_prim mv F _ _ r1.vv).trans hr2) rfl
  have hex3 := seqM_some hd' rfl hex2
  have hseq := seqM_some h1 hr1 hex3
  obtain ⟨r0, h0, hr0, hp0, hv0, hc0, hw0⟩ :=
    CInit_ch0r mv Ev0.hnv pre Ev0.hty Ev0.hty32 (initC b n |> fun _ => b) P inf n op qa qb 0 Ev0.hinf Ev0.hnM Ev0.hopM Ev0.hqaM Ev0.hqbM Ev0.hx hV.v11 hV.v12 hV.v13
      hlk hll hlr sp_.idv hinit.symm 1 rfl Ev0.hninf F
      (.sequence (CLoop (mv.nv + pre.length)) (.sequence (.primitive (.declare s64 true (.variable s64 (mv.nv + pre.length + 5)))) (.sequence (.primitive (.ret (.variable s64 (mv.nv + pre.length + 7)))) Sk)))
      _ hseq (some xf) rfl
  refine ⟨bf, H', xf, F, r0, h0, hr0, ?_, ?_, ?_, ?_, hHR', hVf, SameLen_trans hSLI hSLf, hAg, hxf, hvf⟩
  · rw [hp0]
  · rw [hv0]; exact hv1
  · have := hc0; simp [vwp, NExpr.nodes] at this ⊢; omega
  · have := hw0; simp at this ⊢; omega

end Proofs.BeatsRep
