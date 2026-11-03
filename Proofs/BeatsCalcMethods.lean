import Proofs.BeatsWrap
import Proofs.BeatsCalcSpec
import Proofs.BeatsCalcApply2
import Proofs.Generated.SegmentTreeBeats
namespace Proofs.BeatsRep
open Proofs.BeatsModel Proofs.BeatsExec Proofs.BeatsInstance
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
set_option maxRecDepth 100000


/-- The five leading copies `inf, n, op, a, b` of a `calc_op` wrapper. -/
abbrev W5 (op : Nat) (REST : Command) : Command :=
  .sequence (.primitive (.declare s64 true (.variable s64 15)))
  (.sequence (.primitive (.declare i32 true (.variable i32 16)))
  (.sequence (.primitive (.declare i32 true (.literal i32 (op : Int))))
  (.sequence (.primitive (.declare i32 true (.variable i32 17)))
  (.sequence (.primitive (.declare i32 true (.variable i32 18))) REST))))

theorem w5_exec (mv : MV) (hnv : mv.nv = 15) (P : List Cell) (vv : Nat → List Int) (fu : Nat)
    (inf : Int) (n a b : Nat) (op : Nat) (hinf : s64.valid inf = true)
    (hn : n < M31) (ha : a < M31) (hb : b < M31) (hop : i32.valid (op : Int) = true)
    (REST : Command) (r2 : PRM)
    (h2 : pexecM mv fu REST (gS P [cs inf, ci n, ci a, ci b, cs inf, ci n, ci op, ci a, ci b]) vv = some r2) :
    ∃ r : PRM, pexecM mv fu (W5 op REST) (gS P [cs inf, ci n, ci a, ci b]) vv = some r ∧
      r.ps = r2.ps ∧ r.vv = r2.vv ∧ r.ret = r2.ret ∧ r.cost ≤ 10 + r2.cost ∧ r.need ≤ max (P.length + 40) r2.need ∧ r.wk = r2.wk := by
  have K : ∀ (cl : List Cell) (e : NExpr) (v v' : Int) (ty : Ty),
      vdenM mv vv (penvN mv.nv (gS P cl)) e = some v → ty.convert v = some v' →
      pexecM mv fu (.primitive (.declare ty true e)) (gS P cl) vv =
        some ⟨gS P (cl ++ [⟨ty, v'⟩]), vv, none, (vwp e).1 + 1, P.length + 2 * cl.length + (vwp e).2 + 4, 0⟩ :=
    fun cl e v v' ty hv hc => (pexecM_prim mv fu _ _ _).trans (gSM_decl mv P cl vv ty e v v' hv hc)
  have q5 := K [cs inf, ci n, ci a, ci b, cs inf, ci n, ci op, ci a] (.variable i32 18) b b i32
    (by have := venv mv vv P [cs inf, ci n, ci a, ci b, cs inf, ci n, ci op, ci a] 3 18 (ci b) rfl (validN b hb) (by omega); exact this)
    (conv_signed i32 rfl rfl _ (validN b hb))
  have q4 := K [cs inf, ci n, ci a, ci b, cs inf, ci n, ci op] (.variable i32 17) a a i32
    (by have := venv mv vv P [cs inf, ci n, ci a, ci b, cs inf, ci n, ci op] 2 17 (ci a) rfl (validN a ha) (by omega); exact this)
    (conv_signed i32 rfl rfl _ (validN a ha))
  have q3 := K [cs inf, ci n, ci a, ci b, cs inf, ci n] (.literal i32 (op : Int)) (op : Int) (op : Int) i32
    (lenv mv vv P _ i32 op hop) (conv_signed i32 rfl rfl _ hop)
  have q2 := K [cs inf, ci n, ci a, ci b, cs inf] (.variable i32 16) n n i32
    (by have := venv mv vv P [cs inf, ci n, ci a, ci b, cs inf] 1 16 (ci n) rfl (validN n hn) (by omega); exact this)
    (conv_signed i32 rfl rfl _ (validN n hn))
  have q1 := K [cs inf, ci n, ci a, ci b] (.variable s64 15) inf inf s64
    (by have := venv mv vv P [cs inf, ci n, ci a, ci b] 0 15 (cs inf) rfl hinf (by omega); exact this)
    (conv_signed s64 rfl rfl _ hinf)
  have c5 := seqM_some q5 rfl h2
  have c4 := seqM_some q4 rfl c5
  have c3 := seqM_some q3 rfl c4
  have c2 := seqM_some q2 rfl c3
  have c1 := seqM_some q1 rfl c2
  refine ⟨_, c1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]; omega
  · simp

theorem wrap5_gen (mv : MV) (hnv : mv.nv = 15) (P : List Cell) (vv : Nat → List Int)
    (inf : Int) (n a b : Nat) (op : Nat) (hinf : s64.valid inf = true)
    (hn : n < M31) (ha : a < M31) (hb : b < M31) (hop : op < M31)
    (T : Command) (hsim : Sim 4 (CalcOpCmd2 19) T) (hna : noAsg 4 (CalcOpCmd2 19) = true)
    (hWf : Wf (W5 op T) = true) (hNb : Nb (W5 op T) ≤ 400)
    (C W : Nat) (xf : Int) (Q : (Nat → List Int) → Prop) (LC : List Cell)
    (hA : ∃ F r, pexecM mv F (CalcOpCmd2 19) (gS P [cs inf, ci n, ci a, ci b, cs inf, ci n, ci op, ci a, ci b]) vv = some r ∧
      r.ret = some xf ∧ r.ps = gS P ([cs inf, ci n, ci a, ci b] ++ LC) ∧ Q r.vv ∧ r.cost ≤ C ∧ r.wk ≤ W) :
    ∃ F r, pexecM mv F (W5 op T) (gS P [cs inf, ci n, ci a, ci b]) vv = some r ∧
      r.ret = some xf ∧ r.ps = gS P ([cs inf, ci n, ci a, ci b] ++ LC) ∧ Q r.vv ∧ r.cost ≤ C + 10 ∧
      r.need ≤ P.length + 410 ∧ r.wk ≤ W := by
  obtain ⟨F, r2, h2, hret, hps, hQ, hc, hw⟩ := hA
  have hAl : Al 4 [cs inf, ci n, ci a, ci b, cs inf, ci n, ci op, ci a, ci b] := ⟨by simp, rfl, rfl⟩
  obtain ⟨h2', _⟩ := sim_exec 4 mv hnv hsim hna F P _ vv r2 hAl h2
  obtain ⟨r, h, e1, e2, e3, e4, e5, e6⟩ := w5_exec mv hnv P vv F inf n a b op hinf hn ha hb (validN op hop) _ r2 h2'
  refine ⟨F, r, h, by rw [e3]; exact hret, by rw [e1]; exact hps, by rw [e2]; exact hQ, by omega, ?_, by omega⟩
  have := (cmd_need mv _ hWf F _ vv r h).1
  simp [szP, gS] at this
  omega


theorem na_calc : noAsg 4 (CalcOpCmd2 19) = true := by decide

theorem tail_calc_max : ∃ T, SegmentTreeBeats_calc_max.body = W5 0 T ∧ Sim 4 (CalcOpCmd2 19) T := by
  refine ⟨_, rfl, ?_⟩
  repeat (first | exact Sim.prim | (apply Sim.dec; decide) | apply Sim.seq | apply Sim.scope | apply Sim.branch | apply Sim.whileLoop | exact Sim.breakLoop)
theorem wf_calc_max : Wf SegmentTreeBeats_calc_max.body = true := by decide
theorem nb_calc_max : Nb SegmentTreeBeats_calc_max.body ≤ 400 := by decide

set_option maxHeartbeats 64000000 in
theorem calc_max_exec {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {L : Nat}
    (hnv : mv.nv = 15)
    (Ev : Env mv [cs inf, ci n, ci qa, ci qb] P inf n 0 qa qb 0 L) (t : BT) (ys : List Int) (b : BS) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) (hinv : BeatsModel.Inv t ys) (hsafe : calcSafe qa qb t 0 n)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : Lens b L) (hidx : IdxOK t 0 L) (hlen : LenOK b t 0 0 n)
    (hsp : 1 + t.height + 2 ≤ L) (hlh : 0 ≤ n ∧ 2 * n < M31) :
    ∃ (bf : BS) (Hf : Heap) (xf : Int) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_calc_max.body (gS P [cs inf, ci n, ci qa, ci qb]) (VVB b) = some r ∧
      r.ret = some xf ∧ r.ps = gS P ([cs inf, ci n, ci qa, ci qb] ++ (CCells inf n 0 qa qb xf 0 ++ [cs xf])) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 72254 + 4 + 5000 + 16 + 10 ∧ r.need ≤ P.length + 410 ∧ r.wk ≤ nodesOf t * 24 + 3 ∧
      HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf ((specMax qa qb).calcF t 0 n).1 0 ∧
      xf = (specMax qa qb).comb (specMax qa qb).idv ((specMax qa qb).calcF t 0 n).2 ∧ bf.len = b.len ∧ s64.valid xf = true := by
  have hI := Ev.hinfI
  have hidv : (if ((0 : Nat) : Int) = 1 then inf else -inf) = (specMax qa qb).idv := by
    rw [hI]; simp [specMax]
  have hv : s64.valid (specMax qa qb).idv = true := by
    simp only [specMax]; first | exact (hI ▸ Ev.hninf) | (rw [← hI]; exact Ev.hinf)
  have hrb : (specMax qa qb).RB (specMax qa qb).idv := by simp [specMax]
  obtain ⟨bf, Hf, xf, F, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    calc_exec2 Ev (specMax qa qb) (wholeStep_max rfl) hidv hv hrb t ys b H hag hsh hlf hinv hsafe hH hV hLens hidx hlen hsp hlh
  rw [hnv] at h1
  obtain ⟨T, hbT, hsim⟩ := tail_calc_max
  have hWf : Wf (W5 0 T) = true := hbT ▸ wf_calc_max
  have hNb : Nb (W5 0 T) ≤ 400 := hbT ▸ nb_calc_max
  obtain ⟨F', r', g1, g2, g3, g4, g5, g6, g7⟩ := wrap5_gen mv hnv P (VVB b) inf n qa qb 0 Ev.hinf Ev.hnM Ev.hqaM Ev.hqbM (by decide)
    T hsim na_calc hWf hNb _ _ xf (fun v => ∃ bf Hf, v = VVB bf ∧ HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf ((specMax qa qb).calcF t 0 n).1 0) (CCells inf n 0 qa qb xf 0 ++ [cs xf])
    ⟨F, r, by simpa using h1, h2, by rw [h3]; simp, ⟨bf, Hf, h4, h7, h8, h9, h10⟩, h5, h6⟩
  obtain ⟨bf', Hf', g4', q1, q2, q3, q4⟩ := g4
  have hnw : noWr 6 (W5 0 T) = true := hbT ▸ (by decide : noWr 6 SegmentTreeBeats_calc_max.body = true)
  have hv := cmd_vec mv 6 _ hnw F' _ (VVB b) r' g1
  rw [g4'] at hv
  have hlen : bf'.len = b.len := by simpa [VVB] using hv
  exact ⟨bf', Hf', xf, F', r', by rw [hbT]; exact g1, g2, g3, g4', by omega, g6, by omega, q1, q2, q3, q4, h11, hlen, h12⟩

theorem tail_calc_min : ∃ T, SegmentTreeBeats_calc_min.body = W5 1 T ∧ Sim 4 (CalcOpCmd2 19) T := by
  refine ⟨_, rfl, ?_⟩
  repeat (first | exact Sim.prim | (apply Sim.dec; decide) | apply Sim.seq | apply Sim.scope | apply Sim.branch | apply Sim.whileLoop | exact Sim.breakLoop)
theorem wf_calc_min : Wf SegmentTreeBeats_calc_min.body = true := by decide
theorem nb_calc_min : Nb SegmentTreeBeats_calc_min.body ≤ 400 := by decide

set_option maxHeartbeats 64000000 in
theorem calc_min_exec {mv : MV} {P : List Cell} {inf : Int} {n qa qb : Nat} {L : Nat}
    (hnv : mv.nv = 15)
    (Ev : Env mv [cs inf, ci n, ci qa, ci qb] P inf n 1 qa qb 0 L) (t : BT) (ys : List Int) (b : BS) (H : Heap)
    (hag : Agree H t 0) (hsh : Shape 0 n t.skel) (hlf : LeafOK t) (hinv : BeatsModel.Inv t ys) (hsafe : calcSafe qa qb t 0 n)
    (hH : HRel inf b H) (hV : ValidOK b) (hLens : Lens b L) (hidx : IdxOK t 0 L) (hlen : LenOK b t 0 0 n)
    (hsp : 1 + t.height + 2 ≤ L) (hlh : 0 ≤ n ∧ 2 * n < M31) :
    ∃ (bf : BS) (Hf : Heap) (xf : Int) (F : Nat) (r : PRM),
      pexecM mv F SegmentTreeBeats_calc_min.body (gS P [cs inf, ci n, ci qa, ci qb]) (VVB b) = some r ∧
      r.ret = some xf ∧ r.ps = gS P ([cs inf, ci n, ci qa, ci qb] ++ (CCells inf n 1 qa qb xf 0 ++ [cs xf])) ∧ r.vv = VVB bf ∧
      r.cost ≤ nodesOf t * 72254 + 4 + 5000 + 16 + 10 ∧ r.need ≤ P.length + 410 ∧ r.wk ≤ nodesOf t * 24 + 3 ∧
      HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf ((specMin qa qb).calcF t 0 n).1 0 ∧
      xf = (specMin qa qb).comb (specMin qa qb).idv ((specMin qa qb).calcF t 0 n).2 ∧ bf.len = b.len ∧ s64.valid xf = true := by
  have hI := Ev.hinfI
  have hidv : (if ((1 : Nat) : Int) = 1 then inf else -inf) = (specMin qa qb).idv := by
    rw [hI]; simp [specMin]
  have hv : s64.valid (specMin qa qb).idv = true := by
    simp only [specMin]; first | exact (hI ▸ Ev.hninf) | (rw [← hI]; exact Ev.hinf)
  have hrb : (specMin qa qb).RB (specMin qa qb).idv := by simp [specMin]
  obtain ⟨bf, Hf, xf, F, r, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ :=
    calc_exec2 Ev (specMin qa qb) (wholeStep_min rfl) hidv hv hrb t ys b H hag hsh hlf hinv hsafe hH hV hLens hidx hlen hsp hlh
  rw [hnv] at h1
  obtain ⟨T, hbT, hsim⟩ := tail_calc_min
  have hWf : Wf (W5 1 T) = true := hbT ▸ wf_calc_min
  have hNb : Nb (W5 1 T) ≤ 400 := hbT ▸ nb_calc_min
  obtain ⟨F', r', g1, g2, g3, g4, g5, g6, g7⟩ := wrap5_gen mv hnv P (VVB b) inf n qa qb 1 Ev.hinf Ev.hnM Ev.hqaM Ev.hqbM (by decide)
    T hsim na_calc hWf hNb _ _ xf (fun v => ∃ bf Hf, v = VVB bf ∧ HRel inf bf Hf ∧ ValidOK bf ∧ SameLen b bf ∧ Agree Hf ((specMin qa qb).calcF t 0 n).1 0) (CCells inf n 1 qa qb xf 0 ++ [cs xf])
    ⟨F, r, by simpa using h1, h2, by rw [h3]; simp, ⟨bf, Hf, h4, h7, h8, h9, h10⟩, h5, h6⟩
  obtain ⟨bf', Hf', g4', q1, q2, q3, q4⟩ := g4
  have hnw : noWr 6 (W5 1 T) = true := hbT ▸ (by decide : noWr 6 SegmentTreeBeats_calc_min.body = true)
  have hv := cmd_vec mv 6 _ hnw F' _ (VVB b) r' g1
  rw [g4'] at hv
  have hlen : bf'.len = b.len := by simpa [VVB] using hv
  exact ⟨bf', Hf', xf, F', r', by rw [hbT]; exact g1, g2, g3, g4', by omega, g6, by omega, q1, q2, q3, q4, h11, hlen, h12⟩

end Proofs.BeatsRep
