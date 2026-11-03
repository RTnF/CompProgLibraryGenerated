import Proofs.LazySegBlocks

namespace Proofs.LazySegUpd
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.ForLoopC (gS_takeC)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getI vdenM_binary envs M31 getD_mem cs pexecM_branch_true pexecM_branch_false)
open Proofs.TopoSortExec (i32v)
open Proofs.InvGcdExec (vS vr bnd v64 lit0_den lit1_den VO VO_get0 VO_set0)
open Proofs.RunLengthExec (inc_val)
open Proofs.LazySegBlocks
open Proofs.LazySegMath (Rep LzFid Cl SInvL)
open Proofs.LazySegChmin (chminMon)
open Proofs.SegmentTreeExec (UpdBlk upd_exec mx)


abbrev aHalf (nv : Nat) : NStmt := .assign (nv + 3) i32 (.divrem i32 false (.variable i32 (nv + 3)) (.literal i32 2))
abbrev incI (nv m : Nat) : NStmt := .assign (nv + m) i32 (.binary i32 .add (.variable i32 (nv + m)) (.literal i32 1))
abbrev condUp (nv m : Nat) : NExpr := .binary bT .le (.variable i32 (nv + m)) (.variable i32 (nv + 2))
abbrev UpBody (nv m : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (aHalf nv)) (UpdBlk nv (m + 1) 0 1 2 3 Sk))) (.sequence (.primitive (incI nv m)) Sk)
abbrev UpLoop (nv m : Nat) : Command := .whileLoop (condUp nv m) (UpBody nv m)

/-- The cells of the update loop: `n, n_node, h_node, idx`, then `pb`, then the counter `i`. -/
abbrev UC (n N h idx : Nat) (pb : List Cell) (i : Nat) : List Cell := [ci n, ci N, ci h, ci idx] ++ pb ++ [ci i]

set_option maxHeartbeats 16000000 in
/-- One iteration of the update loop: `idx = idx / 2; update(idx); i++`. The cells are `n, n_node, h_node, idx`, `pb`, `i`. -/
theorem up_iter (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (P : List Cell) (fu : Nat) (n N h idx : Nat) (pb : List Cell) (m : Nat) (hm : pb.length + 4 = m) (i : Nat)
    (vv : Nat → List Int) (hn : n < 2147483648) (hN : N < 2147483648) (hh : h < 2147483648) (hidx : idx < 2147483648)
    (hq1 : 2 ≤ idx) (hqN : idx / 2 < N) (hlen : (vv 0).length = 2 * N) (hV : ∀ j, j < 2 * N → s64.valid ((vv 0).getD j 0) = true) (hi : i + 1 < 2147483648) :
    ∃ r : PRM, pexecM mv fu (UpBody mv.nv m) (gS P (UC n N h idx pb i)) vv = some r ∧ r.ret = none ∧
      r.ps = gS P (UC n N h (idx / 2) pb (i + 1)) ∧
      r.vv = upd vv 0 ((vv 0).set (idx / 2) (mx ((vv 0).getD (2 * (idx / 2)) 0) ((vv 0).getD (2 * (idx / 2) + 1) 0))) ∧
      r.cost ≤ 800 ∧ r.need ≤ P.length + 2 * m + 120 ∧ r.wk = 1 := by
  have hqM : idx / 2 < 2147483648 := by omega
  have eI := envs mv P (UC n N h idx pb i) 3 (ci idx) (by simp [UC]) (i32v idx hidx)
  have eI' : penvN mv.nv (gS P (UC n N h idx pb i)) (mv.nv + 3) i32 = some (idx : Int) := eI
  have e1 : vdenM mv vv (penvN mv.nv (gS P (UC n N h idx pb i))) (.divrem i32 false (.variable i32 (mv.nv + 3)) (.literal i32 2)) =
      some ((idx / 2 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_divrem, den_variable, eI', Option.bind_some, den_literal,
      if_pos (show i32.valid 2 = true from rfl), Option.bind_some]
    simpa using cdr_i32_div idx 2 hidx (by omega) (by omega)
  have s1 := gSM_assign mv P (UC n N h idx pb i) vv 3 (by simp [UC]) i32 _ _ _ e1 (ci idx) (by simp [UC]) rfl (i32v idx hidx)
    (conv_signed i32 rfl rfl _ (i32v _ (by show idx / 2 < 2147483648; omega)))
  have eA : (UC n N h idx pb i).set 3 ⟨i32, ((idx / 2 : Nat) : Int)⟩ = UC n N h (idx / 2) pb i := by simp [UC, List.set_append_left]
  rw [eA] at s1
  have a1 := (pexecM_prim mv fu (aHalf mv.nv) _ _).trans s1
  have hlt : 2 * (idx / 2) + 1 < (vv 0).length := by omega
  have vx : s64.valid ((vv 0).getD (2 * (idx / 2)) 0) = true := hV _ (by omega)
  have vy : s64.valid ((vv 0).getD (2 * (idx / 2) + 1) 0) = true := hV _ (by omega)
  obtain ⟨rU, hU, retU, psU, vvU, cU, nU, wU⟩ := upd_exec mv (by omega) ty0 P vv fu (UC n N h (idx / 2) pb i) (m + 1) (by simp [UC, hm.symm]) 0 1 2 3
    n N h (idx / 2) rfl rfl rfl rfl hn hN hh (by omega) hlt vx vy Sk _ (pexecM_skip mv fu _ _)
  have s2 := seqM_some a1 rfl hU
  obtain ⟨r1, hr1, hr1ps, hr1ret, hr1vv, hr1w, hr1c, hr1n⟩ : ∃ r1 : PRM,
      pexecM mv fu (.sequence (.primitive (aHalf mv.nv)) (UpdBlk mv.nv (m + 1) 0 1 2 3 Sk)) (gS P (UC n N h idx pb i)) vv = some r1 ∧
      r1.ps = gS P (UC n N h (idx / 2) pb i ++ [ci n, ci N, ci h, ci (idx / 2), cs ((vv 0).getD (2 * (idx / 2)) 0),
        cs ((vv 0).getD (2 * (idx / 2) + 1) 0), cs (mx ((vv 0).getD (2 * (idx / 2)) 0) ((vv 0).getD (2 * (idx / 2) + 1) 0)),
        cs (mx ((vv 0).getD (2 * (idx / 2)) 0) ((vv 0).getD (2 * (idx / 2) + 1) 0))]) ∧
      r1.ret = none ∧ r1.vv = upd vv 0 ((vv 0).set (idx / 2) (mx ((vv 0).getD (2 * (idx / 2)) 0) ((vv 0).getD (2 * (idx / 2) + 1) 0))) ∧
      r1.wk = 1 ∧ r1.cost ≤ 340 ∧ r1.need ≤ P.length + 2 * m + 100 := by
    refine ⟨_, s2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [VO_get0] at psU
      simpa using psU
    · simpa using retU
    · simpa using vvU
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at wU ⊢; try omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cU ⊢; omega
    · have := nU (P.length + 2 * m + 100) (by simp [gS_mem_len, gS_bs_len, UC]; omega) (by omega)
      simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at this ⊢
      omega
  have b0 := pexecM_scope mv fu _ _ _ _ hr1
  rw [hr1ps] at b0
  have tk := gS_takeC P (UC n N h idx pb i) (UC n N h (idx / 2) pb i) [ci n, ci N, ci h, ci (idx / 2), cs ((vv 0).getD (2 * (idx / 2)) 0),
        cs ((vv 0).getD (2 * (idx / 2) + 1) 0), cs (mx ((vv 0).getD (2 * (idx / 2)) 0) ((vv 0).getD (2 * (idx / 2) + 1) 0)),
        cs (mx ((vv 0).getD (2 * (idx / 2)) 0) ((vv 0).getD (2 * (idx / 2) + 1) 0))] (by simp [UC])
  simp only [tk] at b0
  -- i++
  have eIi := envs mv P (UC n N h (idx / 2) pb i) m (ci i) (by simp [UC, hm.symm])  (i32v i (by show i < 2147483648; omega))
  have eIi' : penvN mv.nv (gS P (UC n N h (idx / 2) pb i)) (mv.nv + m) i32 = some (i : Int) := eIi
  have e2 := inc_val mv (upd vv 0 ((vv 0).set (idx / 2) (mx ((vv 0).getD (2 * (idx / 2)) 0) ((vv 0).getD (2 * (idx / 2) + 1) 0))))
    (penvN mv.nv (gS P (UC n N h (idx / 2) pb i))) (mv.nv + m) i eIi' hi
  have s3 := gSM_assign mv P (UC n N h (idx / 2) pb i) (upd vv 0 ((vv 0).set (idx / 2) (mx ((vv 0).getD (2 * (idx / 2)) 0)
    ((vv 0).getD (2 * (idx / 2) + 1) 0)))) m (by simp [UC, hm.symm]) i32 _ _ _ e2 (ci i) (by simp [UC, hm.symm]) rfl (i32v i (by show i < 2147483648; omega))
    (conv_signed i32 rfl rfl _ (i32v (i + 1) (by show i + 1 < 2147483648; omega)))
  have eB : (UC n N h (idx / 2) pb i).set m ⟨i32, ((i + 1 : Nat) : Int)⟩ = UC n N h (idx / 2) pb (i + 1) := by
    unfold UC; rw [← hm]; simp [List.set_append_right]
  rw [eB] at s3
  have a3 := (pexecM_prim mv fu (incI mv.nv m) _ _).trans s3
  have c3 := seqM_some a3 rfl (pexecM_skip mv fu _ _)
  have c0 := seqM_some b0 hr1ret (by rw [hr1vv]; exact c3)
  refine ⟨_, c0, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [hr1vv]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hr1c ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hr1n ⊢; omega
  · simp at hr1w ⊢; omega



theorem cond_up_val (mv : MV) (P : List Cell) (vv : Nat → List Int) (n N h idx : Nat) (pb : List Cell) (m : Nat)
    (hm : pb.length + 4 = m) (i : Nat) (hh : h < 2147483648) (hi : i < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P (UC n N h idx pb i))) (condUp mv.nv m) = some (if i ≤ h then 1 else 0) := by
  have ei : penvN mv.nv (gS P (UC n N h idx pb i)) (mv.nv + m) i32 = some (i : Int) :=
    envs mv P (UC n N h idx pb i) m (ci i) (by simp [UC, hm.symm]) (i32v i hi)
  have eh : penvN mv.nv (gS P (UC n N h idx pb i)) (mv.nv + 2) i32 = some (h : Int) :=
    envs mv P (UC n N h idx pb i) 2 (ci h) (by simp [UC]) (i32v h hh)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, ei, Option.bind_some, den_variable, eh, Option.bind_some]
  by_cases hle : i ≤ h
  · have : (i : Int) ≤ (h : Int) := by omega
    simp [binaryValue, hle, this, Ty.convert, bT, Ty.valid]
  · have : ¬ ((i : Int) ≤ (h : Int)) := by omega
    simp [binaryValue, hle, this, Ty.convert, bT, Ty.valid]

theorem upd_node_eq (vv : Nat → List Int) (i : Nat) (hlt : 2 * i + 1 < (vv 0).length) :
    (vv 0).set i (mx ((vv 0).getD (2 * i) 0) ((vv 0).getD (2 * i + 1) 0)) =
      Proofs.LazySegMath.updNode chminMon (vv 0) i := by
  unfold Proofs.LazySegMath.updNode
  rw [Proofs.LazySegBlocks.getD_dflt (vv 0) (2 * i) 0 chminMon.e (by omega),
    Proofs.LazySegBlocks.getD_dflt (vv 0) (2 * i + 1) 0 chminMon.e (by omega)]
  rfl

set_option maxHeartbeats 64000000 in
theorem up_loop (mv : MV) (hnv : mv.nv = 2) (ty0 : mv.ty 0 = s64) (P : List Cell) (n h p : Nat) (pb : List Cell) (m : Nat) (hm : pb.length + 4 = m) (A' : List Int)
    (hn : n < 2147483648) (hh30 : h ≤ 30) (hp1 : 2 ^ h ≤ p) (hp2 : p < 2 * 2 ^ h) :
    ∀ (d t : Nat) (vv : Nat → List Int) (fu : Nat), t + d = h →
      SInvL chminMon (2 ^ h) A' p h t (vv 0) (vv 1) → d + 1 ≤ fu →
      ∃ (res : PRM) (vf : Nat → List Int), pexecM mv fu (UpLoop mv.nv m)
          (gS P (UC n (2 ^ h) h (p / 2 ^ t) pb (t + 1))) vv = some res ∧
        res.ret = none ∧ res.ps = gS P (UC n (2 ^ h) h (p / 2 ^ h) pb (h + 1)) ∧ res.vv = vf ∧ vf 1 = vv 1 ∧
        SInvL chminMon (2 ^ h) A' p h h (vf 0) (vf 1) ∧
        res.cost ≤ 900 * d + 30 ∧ res.need ≤ P.length + 2 * m + 120 ∧ res.wk ≤ d := by
  have hN30 : 2 ^ h ≤ 2 ^ 30 := Nat.pow_le_pow_right (by decide) hh30
  have h30 : 2 ^ 30 = 1073741824 := by norm_num
  intro d
  induction d with
  | zero =>
    intro t vv fu hid hI hfu
    have ht : t = h := by omega
    subst ht
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond_up_val mv P vv n (2 ^ t) t (p / 2 ^ t) pb m hm (t + 1) (by omega) (by omega)
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, vv, rfl, rfl, rfl, rfl, rfl, hI, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, UC]; omega
    · simp
  | succ d ih =>
    intro t vv fu hid hI hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond_up_val mv P vv n (2 ^ h) h (p / 2 ^ t) pb m hm (t + 1) (by omega) (by omega)
    rw [if_pos (by omega)] at hc
    obtain ⟨hn0, hl0, hV0, hF0, hAV, hA0, hz, hE⟩ := hI
    have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
    have hq1 : 2 ≤ p / 2 ^ t := by
      rw [Nat.le_div_iff_mul_le hpos]
      have : 2 ^ (t + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.pow_succ] at this
      omega
    have hdivdiv : p / 2 ^ t / 2 = p / 2 ^ (t + 1) := by
      rw [Nat.div_div_eq_div_mul, Nat.pow_succ]
    have hqN : p / 2 ^ t / 2 < 2 ^ h := by
      rw [hdivdiv]
      have hpos' : 0 < 2 ^ (t + 1) := Nat.two_pow_pos _
      rw [Nat.div_lt_iff_lt_mul hpos']
      have : 2 ^ 1 ≤ 2 ^ (t + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 : 2 ^ h * 2 ≤ 2 ^ h * 2 ^ (t + 1) := Nat.mul_le_mul_left _ (by simpa using this)
      omega
    have hVv : ∀ j, j < 2 * 2 ^ h → s64.valid ((vv 0).getD j 0) = true := fun j hj => by
      have := Proofs.LazySegMath.getD_Ve chminMon (vv 0) hV0 j (by omega)
      rw [Proofs.LazySegBlocks.getD_dflt (vv 0) j 0 chminMon.e (by omega)]
      exact this
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := up_iter mv hnv ty0 P (fu' + 1) n (2 ^ h) h (p / 2 ^ t) pb m hm (t + 1) vv hn
      (by omega) (by omega) (by omega) hq1 hqN hn0 hVv (by omega)
    have hlt2 : 2 * (p / 2 ^ t / 2) + 1 < (vv 0).length := by omega
    rw [upd_node_eq vv _ hlt2, hdivdiv] at vv1
    have ps1' : r1.ps = gS P (UC n (2 ^ h) h (p / 2 ^ (t + 1)) pb (t + 1 + 1)) := by rw [ps1, hdivdiv]
    have hS := Proofs.LazySegMath.sInvL_step chminMon (2 ^ h) A' p h t (vv 0) (vv 1) rfl hp1 hp2 (by omega)
      ⟨hn0, hl0, hV0, hF0, hAV, hA0, hz, hE⟩
    have hv1 : (upd vv 0 (Proofs.LazySegMath.updNode chminMon (vv 0) (p / 2 ^ (t + 1)))) 1 = vv 1 := by simp [upd]
    have hv0 : (upd vv 0 (Proofs.LazySegMath.updNode chminMon (vv 0) (p / 2 ^ (t + 1)))) 0
        = Proofs.LazySegMath.updNode chminMon (vv 0) (p / 2 ^ (t + 1)) := by simp [upd]
    obtain ⟨r2, vf, h2, ret2, ps2, vv2, hv1f, hIf, c2, n2, w2⟩ := ih (t + 1) (upd vv 0 (Proofs.LazySegMath.updNode chminMon (vv 0) (p / 2 ^ (t + 1)))) fu'
      (by omega) (by rw [hv0, hv1]; exact hS) (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, ret1, ps1', vv1, h2]
    refine ⟨_, vf, rfl, ret2, ps2, vv2, by rw [hv1f, hv1], hIf, ?_, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len, UC] at n1 n2 ⊢; omega
    · simp at w1 w2 ⊢; omega


end Proofs.LazySegUpd
