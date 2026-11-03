import Proofs.SegmentTreeMinExec

namespace Proofs.SegmentTreeMinSet
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (rdM_val cidx_den vec_getI vdenM_binary envs M31 getD_mem cs pexecM_branch_true pexecM_branch_false)
open Proofs.TopoSortExec (i32v)
open Proofs.InvGcdExec (vS vr bnd v64 lit0_den lit1_den VO VO_get0 VO_set0)
open Proofs.RunLengthExec (inc_val)
open Proofs.SegmentTreeMinExec
open Proofs.SegTreeMath

/-! ### `SegmentTree::set` (nv = 1: node).  Cells: 0 = n, 1 = n_node, 2 = h_node, 3 = idx, 4 = val, 5 = i -/

abbrev condSet (nv : Nat) : NExpr := .binary bT .le (.variable i32 (nv + 5)) (.variable i32 (nv + 2))
abbrev aHalf (nv : Nat) : NStmt := .assign (nv + 3) i32 (.divrem i32 false (.variable i32 (nv + 3)) (.literal i32 2))
abbrev incI (nv : Nat) : NStmt := .assign (nv + 5) i32 (.binary i32 .add (.variable i32 (nv + 5)) (.literal i32 1))
abbrev SetBody (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (aHalf nv)) (UpdBlk nv 6 0 1 2 3 Sk))) (.sequence (.primitive (incI nv)) Sk)
abbrev bodySet (nv : Nat) : Command :=
  .sequence (.primitive (.assign (nv + 3) i32 (.binary i32 .add (.variable i32 (nv + 3)) (.variable i32 (nv + 1)))))
    (.sequence (.primitive (.write (.local 0) s64 (.cast u64 (.variable i32 (nv + 3))) (.variable s64 (nv + 4))))
      (.sequence (.scope (.sequence (.primitive (.declare i32 true (.literal i32 1)))
        (.sequence (.whileLoop (condSet nv) (SetBody nv)) Sk))) Sk))

theorem body_eqSet : Proofs.SegmentTreeInstance.SegmentTree_cp__SegMin_long_long__long_long_set.body = bodySet 1 := rfl

abbrev LS (n N h idx : Nat) (val : Int) (i : Nat) : List Cell := [ci n, ci N, ci h, ci idx, cs val, ci i]

theorem cdr_i32_div2 (l : Nat) (h : l < 2147483648) : checkedDivRem i32 false (l : Int) 2 = some ((l / 2 : Nat) : Int) := by
  have hq : (l : Int).tdiv 2 = ((l / 2 : Nat) : Int) := by
    rw [Int.tdiv_eq_ediv_of_nonneg (Int.natCast_nonneg l)]; omega
  have hv : i32.valid ((l / 2 : Nat) : Int) = true := i32v _ (by show l / 2 < 2147483648; omega)
  unfold checkedDivRem
  have h0 : ((2 : Int) == 0) = false := by decide
  simp only [h0, hq, hv, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
  exact conv_signed i32 rfl rfl _ hv

set_option maxHeartbeats 16000000 in
/-- One iteration of the loop of `set`: `idx = idx / 2; update(idx); i++`. -/
theorem set_iter (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = s64) (P : List Cell) (fu : Nat) (n N h idx : Nat) (val : Int) (i : Nat)
    (Vt : List Int) (hn : n < 2147483648) (hN : N < 2147483648) (hh : h < 2147483648) (hidx : idx < 2147483648)
    (hq1 : 2 ≤ idx) (hqN : idx / 2 < N) (hlen : Vt.length = 2 * N) (hV : AllV minMon Vt) (hi : i + 1 < 2147483648) :
    ∃ r : PRM, pexecM mv fu (SetBody mv.nv) (gS P (LS n N h idx val i)) (VO Vt) = some r ∧ r.ret = none ∧
      r.ps = gS P (LS n N h (idx / 2) val (i + 1)) ∧
      r.vv = VO (Vt.set (idx / 2) (mn (Vt.getD (2 * (idx / 2)) 0) (Vt.getD (2 * (idx / 2) + 1) 0))) ∧
      r.cost ≤ 800 ∧ r.need ≤ P.length + 100 ∧ r.wk = 1 := by
  have vi : s64.valid (val) = true ∨ True := Or.inr trivial
  have hqM : idx / 2 < 2147483648 := by omega
  have eI := envs mv P (LS n N h idx val i) 3 (ci idx) rfl (i32v idx hidx)
  have eI' : penvN mv.nv (gS P (LS n N h idx val i)) (mv.nv + 3) i32 = some (idx : Int) := eI
  have e1 : vdenM mv (VO Vt) (penvN mv.nv (gS P (LS n N h idx val i))) (.divrem i32 false (.variable i32 (mv.nv + 3)) (.literal i32 2)) =
      some ((idx / 2 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_divrem, den_variable, eI', Option.bind_some, den_literal,
      if_pos (show i32.valid 2 = true from rfl), Option.bind_some, cdr_i32_div2 idx hidx]
  have s1 := gSM_assign mv P (LS n N h idx val i) (VO Vt) 3 (by simp) i32 _ _ _ e1 (ci idx) rfl rfl (i32v idx hidx)
    (conv_signed i32 rfl rfl _ (i32v _ (by show idx / 2 < 2147483648; omega)))
  have eA : (LS n N h idx val i).set 3 ⟨i32, ((idx / 2 : Nat) : Int)⟩ = LS n N h (idx / 2) val i := rfl
  rw [eA] at s1
  have a1 := (pexecM_prim mv fu (aHalf mv.nv) _ _).trans s1
  have hlt : 2 * (idx / 2) + 1 < (VO Vt 0).length := by rw [VO_get0]; omega
  have vx : s64.valid ((VO Vt 0).getD (2 * (idx / 2)) 0) = true := by
    rw [VO_get0]; exact getD_V minMon Vt hV _ (by omega)
  have vy : s64.valid ((VO Vt 0).getD (2 * (idx / 2) + 1) 0) = true := by
    rw [VO_get0]; exact getD_V minMon Vt hV _ (by omega)
  obtain ⟨rU, hU, retU, psU, vvU, cU, nU, wU⟩ := upd_exec mv (by omega) ty0 P (VO Vt) fu (LS n N h (idx / 2) val i) 6 rfl 0 1 2 3
    n N h (idx / 2) rfl rfl rfl rfl hn hN hh (by omega) hlt vx vy Sk _ (pexecM_skip mv fu _ _)
  have s2 := seqM_some a1 rfl hU
  obtain ⟨r1, hr1, hr1ps, hr1ret, hr1vv, hr1w, hr1c, hr1n⟩ : ∃ r1 : PRM,
      pexecM mv fu (.sequence (.primitive (aHalf mv.nv)) (UpdBlk mv.nv 6 0 1 2 3 Sk)) (gS P (LS n N h idx val i)) (VO Vt) = some r1 ∧
      r1.ps = gS P (LS n N h (idx / 2) val i ++ [ci n, ci N, ci h, ci (idx / 2), cs (Vt.getD (2 * (idx / 2)) 0),
        cs (Vt.getD (2 * (idx / 2) + 1) 0), cs (mn (Vt.getD (2 * (idx / 2)) 0) (Vt.getD (2 * (idx / 2) + 1) 0)),
        cs (mn (Vt.getD (2 * (idx / 2)) 0) (Vt.getD (2 * (idx / 2) + 1) 0))]) ∧
      r1.ret = none ∧ r1.vv = VO (Vt.set (idx / 2) (mn (Vt.getD (2 * (idx / 2)) 0) (Vt.getD (2 * (idx / 2) + 1) 0))) ∧
      r1.wk = 1 ∧ r1.cost ≤ 340 ∧ r1.need ≤ P.length + 90 := by
    refine ⟨_, s2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [VO_get0] at psU
      simpa using psU
    · simpa using retU
    · show rU.vv = _
      rw [vvU]
      show upd (VO Vt) 0 ((VO Vt 0).set _ _) = _
      rw [VO_get0, VO_set0]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at wU ⊢; try omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cU ⊢; omega
    · have := nU (P.length + 90) (by simp [gS_mem_len, gS_bs_len]) (by omega)
      simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at this ⊢
      omega
  have b0 := pexecM_scope mv fu _ _ _ _ hr1
  rw [hr1ps] at b0
  have tk := gS_takeC P (LS n N h idx val i) (LS n N h (idx / 2) val i) [ci n, ci N, ci h, ci (idx / 2), cs (Vt.getD (2 * (idx / 2)) 0),
        cs (Vt.getD (2 * (idx / 2) + 1) 0), cs (mn (Vt.getD (2 * (idx / 2)) 0) (Vt.getD (2 * (idx / 2) + 1) 0)),
        cs (mn (Vt.getD (2 * (idx / 2)) 0) (Vt.getD (2 * (idx / 2) + 1) 0))] rfl
  simp only [tk] at b0
  -- i++
  have eIi := envs mv P (LS n N h (idx / 2) val i) 5 (ci i) rfl (i32v i (by show i < 2147483648; omega))
  have eIi' : penvN mv.nv (gS P (LS n N h (idx / 2) val i)) (mv.nv + 5) i32 = some (i : Int) := eIi
  have e2 := inc_val mv (VO (Vt.set (idx / 2) (mn (Vt.getD (2 * (idx / 2)) 0) (Vt.getD (2 * (idx / 2) + 1) 0))))
    (penvN mv.nv (gS P (LS n N h (idx / 2) val i))) (mv.nv + 5) i eIi' hi
  have s3 := gSM_assign mv P (LS n N h (idx / 2) val i) (VO (Vt.set (idx / 2) (mn (Vt.getD (2 * (idx / 2)) 0)
    (Vt.getD (2 * (idx / 2) + 1) 0)))) 5 (by simp) i32 _ _ _ e2 (ci i) rfl rfl (i32v i (by show i < 2147483648; omega))
    (conv_signed i32 rfl rfl _ (i32v (i + 1) (by show i + 1 < 2147483648; omega)))
  have eB : (LS n N h (idx / 2) val i).set 5 ⟨i32, ((i + 1 : Nat) : Int)⟩ = LS n N h (idx / 2) val (i + 1) := rfl
  rw [eB] at s3
  have a3 := (pexecM_prim mv fu (incI mv.nv) _ _).trans s3
  have c3 := seqM_some a3 rfl (pexecM_skip mv fu _ _)
  have c0 := seqM_some b0 hr1ret (by rw [hr1vv]; exact c3)
  refine ⟨_, c0, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp [hr1vv]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hr1c ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hr1n ⊢; omega
  · simp at hr1w ⊢; omega

theorem cond_set_val (mv : MV) (P : List Cell) (vv : Nat → List Int) (n N h idx : Nat) (val : Int) (i : Nat)
    (hh : h < 2147483648) (hi : i < 2147483648) :
    vdenM mv vv (penvN mv.nv (gS P (LS n N h idx val i))) (condSet mv.nv) = some (if i ≤ h then 1 else 0) := by
  have ei : penvN mv.nv (gS P (LS n N h idx val i)) (mv.nv + 5) i32 = some (i : Int) :=
    envs mv P (LS n N h idx val i) 5 (ci i) rfl (i32v i hi)
  have eh : penvN mv.nv (gS P (LS n N h idx val i)) (mv.nv + 2) i32 = some (h : Int) :=
    envs mv P (LS n N h idx val i) 2 (ci h) rfl (i32v h hh)
  rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable, ei, Option.bind_some, den_variable, eh, Option.bind_some]
  by_cases hle : i ≤ h
  · have : (i : Int) ≤ (h : Int) := by omega
    simp [binaryValue, hle, this, Ty.convert, bT, Ty.valid]
  · have : ¬ ((i : Int) ≤ (h : Int)) := by omega
    simp [binaryValue, hle, this, Ty.convert, bT, Ty.valid]

theorem pow_div_facts (h t p : Nat) (ht : t < h) (hp1 : 2 ^ h ≤ p) (hp2 : p < 2 * 2 ^ h) :
    2 ≤ p / 2 ^ t ∧ p / 2 ^ t / 2 = p / 2 ^ (t + 1) ∧ 1 ≤ p / 2 ^ (t + 1) ∧ p / 2 ^ (t + 1) < 2 ^ h := by
  have h1 : 2 ^ (t + 1) ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) ht
  have e : 2 ^ (t + 1) = 2 ^ t * 2 := Nat.pow_succ 2 t
  have hpos : 0 < 2 ^ t := Nat.two_pow_pos t
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Nat.le_div_iff_mul_le hpos]; omega
  · rw [Nat.div_div_eq_div_mul, e]
  · rw [Nat.le_div_iff_mul_le (by omega)]; omega
  · rw [Nat.div_lt_iff_lt_mul (by omega)]
    have : 2 ^ h * 2 ^ (t + 1) ≥ 2 * 2 ^ h := by
      have h2 : 2 ≤ 2 ^ (t + 1) := by rw [e]; omega
      calc 2 * 2 ^ h ≤ 2 ^ (t + 1) * 2 ^ h := Nat.mul_le_mul_right _ h2
        _ = 2 ^ h * 2 ^ (t + 1) := Nat.mul_comm _ _
    omega

set_option maxHeartbeats 16000000 in
/-- The loop `for (i = 1; i <= h_node; i++) { idx = idx / 2; update(idx); }` run from iteration `t + 1`. -/
theorem set_loop (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = s64) (P : List Cell) (n N h p : Nat) (val : Int)
    (hN : N = 2 ^ h) (hn : n < 2147483648) (hh30 : h ≤ 30) (hp1 : N ≤ p) (hp2 : p < 2 * N) :
    ∀ (r t : Nat) (Vt : List Int) (fu : Nat), t + r = h → SInv minMon Vt N (p / 2 ^ (t + 1)) → AllV minMon Vt →
      Vt.length = 2 * N → r + 1 ≤ fu →
      ∃ (res : PRM) (Vf : List Int), pexecM mv fu (.whileLoop (condSet mv.nv) (SetBody mv.nv))
          (gS P (LS n N h (p / 2 ^ t) val (t + 1))) (VO Vt) = some res ∧ res.ret = none ∧
        res.ps = gS P (LS n N h (p / 2 ^ h) val (h + 1)) ∧ res.vv = VO Vf ∧ SInv minMon Vf N 0 ∧ AllV minMon Vf ∧
        Vf.length = 2 * N ∧ (∀ j, N ≤ j → Vf.getD j 0 = Vt.getD j 0) ∧
        res.cost ≤ 900 * r + 30 ∧ res.need ≤ P.length + 100 ∧ res.wk ≤ r := by
  have h30 : 2 ^ 30 = 1073741824 := by norm_num
  have hN30 : N ≤ 1073741824 := by
    rw [hN, ← h30]; exact Nat.pow_le_pow_right (by decide) hh30
  have hN31 : N < 2147483648 := by omega
  have hh : h < 2147483648 := by omega
  have hp31 : p < 2147483648 := by omega
  intro r
  induction r with
  | zero =>
    intro t Vt fu htr hS hV hlen hfu
    have hth : t = h := by omega
    subst hth
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond_set_val mv P (VO Vt) n N t (p / 2 ^ t) val (t + 1) hh (by omega)
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    have hz : p / 2 ^ (t + 1) = 0 := by
      apply Nat.div_eq_of_lt
      rw [Nat.pow_succ, ← hN]; omega
    refine ⟨_, Vt, rfl, rfl, rfl, rfl, ?_, hV, hlen, fun j _ => rfl, ?_, ?_, ?_⟩
    · rw [hz] at hS; exact hS
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
    · simp
  | succ r ih =>
    intro t Vt fu htr hS hV hlen hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hth : t < h := by omega
    have hc := cond_set_val mv P (VO Vt) n N h (p / 2 ^ t) val (t + 1) hh (by omega)
    rw [if_pos (by omega)] at hc
    obtain ⟨hid2, hdiv, hq1, hqN⟩ := pow_div_facts h t p hth (by rw [← hN]; exact hp1) (by rw [← hN]; exact hp2)
    rw [← hN] at hqN
    have hidx : p / 2 ^ t < 2147483648 := by
      have : p / 2 ^ t ≤ p := Nat.div_le_self _ _
      omega
    obtain ⟨r1, h1, ret1, ps1, vv1, c1, n1, w1⟩ := set_iter mv hnv ty0 P (fu' + 1) n N h (p / 2 ^ t) val (t + 1) Vt hn hN31 hh hidx
      hid2 (by rw [hdiv]; exact hqN) hlen hV (by omega)
    rw [hdiv] at ps1 vv1
    have hqmem : 1 ≤ p / 2 ^ (t + 1) ∧ p / 2 ^ (t + 1) < N := ⟨hq1, hqN⟩
    have hS' : SInv minMon (Vt.set (p / 2 ^ (t + 1)) (mn (Vt.getD (2 * (p / 2 ^ (t + 1))) 0) (Vt.getD (2 * (p / 2 ^ (t + 1)) + 1) 0)))
        N (p / 2 ^ (t + 1 + 1)) := by
      have e : p / 2 ^ (t + 1 + 1) = p / 2 ^ (t + 1) / 2 := by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
      rw [e]
      exact sinv_step minMon Vt N (p / 2 ^ (t + 1)) hS hq1 hqN hlen
    have hVx : minMon.V (mn (Vt.getD (2 * (p / 2 ^ (t + 1))) 0) (Vt.getD (2 * (p / 2 ^ (t + 1)) + 1) 0)) :=
      minMon.closed _ _ (getD_V minMon Vt hV _ (by omega)) (getD_V minMon Vt hV _ (by omega))
    have hV' := allV_set minMon Vt hV (p / 2 ^ (t + 1)) _ hVx
    have hlen' : (Vt.set (p / 2 ^ (t + 1)) (mn (Vt.getD (2 * (p / 2 ^ (t + 1))) 0) (Vt.getD (2 * (p / 2 ^ (t + 1)) + 1) 0))).length = 2 * N := by
      simp [hlen]
    obtain ⟨r2, Vf, h2, ret2, ps2, vv2, hSf, hVf, hlenf, hleaf, c2, n2, w2⟩ :=
      ih (t + 1) _ fu' (by omega) hS' hV' hlen' (by omega)
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, ret1, ps1, vv1, h2]
    refine ⟨_, Vf, rfl, ret2, ps2, vv2, hSf, hVf, hlenf, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rw [hleaf j hj, getD_setE]
      have : ¬ (j = p / 2 ^ (t + 1) ∧ p / 2 ^ (t + 1) < Vt.length) := fun hh2 => by omega
      rw [if_neg this]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
    · simp at w1 w2 ⊢; omega

set_option maxHeartbeats 16000000 in
/-- The whole body of `SegmentTree::set`. -/
theorem body_execSet (mv : MV) (hnv : mv.nv = 1) (ty0 : mv.ty 0 = s64) (P : List Cell) (n N h idx : Nat) (val : Int) (V : List Int)
    (hN : N = 2 ^ h) (hn : n < 2147483648) (hh30 : h ≤ 30) (hidx : idx < N) (hT : TInv minMon V N) (hV : AllV minMon V)
    (hval : s64.valid val = true) (fu : Nat) (hfu : h + 3 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (bodySet mv.nv) (gS P [ci n, ci N, ci h, ci idx, cs val]) (VO V) = some r ∧ r.ret = none ∧
      (∃ cl : List Cell, r.ps = gS P cl) ∧
      ∃ Vf : List Int, r.vv = VO Vf ∧ TInv minMon Vf N ∧ AllV minMon Vf ∧ Vf.length = 2 * N ∧ Vf.getD (idx + N) 0 = val ∧
        (∀ j, N ≤ j → j ≠ idx + N → Vf.getD j 0 = V.getD j 0) ∧
        r.cost ≤ 900 * h + 300 ∧ r.need ≤ P.length + 100 ∧ r.wk ≤ h + 1 := by
  have h30 : 2 ^ 30 = 1073741824 := by norm_num
  have hN30 : N ≤ 1073741824 := by
    rw [hN, ← h30]; exact Nat.pow_le_pow_right (by decide) hh30
  have hNpos : 0 < N := by rw [hN]; exact Nat.two_pow_pos h
  have hlenV := hT.2.1
  have hN31 : N < 2147483648 := by omega
  have hh : h < 2147483648 := by omega
  have hidx31 : idx < 2147483648 := by omega
  have hp1 : N ≤ idx + N := by omega
  have hp2 : idx + N < 2 * N := by omega
  have hp31 : idx + N < 2147483648 := by omega
  -- idx += n_node
  have e3 := envs mv P [ci n, ci N, ci h, ci idx, cs val] 3 (ci idx) rfl (i32v idx hidx31)
  have e1 := envs mv P [ci n, ci N, ci h, ci idx, cs val] 1 (ci N) rfl (i32v N hN31)
  have eA : vdenM mv (VO V) (penvN mv.nv (gS P [ci n, ci N, ci h, ci idx, cs val])) (.binary i32 .add (.variable i32 (mv.nv + 3)) (.variable i32 (mv.nv + 1))) =
      some ((idx + N : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_binary, den_variable]
    have e3' : penvN mv.nv (gS P [ci n, ci N, ci h, ci idx, cs val]) (mv.nv + 3) i32 = some (idx : Int) := e3
    have e1' : penvN mv.nv (gS P [ci n, ci N, ci h, ci idx, cs val]) (mv.nv + 1) i32 = some (N : Int) := e1
    rw [e3', Option.bind_some, den_variable, e1', Option.bind_some]
    have : binaryValue .add (idx : Int) (N : Int) = ((idx + N : Nat) : Int) := by
      show (idx : Int) + (N : Int) = _; push_cast; rfl
    rw [this]
    exact conv_signed i32 rfl rfl _ (i32v _ (by show idx + N < 2147483648; omega))
  have s1 := gSM_assign mv P [ci n, ci N, ci h, ci idx, cs val] (VO V) 3 (by simp) i32 _ _ _ eA (ci idx) rfl rfl (i32v idx hidx31)
    (conv_signed i32 rfl rfl _ (i32v _ (by show idx + N < 2147483648; omega)))
  have eS : [ci n, ci N, ci h, ci idx, cs val].set 3 ⟨i32, ((idx + N : Nat) : Int)⟩ = [ci n, ci N, ci h, ci (idx + N), cs val] := rfl
  rw [eS] at s1
  have a1 := (pexecM_prim mv fu (.assign (mv.nv + 3) i32 (.binary i32 .add (.variable i32 (mv.nv + 3)) (.variable i32 (mv.nv + 1)))) _ _).trans s1
  -- node[idx] = val
  have e3p := envs mv P [ci n, ci N, ci h, ci (idx + N), cs val] 3 (ci (idx + N)) rfl (i32v _ hp31)
  have e4p := envs mv P [ci n, ci N, ci h, ci (idx + N), cs val] 4 (cs val) rfl hval
  have hw := pstmtM_write_ok mv (gS P [ci n, ci N, ci h, ci (idx + N), cs val]) (VO V) 0 (by omega)
    (.cast u64 (.variable i32 (mv.nv + 3))) (.variable s64 (mv.nv + 4)) val (idx + N)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact e4p)
    (by rw [vdenM_scalar _ _ _ _ rfl]; exact cidx_den _ _ _ e3p hp31) (by rw [VO_get0]; omega) (by rw [ty0]; exact hval)
  rw [ty0, VO_get0, VO_set0] at hw
  have a2 := (pexecM_prim mv fu (.write (.local 0) s64 (.cast u64 (.variable i32 (mv.nv + 3))) (.variable s64 (mv.nv + 4))) _ _).trans hw
  -- int i = 1
  have d1 := gSM_decl mv P [ci n, ci N, ci h, ci (idx + N), cs val] (VO (V.set (idx + N) val)) i32 (.literal i32 1) 1 1
    (by rw [vdenM_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 1 = true from rfl)])
    (conv_signed i32 rfl rfl _ (show i32.valid 1 = true from rfl))
  have a3 := (pexecM_prim mv fu (.declare i32 true (.literal i32 1)) _ _).trans d1
  -- the loop
  have hS0 := sinv_init minMon V N (idx + N) val hT hp1 hp2
  have hS0' : SInv minMon (V.set (idx + N) val) N ((idx + N) / 2 ^ (0 + 1)) := by simpa using hS0
  have hV0 := allV_set minMon V hV (idx + N) val hval
  have hlen0 : (V.set (idx + N) val).length = 2 * N := by simp [hlenV]
  obtain ⟨rL, Vf, hL, retL, psL, vvL, hSf, hVf, hlenf, hleaf, cL, nL, wL⟩ :=
    set_loop mv hnv ty0 P n N h (idx + N) val hN hn hh30 hp1 hp2 h 0 (V.set (idx + N) val) fu (by omega) hS0' hV0 hlen0 (by omega)
  have hL' : pexecM mv fu (.whileLoop (condSet mv.nv) (SetBody mv.nv)) (gS P ([ci n, ci N, ci h, ci (idx + N), cs val] ++ [ci 1]))
      (VO (V.set (idx + N) val)) = some rL := by simpa using hL
  have b1 := seqM_some hL' retL (pexecM_skip mv fu rL.ps rL.vv)
  have c1 := seqM_some a3 rfl b1
  have c2 := pexecM_scope mv fu _ _ _ _ c1
  have tk := gS_takeC P [ci n, ci N, ci h, ci (idx + N), cs val] [ci n, ci N, ci h, ci ((idx + N) / 2 ^ h), cs val] [ci (h + 1)] rfl
  rw [psL] at c2
  simp only [LS] at c2
  have c3 := seqM_some c2 rfl (pexecM_skip mv fu _ _)
  have c4 := seqM_some a2 rfl c3
  have c5 := seqM_some a1 rfl c4
  refine ⟨_, c5, rfl, ⟨[ci n, ci N, ci h, ci ((idx + N) / 2 ^ h), cs val], ?_⟩, Vf, ?_, ?_, hVf, hlenf, ?_, ?_, ?_, ?_, ?_⟩
  · simp
    exact tk
  · simp [vvL]
  · exact ⟨hNpos, hlenf, sinv_zero minMon Vf N hSf⟩
  · rw [hleaf (idx + N) hp1, getD_setE]
    rw [if_pos ⟨rfl, by omega⟩]
  · intro j hj hne
    rw [hleaf j hj, getD_setE]
    have : ¬ (j = idx + N ∧ idx + N < V.length) := fun hh2 => hne hh2.1
    rw [if_neg this]
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at cL ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at nL ⊢; omega
  · simp at wL ⊢; omega

end Proofs.SegmentTreeMinSet
