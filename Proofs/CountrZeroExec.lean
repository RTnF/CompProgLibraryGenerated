import Proofs.InvGcdExec
import Proofs.Generated.CountrZero

namespace Proofs.CountrZeroExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne rem_value)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (envs M31)
open Proofs.TopoSortExec (i32v)
open Proofs.RunLengthExec (inc_val)

/-! ### `countr_zero_u64` (nv = 0).  Cells: 0 = n (u64), 1 = x (int) -/

abbrev cu (n : Nat) : Cell := ⟨u64, (n : Int)⟩
abbrev two : NExpr := .cast u64 (.literal i32 2)
abbrev zeroU : NExpr := .cast u64 (.literal i32 0)
abbrev cCZ (nv : Nat) : NExpr :=
  .logical true (.binary bT .lt (.variable i32 (nv + 1)) (.literal i32 64))
    (.binary bT .eq (.divrem u64 true (.variable u64 (nv + 0)) two) zeroU)
abbrev aN (nv : Nat) : NStmt := .assign (nv + 0) u64 (.divrem u64 false (.variable u64 (nv + 0)) two)
abbrev aX (nv : Nat) : NStmt := .assign (nv + 1) i32 (.binary i32 .add (.variable i32 (nv + 1)) (.literal i32 1))
abbrev Bcz (nv : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (aN nv)) (.sequence (.primitive (aX nv)) Sk))) Sk
abbrev bodyCZ (nv : Nat) : Command :=
  .sequence (.primitive (.declare i32 true (.literal i32 0))) (.sequence (.whileLoop (cCZ nv) (Bcz nv))
    (.sequence (.primitive (.ret (.variable i32 (nv + 1)))) Sk))

theorem body_eqCZ : Proofs.CountrZeroInstance.countr_zero_u64.body = bodyCZ 0 := rfl

/-- The number of iterations when at most `f` more are allowed. -/
def cz : Nat → Nat → Nat
  | 0, _ => 0
  | f + 1, n => if n % 2 = 0 then cz f (n / 2) + 1 else 0

theorem cz_le (f n : Nat) : cz f n ≤ f := by
  induction f generalizing n with
  | zero => simp [cz]
  | succ f ih =>
    unfold cz
    split
    · have := ih (n / 2); omega
    · omega

/-- The result of the loop, characterized by divisibility. -/
theorem cz_spec (f n : Nat) (hn : n ≠ 0) (hf : n < 2 ^ f) :
    2 ^ (cz f n) ∣ n ∧ ¬ 2 ^ (cz f n + 1) ∣ n := by
  induction f generalizing n with
  | zero => simp at hf; omega
  | succ f ih =>
    unfold cz
    by_cases h : n % 2 = 0
    · rw [if_pos h]
      obtain ⟨m, hm⟩ : ∃ m, m = n / 2 := ⟨_, rfl⟩
      rw [← hm]
      have hn' : n = 2 * m := by omega
      have hn2 : m ≠ 0 := by omega
      have hf2 : m < 2 ^ f := by rw [Nat.pow_succ] at hf; omega
      obtain ⟨h1, h2⟩ := ih m hn2 hf2
      refine ⟨?_, ?_⟩
      · have e2 : 2 ^ (cz f m + 1) = 2 * 2 ^ cz f m := by rw [Nat.pow_succ]; ring
        rw [hn', e2]
        exact Nat.mul_dvd_mul_left 2 h1
      · intro hd
        apply h2
        obtain ⟨k, hk⟩ := hd
        refine ⟨k, ?_⟩
        have e : 2 * m = 2 * (2 ^ (cz f m + 1) * k) := by
          rw [← hn', hk, Nat.pow_succ 2 (cz f m + 1)]
          ring
        omega
    · rw [if_neg h]
      refine ⟨by simp, ?_⟩
      intro hd
      have : 2 ∣ n := by
        have h2 : 2 ∣ 2 ^ (0 + 1) := by simp
        exact Nat.dvd_trans h2 hd
      omega

theorem cz_zero (f : Nat) : cz f 0 = f := by
  induction f with
  | zero => rfl
  | succ f ih => simp [cz, ih]

theorem lit2_den (env : Nat → Ty → Option Int) : two.denote env = some 2 := by
  rw [den_cast, den_literal, if_pos (show i32.valid 2 = true from rfl), Option.bind_some, convert_u64]
  rfl

theorem lit0u_den (env : Nat → Ty → Option Int) : zeroU.denote env = some 0 := by
  rw [den_cast, den_literal, if_pos (show i32.valid 0 = true from rfl), Option.bind_some, convert_u64]
  rfl

theorem den_and (env : Nat → Ty → Option Int) (l r : NExpr) :
    (NExpr.logical true l r).denote env = (l.denote env).bind fun a =>
      if a == 0 then some 0 else (r.denote env).bind fun b => some (if b == 0 then 0 else 1) := by
  simp [NExpr.denote]

theorem cond_val (mv : MV) (hnv : mv.nv = 0) (P : List Cell) (vv : Nat → List Int) (n x : Nat) (hn : n < 18446744073709551616) (hx : x ≤ 64) :
    vdenM mv vv (penvN mv.nv (gS P [cu n, ci x])) (cCZ mv.nv) = some (if x < 64 ∧ n % 2 = 0 then 1 else 0) := by
  have hn' : u64.valid (n : Int) = true := u64_valid_nat n hn
  have ex := envs mv P [cu n, ci x] 1 (ci x) rfl (i32v x (by show x < 2147483648; omega))
  have en := envs mv P [cu n, ci x] 0 (cu n) rfl hn'
  have ex' : penvN mv.nv (gS P [cu n, ci x]) (mv.nv + 1) i32 = some (x : Int) := ex
  have en' : penvN mv.nv (gS P [cu n, ci x]) (mv.nv + 0) u64 = some (n : Int) := en
  have hr0 := rem_value n 2 (by omega) (by omega)
  have hr : checkedDivRem u64 true (n : Int) 2 = some ((n % 2 : Nat) : Int) := hr0
  have lit64 : (NExpr.literal i32 64).denote (penvN mv.nv (gS P [cu n, ci x])) = some 64 := by
    rw [den_literal, if_pos (show i32.valid 64 = true from rfl)]
  rw [vdenM_scalar _ _ _ _ rfl, den_and, den_binary, den_variable, ex', Option.bind_some, lit64, Option.bind_some]
  by_cases h : x < 64
  · have hb : bT.convert (binaryValue .lt (x : Int) 64) = some 1 := by
      simp [binaryValue, Ty.convert, bT, Ty.valid, h]
    rw [hb, Option.bind_some, if_neg (by decide), den_binary, den_divrem, den_variable, en', Option.bind_some, lit2_den,
      Option.bind_some, hr, Option.bind_some, lit0u_den, Option.bind_some]
    by_cases h2 : n % 2 = 0
    · have hb2 : bT.convert (binaryValue .eq ((n % 2 : Nat) : Int) 0) = some 1 := by
        simp [binaryValue, Ty.convert, bT, Ty.valid, h2]
      rw [hb2, Option.bind_some]
      simp [h, h2]
    · have hb2 : bT.convert (binaryValue .eq ((n % 2 : Nat) : Int) 0) = some 0 := by
        have : ((n % 2 : Nat) : Int) ≠ 0 := by omega
        simp [binaryValue, Ty.convert, bT, Ty.valid, this]
        omega
      rw [hb2, Option.bind_some]
      simp [h, h2]
  · have hb : bT.convert (binaryValue .lt (x : Int) 64) = some 0 := by
      simp [binaryValue, Ty.convert, bT, Ty.valid]; omega
    rw [hb, Option.bind_some, if_pos (by decide)]
    simp [h]

theorem lit64_den (env : Nat → Ty → Option Int) : (NExpr.literal i32 64).denote env = some 64 := by
  rw [den_literal, if_pos (show i32.valid 64 = true from rfl)]

set_option maxHeartbeats 16000000 in
/-- One iteration: `n = n / 2; x = x + 1;` (when `x < 64` and `n` is even). -/
theorem b_iter (mv : MV) (hnv : mv.nv = 0) (P : List Cell) (vv : Nat → List Int) (n x : Nat) (hn : n < 18446744073709551616)
    (hx : x < 64) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (Bcz mv.nv) (gS P [cu n, ci x]) vv = some r ∧ r.ret = none ∧
      r.ps = gS P [cu (n / 2), ci (x + 1)] ∧ r.vv = vv ∧ r.cost ≤ 100 ∧ r.need ≤ P.length + 40 ∧ r.wk = 0 := by
  have hn' : u64.valid (n : Int) = true := u64_valid_nat n hn
  have hq : n / 2 < 18446744073709551616 := by omega
  have hq' : u64.valid ((n / 2 : Nat) : Int) = true := u64_valid_nat _ hq
  have ex := envs mv P [cu n, ci x] 1 (ci x) rfl (i32v x (by show x < 2147483648; omega))
  have en := envs mv P [cu n, ci x] 0 (cu n) rfl hn'
  have ex' : penvN mv.nv (gS P [cu n, ci x]) (mv.nv + 1) i32 = some (x : Int) := ex
  have en' : penvN mv.nv (gS P [cu n, ci x]) (mv.nv + 0) u64 = some (n : Int) := en
  have hd0 := div_value n 2 (by omega) hn
  have hd : checkedDivRem u64 false (n : Int) 2 = some ((n / 2 : Nat) : Int) := hd0
  have e1 : vdenM mv vv (penvN mv.nv (gS P [cu n, ci x])) (.divrem u64 false (.variable u64 (mv.nv + 0)) two) =
      some ((n / 2 : Nat) : Int) := by
    rw [vdenM_scalar _ _ _ _ rfl, den_divrem, den_variable, en', Option.bind_some, lit2_den, Option.bind_some, hd]
  have s1 := gSM_assign mv P [cu n, ci x] vv 0 (by simp) u64 _ _ _ e1 (cu n) rfl rfl hn' (Ty.convert_of_valid _ _ hq')
  have a1 := (pexecM_prim mv fu (aN mv.nv) _ _).trans s1
  have ex2 : penvN mv.nv (gS P [⟨u64, ((n / 2 : Nat) : Int)⟩, ci x]) (mv.nv + 1) i32 = some (x : Int) :=
    envs mv P [⟨u64, ((n / 2 : Nat) : Int)⟩, ci x] 1 (ci x) rfl (i32v x (by show x < 2147483648; omega))
  have e2 := inc_val mv vv (penvN mv.nv (gS P [⟨u64, ((n / 2 : Nat) : Int)⟩, ci x])) (mv.nv + 1) x ex2
    (by show x + 1 < 2147483648; omega)
  have s2 := gSM_assign mv P [⟨u64, ((n / 2 : Nat) : Int)⟩, ci x] vv 1 (by simp) i32 _ _ _ e2 (ci x) rfl rfl
    (i32v x (by show x < 2147483648; omega)) (conv_signed i32 rfl rfl _ (i32v (x + 1) (by show x + 1 < 2147483648; omega)))
  have a2 := (pexecM_prim mv fu (aX mv.nv) _ _).trans s2
  have b2 := seqM_some a2 rfl (pexecM_skip mv fu _ _)
  have b1 := seqM_some a1 rfl b2
  obtain ⟨r1, hr1, hr1ps, hr1ret, hr1vv, hr1w, hr1c, hr1n⟩ : ∃ r1 : PRM,
      pexecM mv fu (.sequence (.primitive (aN mv.nv)) (.sequence (.primitive (aX mv.nv)) Sk)) (gS P [cu n, ci x]) vv = some r1 ∧
      r1.ps = gS P [cu (n / 2), ci (x + 1)] ∧ r1.ret = none ∧ r1.vv = vv ∧ r1.wk = 0 ∧ r1.cost ≤ 90 ∧ r1.need ≤ P.length + 40 := by
    refine ⟨_, b1, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_mem_len, gS_bs_len]
  have b0 := pexecM_scope mv fu _ _ _ _ hr1
  have tk := Proofs.PexecKit.scope_take (gS P [cu n, ci x]) (gS P [cu (n / 2), ci (x + 1)]) (by simp [gS_mem_len]) (by simp [gS_bs_len])
  rw [hr1ps] at b0
  simp only [tk] at b0
  have b00 := seqM_some b0 hr1ret (pexecM_skip mv fu _ _)
  refine ⟨_, b00, rfl, rfl, hr1vv, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly] at hr1c ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, gS_mem_len, gS_bs_len] at hr1n ⊢; omega
  · simp [hr1w]

theorem cz_succ (f n : Nat) : cz (f + 1) n = if n % 2 = 0 then cz f (n / 2) + 1 else 0 := rfl

set_option maxHeartbeats 16000000 in
/-- The loop `while (x < 64 && n % 2 == 0) {...}`. -/
theorem while_exec (mv : MV) (hnv : mv.nv = 0) (P : List Cell) (vv : Nat → List Int) :
    ∀ (f x n fu : Nat), x + f = 64 → n < 18446744073709551616 → f + 1 ≤ fu →
      ∃ res : PRM, pexecM mv fu (.whileLoop (cCZ mv.nv) (Bcz mv.nv)) (gS P [cu n, ci x]) vv = some res ∧ res.ret = none ∧
        res.ps = gS P [cu (n / 2 ^ cz f n), ci (x + cz f n)] ∧ res.vv = vv ∧
        res.cost ≤ 200 * f + 20 ∧ res.need ≤ P.length + 40 ∧ res.wk = 0 := by
  intro f
  induction f with
  | zero =>
    intro x n fu hxf hn hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond_val mv hnv P vv n x hn (by omega)
    rw [if_neg (by omega)] at hc
    rw [pexecM_while, hc]
    simp only [Bind.bind, Option.bind, ite_true]
    refine ⟨_, rfl, rfl, ?_, rfl, ?_, ?_, rfl⟩
    · simp [cz]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
    · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]
  | succ f ih =>
    intro x n fu hxf hn hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hc := cond_val mv hnv P vv n x hn (by omega)
    by_cases h2 : n % 2 = 0
    · rw [if_pos ⟨by omega, h2⟩] at hc
      obtain ⟨r1, h1, ret1, p1, vv1, c1, n1, w1⟩ := b_iter mv hnv P vv n x hn (by omega) (fu' + 1)
      obtain ⟨r2, h2', ret2, p2, vv2, c2, n2, w2⟩ := ih (x + 1) (n / 2) fu' (by omega) (by omega) (by omega)
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, int_one_ne, ite_false, h1, ret1, p1, vv1, h2']
      have hcs : cz (f + 1) n = cz f (n / 2) + 1 := by rw [cz_succ, if_pos h2]
      refine ⟨_, rfl, ret2, ?_, vv2, ?_, ?_, ?_⟩
      · rw [p2, hcs]
        have e1 : n / 2 / 2 ^ cz f (n / 2) = n / 2 ^ (cz f (n / 2) + 1) := by
          rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm (2 ^ _) 2]
        have e2 : x + 1 + cz f (n / 2) = x + (cz f (n / 2) + 1) := by omega
        rw [e1, e2]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at c1 c2 ⊢; omega
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at n1 n2 ⊢; omega
      · simp at w1 w2 ⊢; omega
    · rw [if_neg (fun h => h2 h.2)] at hc
      rw [pexecM_while, hc]
      simp only [Bind.bind, Option.bind, ite_true]
      have hcs : cz (f + 1) n = 0 := by rw [cz_succ, if_neg h2]
      refine ⟨_, rfl, rfl, ?_, rfl, ?_, ?_, rfl⟩
      · rw [hcs]; simp
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]
      · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len]

set_option maxHeartbeats 16000000 in
/-- The whole body of `countr_zero_u64`. -/
theorem body_exec (mv : MV) (hnv : mv.nv = 0) (P : List Cell) (vv : Nat → List Int) (n : Nat) (hn : n < 18446744073709551616)
    (fu : Nat) (hfu : 66 ≤ fu) :
    ∃ r : PRM, pexecM mv fu (bodyCZ mv.nv) (gS P [cu n]) vv = some r ∧ r.ret = some ((cz 64 n : Nat) : Int) ∧ r.vv = vv ∧
      (∃ cl : List Cell, r.ps = gS P cl) ∧ r.cost ≤ 13000 ∧ r.need ≤ P.length + 40 ∧ r.wk = 0 := by
  have d1 := gSM_decl mv P [cu n] vv i32 (.literal i32 0) 0 0
    (by rw [vdenM_scalar _ _ _ _ rfl]; rw [den_literal, if_pos (show i32.valid 0 = true from rfl)])
    (conv_signed i32 rfl rfl _ (show i32.valid 0 = true from rfl))
  have a1 := (pexecM_prim mv fu (.declare i32 true (.literal i32 0)) _ _).trans d1
  obtain ⟨rw_, hw, hret, hps, hvv, hc, hn', hwk⟩ := while_exec mv hnv P vv 64 0 n fu (by omega) hn (by omega)
  have hx : cz 64 n ≤ 64 := cz_le 64 n
  have ex := envs mv P [cu (n / 2 ^ cz 64 n), ci (0 + cz 64 n)] 1 (ci (0 + cz 64 n)) rfl
    (i32v (0 + cz 64 n) (by show 0 + cz 64 n < 2147483648; omega))
  have rr := pstmtM_ret_ok mv (gS P [cu (n / 2 ^ cz 64 n), ci (0 + cz 64 n)]) vv (.variable i32 (mv.nv + 1)) ((0 + cz 64 n : Nat) : Int)
    (by rw [vdenM_scalar _ _ _ _ rfl, den_variable]; exact ex)
  have e3 := seqM_ret (b := Sk) ((pexecM_prim mv fu _ _ _).trans rr) rfl
  have c2 := seqM_some hw hret (by rw [hps, hvv]; exact e3)
  have c1 := seqM_some a1 rfl (by exact c2)
  refine ⟨_, c1, ?_, rfl, ⟨_, rfl⟩, ?_, ?_, ?_⟩
  · simp
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at hc ⊢; omega
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_mem_len, gS_bs_len] at hn' ⊢; omega
  · simp at hwk ⊢; omega

end Proofs.CountrZeroExec
