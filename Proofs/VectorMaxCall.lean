import Proofs.VectorSumCall
import Proofs.Generated.VectorMax

namespace Proofs.VectorMaxCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.VecStraight Proofs.VecCall Proofs.VecKit
open Proofs.CppNestedFacts Proofs.IntSim Proofs.ScalarCall Proofs.VectorSumCall
open Proofs.CppState (Cell)

abbrev chkE : NExpr := .binary bT .ne (.size (.integer s64) (.local 0)) (.cast u64 (.literal i32 0))
abbrev rd0 : NExpr := .read s64 (.local 0) (.cast u64 (.literal i32 0))
abbrev rdI : NExpr := .read s64 (.local 0) (.cast u64 (.variable i32 2))
abbrev gtE : NExpr := .binary bT .gt rdI (.variable s64 1)
abbrev assignM : NStmt := .assign 1 s64 rdI
abbrev yesC : Command := .sequence (.scope (.sequence (.primitive assignM) (.primitive .skip))) (.primitive .skip)
abbrev brC : Command := .branch gtE yesC (.primitive .skip)
abbrev loopBodyM : Command := .sequence (.scope (.sequence brC (.primitive .skip)))
  (.sequence (.primitive Proofs.VectorSumCall.assignI) (.primitive .skip))
abbrev loopCM : Command := .whileLoop Proofs.VectorSumCall.condE loopBodyM
abbrev declM : NStmt := .declare s64 true rd0
abbrev declI1 : NStmt := .declare i32 true (.literal i32 1)
abbrev bodyCmdM : Command := .sequence (.primitive (.check chkE)) (.sequence (.primitive declM)
  (.sequence (.scope (.sequence (.primitive declI1) (.sequence loopCM (.primitive .skip))))
    (.sequence (.primitive (.ret (.variable s64 1))) (.primitive .skip))))

theorem body_eq : Proofs.VectorMaxInstance.vector_max_std_vector_long_long.body = bodyCmdM := rfl

theorem vwp_chk : vwp chkE = (6,6) := by decide
theorem vwp_rd0 : vwp rd0 = (5,5) := by decide
theorem vwp_gt : vwp gtE = (7,7) := by decide
theorem vwp_rdI : vwp rdI = (5,5) := by decide
theorem vwp_one : vwp (.literal i32 1) = (1,1) := by decide

def pmx (l : List Int) (k : Nat) : Int := (l.take k).foldl max (l.headD 0)

theorem pmx_succ (l : List Int) (i : Nat) (x : Int) (hx : l[i]? = some x) : pmx l (i+1) = max (pmx l i) x := by
  simp [pmx, List.take_succ, hx, List.foldl_append]

theorem rdI_val (vc : VCtx) (hty : vc.ty = s64) (P : List Cell) (m : Int) (i : Nat) (hn : vc.vec.length < 2147483648)
    (hm : s64.valid m = true) (x : Int) (hx : vc.vec[i]? = some x) (hxv : s64.valid x = true) :
    vden vc (penv1 (stS P m i)) rdI = some x := by
  have e2 := env_i P m i (i32_valid i (by have := (List.getElem?_eq_some_iff.mp hx).1; omega) (by have := (List.getElem?_eq_some_iff.mp hx).1; omega))
  have hrd : rdI.scalarOnly = false := rfl
  have hidx : (NExpr.cast u64 (.variable i32 2)).scalarOnly = true := rfl
  have hden : (NExpr.cast u64 (.variable i32 2)).denote (penv1 (stS P m i)) = some (i : Int) := by
    have hlt := (List.getElem?_eq_some_iff.mp hx).1
    rw [den_cast]
    show ((penv1 (stS P m i)) 2 i32).bind u64.convert = _
    rw [e2, Option.bind_some, convert_u64]
    simp
    exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [vden_read vc _ _ _ hrd, if_pos ⟨hty.symm, hidx⟩, hden, Option.bind_some]
  simp [elemAt, hx, hty, hxv]

theorem gt_val (vc : VCtx) (hty : vc.ty = s64) (P : List Cell) (m : Int) (i : Nat) (hn : vc.vec.length < 2147483648)
    (hm : s64.valid m = true) (x : Int) (hx : vc.vec[i]? = some x) (hxv : s64.valid x = true) :
    vden vc (penv1 (stS P m i)) gtE = some (if x > m then 1 else 0) := by
  have hr := rdI_val vc hty P m i hn hm x hx hxv
  have e1 := env_s P m i hm
  have hb : gtE.scalarOnly = false := rfl
  have hl : (NExpr.variable s64 1).scalarOnly = true := rfl
  have step1 := vden_binary vc (penv1 (stS P m i)) bT .gt rdI (.variable s64 1) hb
  have step3 : vden vc (penv1 (stS P m i)) (.variable s64 1) = some m := by
    rw [vden_scalar vc _ _ hl]; exact e1
  rw [step1, hr, step3, Option.bind_some, Option.bind_some]
  have : binaryValue .gt x m = if x > m then 1 else 0 := rfl
  rw [this]
  simp only [bT]; unfold Ty.convert
  by_cases hh : x > m <;> simp [hh]

theorem iterM (vc : VCtx) (hty : vc.ty = s64) (P : List Cell) (m : Int) (i : Nat) (hn : vc.vec.length < 2147483648)
    (hi : i < vc.vec.length) (hm : s64.valid m = true) (x : Int) (hx : vc.vec[i]? = some x)
    (hxv : s64.valid x = true) (fu : Nat) :
    ∃ r1, pexecV vc fu loopBodyM (stS P m i) = some r1 ∧ r1.ps = stS P (max m x) (i+1) ∧ r1.ret = none ∧
      r1.cost ≤ 20 ∧ r1.need ≤ P.length + 13 := by
  have hg := gt_val vc hty P m i hn hm x hx hxv
  have hrd := rdI_val vc hty P m i hn hm x hx hxv
  have bA : (stS P m i).bs[0]? = some ⟨P.length,true⟩ := by simp [stS]
  have cA : (stS P m i).mem[P.length]? = some ⟨s64,m⟩ := by
    have := Proofs.ModIntExec.get_tail P [⟨s64,m⟩,⟨i32,i⟩] 0
    simpa [stS] using this
  have hsz : ∀ m', (stS P m' i).mem.length = (stS P m i).mem.length ∧ (stS P m' i).bs.length = (stS P m i).bs.length := by
    intro m'; simp [stS]
  have hsize : ∀ m', (stS P m' i).mem.length + (stS P m' i).bs.length = P.length + 4 := fun m' => stS_size P m' i
  have core : ∃ r2, pexecV vc fu (.sequence brC (.primitive .skip)) (stS P m i) = some r2 ∧
      r2.ps = stS P (max m x) i ∧ r2.ret = none ∧ r2.cost ≤ 15 ∧ r2.need ≤ P.length + 13 := by
    by_cases hgt : x > m
    · rw [if_pos hgt] at hg
      have stA := Proofs.VecKit.pstmtV_assign_ok vc (stS P m i) 0 s64 rdI x hrd ⟨P.length,true⟩ ⟨s64,m⟩ bA cA rfl hm rfl x
        (conv_signed s64 rfl rfl _ hxv)
      rw [set_s] at stA
      have yes := Proofs.VecKit.pexecV_braced vc fu assignM (stS P m i) _ stA rfl (hsz x).1 (hsz x).2
      have br := Proofs.VecKit.pexecV_branch_true vc fu gtE yesC (.primitive .skip) (stS P m i) 1 hg (by decide) _ yes
      have sq := Proofs.VecKit.seqV_some br rfl (Proofs.VecKit.pexecV_skip vc fu (stS P x i))
      refine ⟨_, sq, ?_, rfl, ?_, ?_⟩
      · show stS P x i = _
        rw [Int.max_eq_right (by omega)]
      · simp [vwp_gt, vwp_rdI]
      · simp [vwp_gt, vwp_rdI, hsize]
    · rw [if_neg hgt] at hg
      have br := Proofs.VecKit.pexecV_branch_false vc fu gtE yesC (.primitive .skip) (stS P m i) hg _
        (Proofs.VecKit.pexecV_skip vc fu (stS P m i))
      have sq := Proofs.VecKit.seqV_some br rfl (Proofs.VecKit.pexecV_skip vc fu (stS P m i))
      refine ⟨_, sq, ?_, rfl, ?_, ?_⟩
      · show stS P m i = _
        rw [Int.max_eq_left (by omega)]
      · simp [vwp_gt]
      · simp [vwp_gt, hsize]
  obtain ⟨r2, h2, p2, ret2, c2, n2⟩ := core
  have s1 := Proofs.VecKit.pexecV_scope vc fu _ _ _ h2
  rw [p2] at s1
  have s2 := Proofs.PexecKit.scope_take (stS P m i) (stS P (max m x) i) (hsz _).1 (hsz _).2
  simp only [s2] at s1
  have hmx : s64.valid (max m x) = true := by
    rcases Int.le_total m x with h | h
    · rw [Int.max_eq_right h]; exact hxv
    · rw [Int.max_eq_left h]; exact hm
  have hi' := inc_val vc P (max m x) i (by omega)
  have bI : (stS P (max m x) i).bs[1]? = some ⟨P.length+1,true⟩ := by simp [stS]
  have cI : (stS P (max m x) i).mem[P.length+1]? = some ⟨i32,i⟩ := by
    have := Proofs.ModIntExec.get_tail P [⟨s64,max m x⟩,⟨i32,i⟩] 1
    simpa [stS] using this
  have stI := Proofs.VecKit.pstmtV_assign_ok vc (stS P (max m x) i) 1 i32 incE ((i : Int) + 1) hi' ⟨P.length+1,true⟩ ⟨i32,i⟩ bI cI rfl
    (show i32.valid (i : Int) = true from i32_valid _ (by omega) (by omega)) rfl ((i : Int) + 1)
    (conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega)))
  rw [set_i] at stI
  have b1 := (Proofs.VecKit.pexecV_prim vc fu Proofs.VectorSumCall.assignI (stS P (max m x) i)).trans stI
  have b2 := Proofs.VecKit.seqV_some b1 rfl (Proofs.VecKit.pexecV_skip vc fu (stS P (max m x) (i+1)))
  have c1 := Proofs.VecKit.seqV_some s1 ret2 b2
  refine ⟨_, c1, rfl, rfl, ?_, ?_⟩
  · simp [vwp_inc]
    omega
  · simp [vwp_inc, stS]
    omega


theorem pmx_mem (l : List Int) (hne : l ≠ []) : ∀ k, k ≤ l.length → pmx l k ∈ l := by
  intro k
  induction k with
  | zero =>
    intro _
    cases l with
    | nil => exact absurd rfl hne
    | cons a t => simp [pmx]
  | succ k ih =>
    intro hk
    have hlt : k < l.length := by omega
    obtain ⟨x, hx⟩ : ∃ x, l[k]? = some x := ⟨l[k], by simp [hlt]⟩
    rw [pmx_succ l k x hx]
    have hxm : x ∈ l := List.mem_of_getElem? hx
    have hp := ih (by omega)
    rcases Int.le_total (pmx l k) x with h | h
    · rw [Int.max_eq_right h]; exact hxm
    · rw [Int.max_eq_left h]; exact hp

theorem loop_runM (vc : VCtx) (hty : vc.ty = s64) (P : List Cell) (hn : vc.vec.length < 2147483648)
    (hne : vc.vec ≠ []) (hel : ∀ y ∈ vc.vec, s64.valid y = true) :
    ∀ (m i : Nat), 1 ≤ i → i + m = vc.vec.length → ∀ fu, m + 1 ≤ fu →
      ∃ r, pexecV vc fu loopCM (stS P (pmx vc.vec i) i) = some r ∧
        r.ps = stS P (pmx vc.vec vc.vec.length) vc.vec.length ∧ r.ret = none ∧ r.cost ≤ 27*m+7 ∧
        r.need ≤ P.length + 13 := by
  intro m
  induction m with
  | zero =>
    intro i h1 hi fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    have hc := cond_val vc hty P (pmx vc.vec i) i hn (by omega) (by omega)
    have hz : ¬ ((i : Int) < (vc.vec.length : Int)) := by omega
    rw [if_neg hz] at hc
    rw [Proofs.VecKit.pexecV_while, hc]
    have : i = vc.vec.length := by omega
    subst this
    simp only [Bind.bind, Option.bind, ite_true, vwp_cond]
    refine ⟨_, rfl, rfl, rfl, ?_, ?_⟩
    · simp
    · simp [stS]
  | succ m ih =>
    intro i h1 hi fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    have hlt : i < vc.vec.length := by omega
    have hc := cond_val vc hty P (pmx vc.vec i) i hn (by omega) (by omega)
    have ht : (i : Int) < (vc.vec.length : Int) := by omega
    rw [if_pos ht] at hc
    obtain ⟨x, hx⟩ : ∃ x, vc.vec[i]? = some x := ⟨vc.vec[i], by simp [hlt]⟩
    have hxv := hel x (List.mem_of_getElem? hx)
    have hm := hel _ (pmx_mem vc.vec hne i (by omega))
    obtain ⟨r1, h1', p1, ret1, c1, n1⟩ := iterM vc hty P (pmx vc.vec i) i hn hlt hm x hx hxv (fu'+1)
    have hps := pmx_succ vc.vec i x hx
    rw [← hps] at p1
    have p1' : r1.ps = stS P (pmx vc.vec (i+1)) ((i+1 : Nat) : Int) := by rw [p1]; simp
    obtain ⟨r2, h2, p2, ret2, c2, n2⟩ := ih (i+1) (by omega) (by omega) fu' (by omega)
    rw [Proofs.VecKit.pexecV_while, hc]
    simp only [Bind.bind, Option.bind, h1', ret1, p1', h2, vwp_cond]
    refine ⟨⟨r2.ps, r2.ret, 6+1+r1.cost+r2.cost, max ((stS P (pmx vc.vec i) i).mem.length +
      (stS P (pmx vc.vec i) i).bs.length + 6 + 2) (max r1.need r2.need)⟩, by simp, ?_, ?_, ?_, ?_⟩
    · exact p2
    · exact ret2
    · simp; omega
    · simp [stS_size, n1, n2]; omega


theorem pmx_one (l : List Int) (x0 : Int) (h0 : l[0]? = some x0) : pmx l 1 = x0 := by
  have := pmx_succ l 0 x0 h0
  have h : pmx l 0 = x0 := by
    cases l with
    | nil => simp at h0
    | cons a t => simp at h0; simp [pmx, h0]
  simpa [h] using this

theorem check_val (vc : VCtx) (hty : vc.ty = s64) (P : List Cell) (hn : vc.vec.length < 2147483648)
    (hne : vc.vec ≠ []) : vden vc (penv1 ⟨P,[]⟩) chkE = some 1 := by
  have hb : chkE.scalarOnly = false := rfl
  have hsz : vden vc (penv1 ⟨P,[]⟩) (.size (.integer s64) (.local 0)) = some (vc.vec.length : Int) := by
    have hr : (NExpr.size (.integer s64) (.local 0)).scalarOnly = false := rfl
    simp [vden, hr, hty]
  have hr2 : (NExpr.cast u64 (.literal i32 0)).scalarOnly = true := rfl
  have hz : vden vc (penv1 ⟨P,[]⟩) (.cast u64 (.literal i32 0)) = some 0 := by
    rw [vden_scalar vc _ _ hr2, den_cast]
    show ((NExpr.literal i32 0).denote (penv1 ⟨P,[]⟩)).bind u64.convert = _
    have h0 : i32.valid 0 = true := rfl
    rw [den_literal, if_pos h0, Option.bind_some, convert_u64]
    rfl
  have step1 := vden_binary vc (penv1 ⟨P,[]⟩) bT .ne (.size (.integer s64) (.local 0)) (.cast u64 (.literal i32 0)) hb
  rw [step1, hsz, hz, Option.bind_some, Option.bind_some]
  have hl : 0 < vc.vec.length := List.length_pos_iff.mpr hne
  have : binaryValue .ne (vc.vec.length : Int) 0 = 1 := by
    show (if (vc.vec.length : Int) != 0 then 1 else 0) = 1
    have : ((vc.vec.length : Int) != 0) = true := by simp; omega
    rw [this]; rfl
  rw [this]
  rfl

theorem rd0_val (vc : VCtx) (hty : vc.ty = s64) (P : List Cell) (x0 : Int) (hx : vc.vec[0]? = some x0)
    (hxv : s64.valid x0 = true) (ps : PS) : vden vc (penv1 ps) rd0 = some x0 := by
  have hrd : rd0.scalarOnly = false := rfl
  have hidx : (NExpr.cast u64 (.literal i32 0)).scalarOnly = true := rfl
  have hden : (NExpr.cast u64 (.literal i32 0)).denote (penv1 ps) = some ((0 : Nat) : Int) := by
    rw [den_cast]
    show ((NExpr.literal i32 0).denote (penv1 ps)).bind u64.convert = _
    have h0 : i32.valid 0 = true := rfl
    rw [den_literal, if_pos h0, Option.bind_some, convert_u64]
    rfl
  rw [vden_read vc _ _ _ hrd, if_pos ⟨hty.symm, hidx⟩, hden, Option.bind_some]
  simp [elemAt, hx, hty, hxv]

theorem vwp_var1 : vwp (.variable s64 1) = (1,1) := by decide

theorem body_execM (vc : VCtx) (hty : vc.ty = s64) (P : List Cell) (hn : vc.vec.length < 2147483648)
    (hne : vc.vec ≠ []) (hel : ∀ y ∈ vc.vec, s64.valid y = true) (fu : Nat) (hfu : vc.vec.length + 1 ≤ fu) :
    ∃ r, pexecV vc fu bodyCmdM ⟨P,[]⟩ = some r ∧ r.ret = some (pmx vc.vec vc.vec.length) ∧
      r.ps = ⟨P ++ [⟨s64,pmx vc.vec vc.vec.length⟩],[⟨P.length,true⟩]⟩ ∧
      r.cost ≤ 27*vc.vec.length + 30 ∧ r.need ≤ P.length + 13 := by
  have hl : 0 < vc.vec.length := List.length_pos_iff.mpr hne
  obtain ⟨x0, hx0⟩ : ∃ x0, vc.vec[0]? = some x0 := ⟨vc.vec[0], by simp [hl]⟩
  have hx0v := hel x0 (List.mem_of_getElem? hx0)
  -- the emptiness check
  have ck := Proofs.VecKit.pstmtV_check_ok vc ⟨P,[]⟩ chkE 1 (check_val vc hty P hn hne) (by decide)
  have e0 := (Proofs.VecKit.pexecV_prim vc fu (.check chkE) _).trans ck
  -- m := x[0]
  have d1 := Proofs.VecKit.pstmtV_declare_ok vc ⟨P,[]⟩ s64 true rd0 x0 (rd0_val vc hty P x0 hx0 hx0v _) x0
    (conv_signed s64 rfl rfl _ hx0v)
  have e1 := (Proofs.VecKit.pexecV_prim vc fu declM _).trans d1
  -- i := 1
  have hv2 : vden vc (penv1 (⟨P ++ [(⟨s64,x0⟩ : Cell)],[⟨P.length,true⟩]⟩ : PS)) (.literal i32 1) = some 1 := by
    have h1 : i32.valid 1 = true := rfl
    rw [vden_scalar vc _ _ rfl, den_literal, if_pos h1]
  have d2 := Proofs.VecKit.pstmtV_declare_ok vc (⟨P ++ [(⟨s64,x0⟩ : Cell)],[⟨P.length,true⟩]⟩ : PS) i32 true (.literal i32 1) 1 hv2 1
    (conv_signed i32 rfl rfl _ rfl)
  have st0 : (⟨(P ++ [(⟨s64,x0⟩ : Cell)]) ++ [(⟨i32,1⟩ : Cell)],[⟨P.length,true⟩] ++ [⟨(P ++ [(⟨s64,x0⟩ : Cell)]).length,true⟩]⟩ : PS) =
      stS P (pmx vc.vec 1) ((1 : Nat) : Int) := by
    rw [pmx_one vc.vec x0 hx0]
    simp [stS]
  rw [st0] at d2
  obtain ⟨rL, hL, pL, retL, cL, nL⟩ := loop_runM vc hty P hn hne hel (vc.vec.length - 1) 1 (Nat.le_refl _) (by omega) fu
    (by omega)
  have hS := hel _ (pmx_mem vc.vec hne vc.vec.length (Nat.le_refl _))
  have f2 := Proofs.VecKit.seqV_some hL retL (Proofs.VecKit.pexecV_skip vc fu rL.ps)
  have d2' := (Proofs.VecKit.pexecV_prim vc fu declI1 _).trans d2
  have f3 := Proofs.VecKit.seqV_some d2' rfl f2
  have f4 := Proofs.VecKit.pexecV_scope vc fu _ _ _ f3
  have take_eq : (⟨(stS P (pmx vc.vec vc.vec.length) vc.vec.length).mem.take (P ++ [(⟨s64,x0⟩ : Cell)]).length,
      (stS P (pmx vc.vec vc.vec.length) vc.vec.length).bs.take [(⟨P.length,true⟩ : CppState.Binding)].length⟩ : PS) =
      (⟨P ++ [(⟨s64,pmx vc.vec vc.vec.length⟩ : Cell)],[⟨P.length,true⟩]⟩ : PS) := by
    simp [stS, List.take_append, List.take_of_length_le]
  rw [pL] at f4
  simp only [take_eq] at f4
  have hret : vden vc (penv1 (⟨P ++ [(⟨s64,pmx vc.vec vc.vec.length⟩ : Cell)],[⟨P.length,true⟩]⟩ : PS)) (.variable s64 1) =
      some (pmx vc.vec vc.vec.length) := by
    rw [vden_scalar vc _ _ rfl]
    show penv _ 0 s64 = _
    refine Proofs.PexecKit.penv_ok _ 0 s64 (⟨P.length,true⟩ : CppState.Binding) (⟨s64,pmx vc.vec vc.vec.length⟩ : Cell) rfl ?_ rfl hS
    show (P ++ [(⟨s64,pmx vc.vec vc.vec.length⟩ : Cell)])[P.length]? = _
    simp
  have g1 := Proofs.VecKit.pstmtV_ret_ok vc _ _ _ hret
  have g2 := (Proofs.VecKit.pexecV_prim vc fu (.ret (.variable s64 1)) _).trans g1
  have g3 := Proofs.VecKit.seqV_ret (b := .primitive .skip) g2 rfl
  have h4 := Proofs.VecKit.seqV_some f4 rfl g3
  have h5 := Proofs.VecKit.seqV_some e1 rfl h4
  have h6 := Proofs.VecKit.seqV_some e0 rfl h5
  refine ⟨_, h6, rfl, rfl, ?_, ?_⟩
  · simp [vwp_var1, vwp_chk, vwp_rd0, vwp_one, vwp_cond]
    omega
  · simp [vwp_var1, vwp_chk, vwp_rd0, vwp_one, stS]
    omega

theorem pmx_ge (l : List Int) : ∀ k, k ≤ l.length → ∀ j, j < k → ∀ y, l[j]? = some y → y ≤ pmx l k := by
  intro k
  induction k with
  | zero => intro _ j hj; omega
  | succ k ih =>
    intro hk j hj y hy
    obtain ⟨x, hx⟩ : ∃ x, l[k]? = some x := ⟨l[k], by simp [show k < l.length by omega]⟩
    rw [pmx_succ l k x hx]
    by_cases hjk : j < k
    · have := ih (by omega) j hjk y hy
      exact Int.le_trans this (Int.le_max_left _ _)
    · have : j = k := by omega
      subst this
      rw [hx] at hy
      cases hy
      exact Int.le_max_right _ _

set_option maxHeartbeats 4000000 in
theorem vector_max_correct (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : VOK caller vslot vb V vsc m vbuf) (vec : List Int) (hitems : vbuf.items = vec.map Value.integer)
    (hne : vec ≠ []) (hn : vec.length < 2147483648) (hel : ∀ y ∈ vec, s64.valid y = true) :
    ∃ Sinit fuel res M, prepare caller Proofs.VectorMaxInstance.vector_max_std_vector_long_long.parameters [.vectorReference vslot] = some Sinit ∧
      Proofs.VectorMaxInstance.vector_max_std_vector_long_long.callFuel fuel caller [.vectorReference vslot] = .finished (res,.scalar M) ∧
      M ∈ vec ∧ (∀ y ∈ vec, y ≤ M) ∧
      ScalarPost2 caller Sinit res 0 (27*vec.length+40) caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prepare_vs caller _ rfl ok
  let vc : VCtx := ⟨s64,false,m,V,vsc,vbuf,vec,hitems,by simp,by omega,caller.frame.state.liveSpace,
    caller.frame.state.storage.work,caller.scope+1,caller.frame.state.storage.objects.length⟩
  have hty : vc.ty = s64 := rfl
  have hvec : vc.vec = vec := rfl
  have fvS : FV vc Sinit.frame := by
    rw [sFrame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag⟩
    intro owner k h
    have := ok.strict owner k h
    show k < caller.scope+1
    omega
  obtain ⟨r,hexec,hret,hrps,hcost,hneed⟩ := body_execM vc hty (callerP caller) (by simpa [hvec] using hn)
    (by simpa [hvec] using hne) (by simpa [hvec] using hel) (vec.length+1) (by simp [hvec])
  simp only [hvec] at hexec hret hrps hcost
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left
  have hmem := pmx_mem vec hne vec.length (Nat.le_refl _)
  have hSv : s64.valid (pmx vec vec.length) = true := hel _ hmem
  have hvl : vc.vec.length = vec.length := rfl
  have hpost := call_vec vc caller Proofs.VectorMaxInstance.vector_max_std_vector_long_long [.vectorReference vslot] Sinit (callerP caller) []
    hprep (by rw [sSlots]; rfl) (by rw [sMem]) sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fvS rfl rfl rfl rfl
    (by omega) (by simp [hlen]) (by rw [takeM]) ok.base (by decide) (vec.length+1) r
    (by rw [body_eq]; exact hexec) (pmx vec vec.length) hret s64 rfl hSv (by omega) (by simp) 0 (27*vec.length+40)
    (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,pmx vec vec.length,hprep,hrun,hmem,?_,?_⟩
  · intro y hy
    obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hy
    exact pmx_ge vec vec.length (Nat.le_refl _) j hj y (by simp [hj, hjy])
  · have hs : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
      rw [hrps]
      simp only [callerP, List.append_assoc, List.take_left]
    rw [hs] at post; exact post

end Proofs.VectorMaxCall