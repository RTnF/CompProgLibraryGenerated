import Proofs.VectorFillCall

namespace Proofs.PrefixSumsCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.VecStraight Proofs.VecCall Proofs.VecKit
open Proofs.CppNestedFacts Proofs.IntSim Proofs.ScalarCall Proofs.VecWrite Proofs.VecWriteCall Proofs.VecKitW
open Proofs.QuotientSearch Proofs.VectorFillCall
open Proofs.VectorSumCall (psum psum_succ i32_valid conv_signed)
open Proofs.CppState (Cell)

-- The callee state: only the counter `i` (the vector parameter is not a scalar cell).
def stI (P : List Cell) (i : Int) : PS := ⟨P ++ [⟨i32,i⟩],[⟨P.length,true⟩]⟩

theorem stI_size (P : List Cell) (i : Int) : (stI P i).mem.length + (stI P i).bs.length = P.length + 2 := by
  simp [stI]

theorem env_i1 (P : List Cell) (i : Int) (hi : i32.valid i = true) : penv1 (stI P i) 1 i32 = some i := by
  show penv (stI P i) 0 i32 = some i
  refine Proofs.PexecKit.penv_ok _ 0 i32 ⟨P.length,true⟩ ⟨i32,i⟩ rfl ?_ rfl hi
  show (P ++ [⟨i32,i⟩])[P.length]? = _
  have := Proofs.ModIntExec.get_tail P [⟨i32,i⟩] 0
  simpa using this

theorem convS (v : Int) (h : s64.valid v = true) : s64.convert v = some v := conv_signed s64 rfl rfl v h

abbrev bT : Ty := ⟨1, false, true⟩
abbrev condE1 : NExpr := .binary bT .lt (.variable i32 1) (.cast i32 (.size (.integer s64) (.local 0)))
abbrev incE1 : NExpr := .binary i32 .add (.variable i32 1) (.literal i32 1)
abbrev assignI1 : NStmt := .assign 1 i32 incE1
abbrev rdPrev : NExpr := .read s64 (.local 0) (.cast u64 (.binary i32 .sub (.variable i32 1) (.literal i32 1)))
abbrev rdCur : NExpr := .read s64 (.local 0) (.cast u64 (.variable i32 1))
abbrev sumE : NExpr := .binary s64 .add rdCur rdPrev
abbrev writeP : NStmt := .write (.local 0) s64 (.cast u64 (.variable i32 1)) sumE
abbrev loopBodyP : Command := .sequence (.scope (.sequence (.primitive writeP) (.primitive .skip)))
  (.sequence (.primitive assignI1) (.primitive .skip))
abbrev loopCP : Command := .whileLoop condE1 loopBodyP
abbrev declI1 : NStmt := .declare i32 true (.literal i32 1)
abbrev bodyCmdP : Command := .sequence (.scope (.sequence (.primitive declI1)
  (.sequence loopCP (.primitive .skip)))) (.primitive .skip)


theorem vwp_c1 : vwp condE1 = (6,6) := by decide
theorem vwp_inc1 : vwp incE1 = (3,3) := by decide
theorem vwp_sum : vwp sumE = (13,13) := by decide
theorem vwp_idx1 : vwp (NExpr.cast u64 (.variable i32 1)) = (2,2) := by decide
theorem vwp_lit1 : vwp (.literal i32 1) = (1,1) := by decide

theorem vdenL_binary (ty : Ty) (vec : List Int) (env : Nat → Ty → Option Int) (t : Ty) (op : Binary) (l r : NExpr)
    (h : (NExpr.binary t op l r).scalarOnly = false) :
    vdenL ty vec env (.binary t op l r) =
      (vdenL ty vec env l).bind fun a => (vdenL ty vec env r).bind fun b => t.convert (binaryValue op a b) := by
  rw [vdenL, if_neg (by rw [h]; decide)]

theorem vdenL_read (ty : Ty) (vec : List Int) (env : Nat → Ty → Option Int) (t : Ty) (index : NExpr)
    (h : (NExpr.read t (.local 0) index).scalarOnly = false) :
    vdenL ty vec env (.read t (.local 0) index) =
      if t = ty ∧ index.scalarOnly = true then (index.denote env).bind (elemAtL ty vec) else none := by
  rw [vdenL, if_neg (by rw [h]; decide)]

theorem vdenL_cast (ty : Ty) (vec : List Int) (env : Nat → Ty → Option Int) (t : Ty) (op : NExpr)
    (h : (NExpr.cast t op).scalarOnly = false) :
    vdenL ty vec env (.cast t op) = (vdenL ty vec env op).bind t.convert := by
  rw [vdenL, if_neg (by rw [h]; decide)]

theorem cond1_valL (vec : List Int) (P : List Cell) (i : Nat) (hn : vec.length < 2147483648) (hi : i ≤ vec.length + 1) (hi2 : i < 2147483648) :
    vdenL s64 vec (penv1 (stI P i)) condE1 = some (if (i : Int) < (vec.length : Int) then 1 else 0) := by
  have e1 := env_i1 P i (i32_valid i (by omega) (by omega))
  have hl : (NExpr.variable i32 1).scalarOnly = true := rfl
  have hc : condE1.scalarOnly = false := rfl
  have hr2 : (NExpr.cast i32 (.size (.integer s64) (.local 0))).scalarOnly = false := rfl
  have hn' : i32.convert (vec.length : Int) = some (vec.length : Int) :=
    conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega))
  have hr : (NExpr.size (.integer s64) (.local 0)).scalarOnly = false := rfl
  have hsz : vdenL s64 vec (penv1 (stI P i)) (.size (.integer s64) (.local 0)) = some (vec.length : Int) := by
    simp [vdenL, hr]
  have hb : bT.convert (if (i : Int) < (vec.length : Int) then 1 else 0) = some (if (i : Int) < (vec.length : Int) then 1 else 0) := by
    simp only [bT]; unfold Ty.convert; by_cases hh : (i : Int) < (vec.length : Int) <;> simp [hh]
  have step1 := vdenL_binary s64 vec (penv1 (stI P i)) bT .lt (.variable i32 1) (.cast i32 (.size (.integer s64) (.local 0))) hc
  have step2 : vdenL s64 vec (penv1 (stI P i)) (.cast i32 (.size (.integer s64) (.local 0))) = some (vec.length : Int) := by
    rw [vdenL_cast s64 vec _ _ _ hr2, hsz, Option.bind_some, hn']
  have step3 : vdenL s64 vec (penv1 (stI P i)) (.variable i32 1) = some (i : Int) := by
    rw [vdenL_scalar _ _ _ _ hl, den_variable]; exact e1
  rw [step1, step2, step3, Option.bind_some, Option.bind_some]
  have : binaryValue .lt (i : Int) (vec.length : Int) = if (i : Int) < (vec.length : Int) then 1 else 0 := rfl
  rw [this]; exact hb

theorem idxcur (vec : List Int) (P : List Cell) (i : Nat) (hn : i < 2147483648) :
    (NExpr.cast u64 (.variable i32 1)).denote (penv1 (stI P i)) = some (i : Int) := by
  have e1 := env_i1 P i (i32_valid i (by omega) (by omega))
  rw [den_cast]
  show ((penv1 (stI P i)) 1 i32).bind u64.convert = _
  rw [e1, Option.bind_some, convert_u64]
  simp
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem idxprev (vec : List Int) (P : List Cell) (i : Nat) (h1 : 1 ≤ i) (hn : i < 2147483648) :
    (NExpr.cast u64 (.binary i32 .sub (.variable i32 1) (.literal i32 1))).denote (penv1 (stI P i)) = some ((i - 1 : Nat) : Int) := by
  have e1 := env_i1 P i (i32_valid i (by omega) (by omega))
  rw [den_cast, den_binary, den_variable, e1, den_literal, if_pos (show i32.valid 1 = true from rfl)]
  simp only [Option.bind_some]
  have : binaryValue .sub (i : Int) 1 = (i : Int) - 1 := rfl
  rw [this]
  rw [conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega)), Option.bind_some, convert_u64]
  simp
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  omega

-- The contents after the first `i` positions have been replaced by their prefix sums.
def pfx (vec : List Int) (i : Nat) : List Int := (List.range i).map (fun k => psum vec (k+1)) ++ vec.drop i

theorem pfx_length (vec : List Int) (i : Nat) (hi : i ≤ vec.length) : (pfx vec i).length = vec.length := by
  simp [pfx]; omega

theorem pfx_get_prev (vec : List Int) (i : Nat) (h1 : 1 ≤ i) (hi : i ≤ vec.length) :
    (pfx vec i)[i-1]? = some (psum vec i) := by
  have hlen : ((List.range i).map (fun k => psum vec (k+1))).length = i := by simp
  unfold pfx
  rw [List.getElem?_append_left (by omega)]
  simp [List.getElem?_map, List.getElem?_range, show i - 1 < i by omega]
  congr 1; omega

theorem pfx_get_cur (vec : List Int) (i : Nat) (hi : i < vec.length) : (pfx vec i)[i]? = vec[i]? := by
  unfold pfx
  rw [List.getElem?_append_right (by simp)]
  simp

theorem pfx_set (vec : List Int) (i : Nat) (hi : i < vec.length) :
    (pfx vec i).set i (psum vec (i+1)) = pfx vec (i+1) := by
  have hd : vec.drop i = vec[i] :: vec.drop (i+1) := List.drop_eq_getElem_cons hi
  have h1 : ((List.range i).map (fun k => psum vec (k+1)) ++ vec.drop i).set i (psum vec (i+1)) =
      (List.range i).map (fun k => psum vec (k+1)) ++ (vec.drop i).set 0 (psum vec (i+1)) := by
    have := List.set_append_right (s := (List.range i).map (fun k => psum vec (k+1))) (t := vec.drop i) i (psum vec (i+1)) (by simp)
    simpa using this
  unfold pfx
  rw [h1, hd, List.set_cons_zero]
  simp [List.range_succ]

theorem pfx_one (vec : List Int) (h : 1 ≤ vec.length) : pfx vec 1 = vec := by
  have hd : vec.drop 1 = vec.tail := by simp
  obtain ⟨a, t, rfl⟩ : ∃ a t, vec = a :: t := by
    cases vec with
    | nil => simp at h
    | cons a t => exact ⟨a, t, rfl⟩
  simp [pfx, psum]

theorem sum_valL (vec : List Int) (P : List Cell) (i : Nat) (hn : vec.length < 2147483648)
    (h1 : 1 ≤ i) (hi : i < vec.length) (hel : ∀ y ∈ vec, s64.valid y = true)
    (hpre : ∀ k ≤ vec.length, s64.valid (psum vec k) = true) :
    vdenL s64 (pfx vec i) (penv1 (stI P i)) sumE = some (psum vec (i+1)) := by
  have hlen := pfx_length vec i (by omega)
  obtain ⟨x, hx⟩ : ∃ x, vec[i]? = some x := ⟨vec[i], by simp [hi]⟩
  have hxv := hel x (List.mem_of_getElem? hx)
  have hps := psum_succ vec i x hx
  have hcur : (pfx vec i)[i]? = some x := by rw [pfx_get_cur vec i hi]; exact hx
  have hprev : (pfx vec i)[i-1]? = some (psum vec i) := pfx_get_prev vec i h1 (by omega)
  have hpv := hpre i (by omega)
  have hb : sumE.scalarOnly = false := rfl
  have hrc : rdCur.scalarOnly = false := rfl
  have hrp : rdPrev.scalarOnly = false := rfl
  have vcur : vdenL s64 (pfx vec i) (penv1 (stI P i)) rdCur = some x := by
    rw [vdenL_read _ _ _ _ _ hrc, if_pos ⟨rfl, rfl⟩, idxcur vec P i (by omega), Option.bind_some]
    simp [elemAtL, hcur, hxv]
  have vprev : vdenL s64 (pfx vec i) (penv1 (stI P i)) rdPrev = some (psum vec i) := by
    rw [vdenL_read _ _ _ _ _ hrp, if_pos ⟨rfl, rfl⟩, idxprev vec P i h1 (by omega), Option.bind_some]
    simp [elemAtL, hprev, hpv]
  rw [vdenL_binary _ _ _ _ _ _ _ hb, vcur, vprev, Option.bind_some, Option.bind_some]
  have hbv : binaryValue .add x (psum vec i) = psum vec (i+1) := by
    show x + psum vec i = _
    rw [hps]; omega
  rw [hbv]
  exact convS _ (hpre (i+1) (by omega))

theorem set_i1 (P : List Cell) (i i' : Int) :
    (⟨(stI P i).mem.set P.length ⟨i32,i'⟩,(stI P i).bs⟩ : PS) = stI P i' := by
  simp [stI, List.set_append_right]

theorem inc1_val (vec' : List Int) (P : List Cell) (i : Nat) (hi : i < 2147483647) :
    vdenL s64 vec' (penv1 (stI P i)) incE1 = some ((i : Int)+1) := by
  have e1 := env_i1 P i (i32_valid i (by omega) (by omega))
  have hl : incE1.scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hl]
  show ((penv1 (stI P i)) 1 i32).bind (fun a => ((NExpr.literal i32 1).denote (penv1 (stI P i))).bind fun b =>
    i32.convert (binaryValue .add a b)) = _
  rw [e1, Option.bind_some]
  have : (NExpr.literal i32 1).denote (penv1 (stI P i)) = some 1 := by
    rw [den_literal]; rw [if_pos (i32_valid 1 (by omega) (by omega))]
  rw [this, Option.bind_some]
  have hv : binaryValue .add (i : Int) 1 = (i : Int) + 1 := rfl
  rw [hv]
  exact conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega))

theorem iterP (P : List Cell) (vec : List Int) (i : Nat) (hn : vec.length < 2147483648) (h1 : 1 ≤ i)
    (hi : i < vec.length) (hel : ∀ y ∈ vec, s64.valid y = true)
    (hpre : ∀ k ≤ vec.length, s64.valid (psum vec k) = true) (fu : Nat) :
    ∃ r1, pexecW s64 fu loopBodyP (stI P i) (pfx vec i) = some r1 ∧ r1.ps = stI P (i+1) ∧
      r1.vec = pfx vec (i+1) ∧ r1.ret = none ∧ r1.cost ≤ 24 ∧ r1.need ≤ P.length + 40 ∧ r1.wk = 1 := by
  have hlen := pfx_length vec i (by omega)
  have hval := sum_valL vec P i hn h1 hi hel hpre
  have hp : vdenL s64 (pfx vec i) (penv1 (stI P i)) (NExpr.cast u64 (.variable i32 1)) = some (i : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl]; exact idxcur vec P i (by omega)
  have w := pstmtW_write_ok s64 (stI P i) (pfx vec i) (NExpr.cast u64 (.variable i32 1)) sumE (psum vec (i+1)) i
    hval hp (by omega) (hpre (i+1) (by omega))
  rw [pfx_set vec i hi] at w
  have a1 := (pexecW_prim s64 fu writeP _ _).trans w
  have a2 := seqW_some a1 rfl (pexecW_skip s64 fu (stI P i) (pfx vec (i+1)))
  have a3 := pexecW_scope s64 fu _ _ _ _ a2
  have a4 := Proofs.PexecKit.scope_take (stI P i) (stI P i) rfl rfl
  simp only [a4] at a3
  have hinc := inc1_val (pfx vec (i+1)) P i (by omega)
  have bI : (stI P i).bs[0]? = some ⟨P.length,true⟩ := by simp [stI]
  have cI : (stI P i).mem[P.length]? = some ⟨i32,i⟩ := by
    have := Proofs.ModIntExec.get_tail P [⟨i32,i⟩] 0
    simpa [stI] using this
  have stI' := pstmtW_assign_ok s64 (stI P i) (pfx vec (i+1)) 0 i32 incE1 ((i : Int)+1) hinc
    ⟨P.length,true⟩ ⟨i32,i⟩ bI cI rfl (show i32.valid (i : Int) = true from i32_valid _ (by omega) (by omega)) rfl
    ((i : Int)+1) (conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega)))
  rw [set_i1] at stI'
  have b1 := (pexecW_prim s64 fu assignI1 _ _).trans stI'
  have b2 := seqW_some b1 rfl (pexecW_skip s64 fu (stI P (i+1)) (pfx vec (i+1)))
  have c1 := seqW_some a3 rfl b2
  refine ⟨_, c1, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · simp [stI]
  · simp [vwp_sum, vwp_inc1, vwp_idx1]
  · simp [vwp_sum, vwp_inc1, vwp_idx1, stI, NExpr.nodes, Container.nodes]
  · simp

theorem loop_runP (P : List Cell) (vec : List Int) (hn : vec.length < 2147483648)
    (hel : ∀ y ∈ vec, s64.valid y = true) (hpre : ∀ k ≤ vec.length, s64.valid (psum vec k) = true) :
    ∀ (m i : Nat), 1 ≤ i → i + m = vec.length → ∀ fu, m + 1 ≤ fu →
      ∃ r, pexecW s64 fu loopCP (stI P i) (pfx vec i) = some r ∧
        r.ps = stI P vec.length ∧ r.vec = pfx vec vec.length ∧ r.ret = none ∧
        r.cost ≤ 31*m+7 ∧ r.need ≤ P.length + 40 ∧ r.wk = m := by
  intro m
  induction m with
  | zero =>
    intro i h1 hi fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    have hc := cond1_valL (pfx vec i) P i (by rw [pfx_length vec i (by omega)]; exact hn)
      (by rw [pfx_length vec i (by omega)]; omega) (by omega)
    rw [pfx_length vec i (by omega)] at hc
    have hz : ¬ ((i : Int) < (vec.length : Int)) := by omega
    rw [if_neg hz] at hc
    rw [pexecW_while, hc]
    have : i = vec.length := by omega
    subst this
    simp only [Bind.bind, Option.bind, ite_true, vwp_c1]
    refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
    · simp
    · simp [stI]
  | succ m ih =>
    intro i h1 hi fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    have hlt : i < vec.length := by omega
    have hlen := pfx_length vec i (by omega)
    have hc := cond1_valL (pfx vec i) P i (by rw [hlen]; exact hn) (by rw [hlen]; omega) (by omega)
    rw [hlen] at hc
    have ht : (i : Int) < (vec.length : Int) := by omega
    rw [if_pos ht] at hc
    obtain ⟨r1, h1', p1, v1, ret1, c1, n1, w1⟩ := iterP P vec i hn h1 hlt hel hpre (fu'+1)
    have p1' : r1.ps = stI P ((i+1 : Nat) : Int) := by rw [p1]; simp
    obtain ⟨r2, h2, p2, v2, ret2, c2, n2, w2⟩ := ih (i+1) (by omega) (by omega) fu' (by omega)
    rw [pexecW_while, hc]
    simp only [Bind.bind, Option.bind, h1', ret1, p1', v1, h2, vwp_c1]
    refine ⟨⟨r2.ps, r2.vec, r2.ret, 6+1+r1.cost+r2.cost, max ((stI P i).mem.length +
      (stI P i).bs.length + 6 + 2) (max r1.need r2.need), r1.wk+r2.wk⟩, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact p2
    · exact v2
    · exact ret2
    · simp; omega
    · simp [stI_size, n1, n2]; omega
    · simp [w1, w2]; omega

theorem loop_all (P : List Cell) (vec : List Int) (hn : vec.length < 2147483648)
    (hel : ∀ y ∈ vec, s64.valid y = true) (hpre : ∀ k ≤ vec.length, s64.valid (psum vec k) = true)
    (fu : Nat) (hfu : vec.length + 1 ≤ fu) :
    ∃ (r : PRW) (k : Nat), pexecW s64 fu loopCP (stI P ((1 : Nat) : Int)) vec = some r ∧
      r.ps = stI P k ∧ r.vec = pfx vec vec.length ∧ r.ret = none ∧
      r.cost ≤ 31*vec.length+7 ∧ r.need ≤ P.length + 40 ∧ r.wk = vec.length - 1 := by
  by_cases h0 : vec.length = 0
  · have hv : vec = [] := List.length_eq_zero_iff.mp h0
    subst hv
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by simp at hfu; omega⟩
    have hc := cond1_valL ([] : List Int) P 1 hn (by simp) (by omega)
    simp only [List.length_nil] at hc
    have hz : ¬ (((1 : Nat) : Int) < ((0 : Nat) : Int)) := by omega
    rw [if_neg hz] at hc
    rw [pexecW_while, hc]
    simp only [Bind.bind, Option.bind, ite_true, vwp_c1]
    refine ⟨_, 1, rfl, rfl, ?_, rfl, ?_, ?_, ?_⟩
    · simp [pfx]
    · simp
    · simp [stI]
    · simp
  · have h1 : 1 ≤ vec.length := by omega
    have hp1 := pfx_one vec h1
    obtain ⟨r, h, p, v, ret, c, n, w⟩ := loop_runP P vec hn hel hpre (vec.length - 1) 1 (Nat.le_refl _) (by omega) fu (by omega)
    rw [hp1] at h
    exact ⟨r, vec.length, h, p, v, ret, by omega, n, w⟩

theorem body_execP (P : List Cell) (vec : List Int) (hn : vec.length < 2147483648)
    (hel : ∀ y ∈ vec, s64.valid y = true) (hpre : ∀ k ≤ vec.length, s64.valid (psum vec k) = true)
    (fu : Nat) (hfu : vec.length + 1 ≤ fu) :
    ∃ r, pexecW s64 fu bodyCmdP ⟨P,[]⟩ vec = some r ∧ r.ps = ⟨P,[]⟩ ∧ r.vec = pfx vec vec.length ∧ r.ret = none ∧
      r.cost ≤ 31*vec.length + 20 ∧ r.need ≤ P.length + 40 ∧ r.wk = vec.length - 1 := by
  have hv2 : vdenL s64 vec (penv1 (⟨P,[]⟩ : PS)) (.literal i32 1) = some 1 := by
    have h0 : i32.valid 1 = true := rfl
    rw [vdenL_scalar _ _ _ _ rfl, den_literal, if_pos h0]
  have d2 := pstmtW_declare_ok s64 (⟨P,[]⟩ : PS) vec i32 true (.literal i32 1) 1 hv2 1 (conv_signed i32 rfl rfl _ rfl)
  have st0 : (⟨P ++ [(⟨i32,1⟩ : Cell)],[] ++ [⟨P.length,true⟩]⟩ : PS) = stI P ((1 : Nat) : Int) := by
    simp [stI]
  simp only [List.length_nil, List.append_nil, Nat.zero_add] at d2
  have d2' : pstmtW s64 declI1 ⟨P,[]⟩ vec = some ⟨stI P ((1 : Nat) : Int),vec,none,(vwp (NExpr.literal i32 1)).1+1,
      P.length+0+(vwp (NExpr.literal i32 1)).2+4,0⟩ := by
    rw [← st0]; simpa using d2
  obtain ⟨rL, k, hL, pL, vL, retL, cL, nL, wL⟩ := loop_all P vec hn hel hpre fu hfu
  have f2 := seqW_some hL retL (pexecW_skip s64 fu rL.ps rL.vec)
  have d3 := (pexecW_prim s64 fu declI1 _ _).trans d2'
  have f3 := seqW_some d3 rfl f2
  have f4 := pexecW_scope s64 fu _ _ _ _ f3
  have take_eq : (⟨(stI P k).mem.take (⟨P,[]⟩ : PS).mem.length, (stI P k).bs.take (⟨P,[]⟩ : PS).bs.length⟩ : PS) = ⟨P,[]⟩ := by
    simp [stI, List.take_append, List.take_of_length_le]
  rw [pL] at f4
  simp only [take_eq] at f4
  have h5 := seqW_some f4 rfl (pexecW_skip s64 fu (⟨P,[]⟩ : PS) rL.vec)
  refine ⟨_, h5, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · simp [vL]
  · simp [vwp_lit1]
    omega
  · simp [vwp_lit1, stI]
    omega
  · simp [wL]

end Proofs.PrefixSumsCall
