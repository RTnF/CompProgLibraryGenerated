import Proofs.FenwickCall
import Proofs.FenwickBuildMath
import Proofs.Generated.SearchUtil

namespace Proofs.LowerBoundIndexCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.VecStraight Proofs.VecCall Proofs.VecKit
open Proofs.CppNestedFacts Proofs.IntSim Proofs.ScalarCall Proofs.VecWrite Proofs.VecWriteCall Proofs.VecKitW
open Proofs.QuotientSearch Proofs.VectorFillCall Proofs.PrefixSumsCall
open Proofs.VectorSumCall (conv_signed i32_valid)
open Proofs.CppState (Cell)
open Proofs.PowModStep (Sk)
open Proofs.FenwickCall (pexecW_branch_trueB pexecW_branch_falseB)

abbrev loopCond : NExpr := .binary bT .lt (.variable i32 2) (.variable i32 3)
abbrev midE : NExpr := .binary i32 .add (.variable i32 2)
  (.divrem i32 false (.binary i32 .sub (.variable i32 3) (.variable i32 2)) (.literal i32 2))
abbrev declMid : NStmt := .declare i32 true midE
abbrev rdMid : NExpr := .read s64 (.local 0) (.cast u64 (.variable i32 4))
abbrev ltE : NExpr := .binary bT .lt rdMid (.variable s64 1)
abbrev loE : NExpr := .binary i32 .add (.variable i32 4) (.literal i32 1)
abbrev setLo : NStmt := .assign 2 i32 loE
abbrev setHi : NStmt := .assign 3 i32 (.variable i32 4)
abbrev yesC : Command := .sequence (.scope (.sequence (.primitive setLo) (.primitive .skip))) (.primitive .skip)
abbrev noC : Command := .sequence (.scope (.sequence (.primitive setHi) (.primitive .skip))) (.primitive .skip)
abbrev brC : Command := .branch ltE yesC noC
abbrev loopBodyL : Command := .sequence (.scope (.sequence (.primitive declMid) (.sequence brC (.primitive .skip))))
  (.primitive .skip)
abbrev loopCL : Command := .whileLoop loopCond loopBodyL
abbrev declLo : NStmt := .declare i32 true (.literal i32 0)
abbrev declHi : NStmt := .declare i32 true (.cast i32 (.size (.integer s64) (.local 0)))
abbrev bodyCmdL : Command := .sequence (.primitive declLo) (.sequence (.primitive declHi)
  (.sequence loopCL (.sequence (.primitive (.ret (.variable i32 2))) (.primitive .skip))))

theorem body_eq : Proofs.SearchUtilInstance.lower_bound_index_std_vector_long_long.body = bodyCmdL := rfl

-- The callee state: parameter `x`, then the locals `lo` and `hi`.
def sL (P : List Cell) (x : Int) (lo hi : Nat) : PS :=
  ⟨P ++ [⟨s64,x⟩,⟨i32,(lo : Int)⟩,⟨i32,(hi : Int)⟩],[⟨P.length,true⟩,⟨P.length+1,true⟩,⟨P.length+2,true⟩]⟩
-- Inside the loop body: also `mid`.
def sM (P : List Cell) (x : Int) (lo hi mid : Nat) : PS :=
  ⟨P ++ [⟨s64,x⟩,⟨i32,(lo : Int)⟩,⟨i32,(hi : Int)⟩,⟨i32,(mid : Int)⟩],
    [⟨P.length,true⟩,⟨P.length+1,true⟩,⟨P.length+2,true⟩,⟨P.length+3,true⟩]⟩

theorem sL_size (P : List Cell) (x : Int) (lo hi : Nat) : (sL P x lo hi).mem.length + (sL P x lo hi).bs.length = P.length + 6 := by
  simp [sL]
theorem sM_size (P : List Cell) (x : Int) (lo hi mid : Nat) :
    (sM P x lo hi mid).mem.length + (sM P x lo hi mid).bs.length = P.length + 8 := by
  simp [sM]

theorem env_gen (ps : PS) (k a : Nat) (w : Bool) (ty : Ty) (v : Int) (hb : ps.bs[k]? = some ⟨a,w⟩)
    (hm : ps.mem[a]? = some ⟨ty,v⟩) (hv : ty.valid v = true) : penv1 ps (k+1) ty = some v := by
  show penv ps k ty = some v
  exact Proofs.PexecKit.penv_ok ps k ty ⟨a,w⟩ ⟨ty,v⟩ hb hm rfl hv

theorem validN (n : Nat) (h : n < 2147483648) : i32.valid (n : Int) = true := i32_valid n (by omega) (by omega)

theorem envL1 (P : List Cell) (x : Int) (lo hi : Nat) (hx : s64.valid x = true) : penv1 (sL P x lo hi) 1 s64 = some x :=
  env_gen _ 0 P.length true s64 x (by simp [sL]) (by
    have := Proofs.ModIntExec.get_tail P [⟨s64,x⟩,⟨i32,(lo : Int)⟩,⟨i32,(hi : Int)⟩] 0
    simpa [sL] using this) hx
theorem envL2 (P : List Cell) (x : Int) (lo hi : Nat) (h : lo < 2147483648) : penv1 (sL P x lo hi) 2 i32 = some (lo : Int) :=
  env_gen _ 1 (P.length+1) true i32 lo (by simp [sL]) (by
    have := Proofs.ModIntExec.get_tail P [⟨s64,x⟩,⟨i32,(lo : Int)⟩,⟨i32,(hi : Int)⟩] 1
    simpa [sL] using this) (validN lo h)
theorem envL3 (P : List Cell) (x : Int) (lo hi : Nat) (h : hi < 2147483648) : penv1 (sL P x lo hi) 3 i32 = some (hi : Int) :=
  env_gen _ 2 (P.length+2) true i32 hi (by simp [sL]) (by
    have := Proofs.ModIntExec.get_tail P [⟨s64,x⟩,⟨i32,(lo : Int)⟩,⟨i32,(hi : Int)⟩] 2
    simpa [sL] using this) (validN hi h)
theorem envM1 (P : List Cell) (x : Int) (lo hi mid : Nat) (hx : s64.valid x = true) : penv1 (sM P x lo hi mid) 1 s64 = some x :=
  env_gen _ 0 P.length true s64 x (by simp [sM]) (by
    have := Proofs.ModIntExec.get_tail P [⟨s64,x⟩,⟨i32,(lo : Int)⟩,⟨i32,(hi : Int)⟩,⟨i32,(mid : Int)⟩] 0
    simpa [sM] using this) hx
theorem envM2 (P : List Cell) (x : Int) (lo hi mid : Nat) (h : lo < 2147483648) : penv1 (sM P x lo hi mid) 2 i32 = some (lo : Int) :=
  env_gen _ 1 (P.length+1) true i32 lo (by simp [sM]) (by
    have := Proofs.ModIntExec.get_tail P [⟨s64,x⟩,⟨i32,(lo : Int)⟩,⟨i32,(hi : Int)⟩,⟨i32,(mid : Int)⟩] 1
    simpa [sM] using this) (validN lo h)
theorem envM3 (P : List Cell) (x : Int) (lo hi mid : Nat) (h : hi < 2147483648) : penv1 (sM P x lo hi mid) 3 i32 = some (hi : Int) :=
  env_gen _ 2 (P.length+2) true i32 hi (by simp [sM]) (by
    have := Proofs.ModIntExec.get_tail P [⟨s64,x⟩,⟨i32,(lo : Int)⟩,⟨i32,(hi : Int)⟩,⟨i32,(mid : Int)⟩] 2
    simpa [sM] using this) (validN hi h)
theorem envM4 (P : List Cell) (x : Int) (lo hi mid : Nat) (h : mid < 2147483648) : penv1 (sM P x lo hi mid) 4 i32 = some (mid : Int) :=
  env_gen _ 3 (P.length+3) true i32 mid (by simp [sM]) (by
    have := Proofs.ModIntExec.get_tail P [⟨s64,x⟩,⟨i32,(lo : Int)⟩,⟨i32,(hi : Int)⟩,⟨i32,(mid : Int)⟩] 3
    simpa [sM] using this) (validN mid h)

theorem cond_valL (vec : List Int) (P : List Cell) (x : Int) (lo hi : Nat) (hlo : lo < 2147483648) (hhi : hi < 2147483648) :
    vdenL s64 vec (penv1 (sL P x lo hi)) loopCond = some (if lo < hi then 1 else 0) := by
  have hs : loopCond.scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, den_binary, den_variable, envL2 P x lo hi hlo, Option.bind_some, den_variable,
    envL3 P x lo hi hhi, Option.bind_some]
  have : binaryValue .lt (lo : Int) (hi : Int) = if lo < hi then 1 else 0 := by
    show (if (lo : Int) < (hi : Int) then 1 else 0) = _
    by_cases h : lo < hi
    · have : (lo : Int) < (hi : Int) := by omega
      simp [h]
    · have : ¬ ((lo : Int) < (hi : Int)) := by omega
      simp [h]
  rw [this]
  simp only [bT]; unfold Ty.convert
  by_cases h : lo < hi <;> simp [h]

set_option maxRecDepth 100000 in
theorem mid_val (vec : List Int) (P : List Cell) (x : Int) (lo hi : Nat) (hle : lo ≤ hi) (hhi : hi < 2147483648) :
    vdenL s64 vec (penv1 (sL P x lo hi)) midE = some ((lo + (hi - lo) / 2 : Nat) : Int) := by
  have hs : midE.scalarOnly = true := rfl
  have hlo : lo < 2147483648 := by omega
  rw [vdenL_scalar _ _ _ _ hs, den_binary, den_variable, envL2 P x lo hi hlo, Option.bind_some, den_divrem,
    den_binary, den_variable, envL3 P x lo hi hhi, Option.bind_some, den_variable, envL2 P x lo hi hlo,
    Option.bind_some, den_literal, if_pos (show i32.valid 2 = true from rfl)]
  have hsub : binaryValue .sub (hi : Int) (lo : Int) = ((hi - lo : Nat) : Int) := by
    show (hi : Int) - (lo : Int) = _; omega
  have hv : i32.convert (binaryValue .sub (hi : Int) (lo : Int)) = some ((hi - lo : Nat) : Int) := by
    rw [hsub]; exact conv_signed i32 rfl rfl _ (validN _ (by omega))
  rw [hv, Option.bind_some, Option.bind_some]
  have hq : (((hi - lo : Nat) : Int)).tdiv 2 = (((hi - lo) / 2 : Nat) : Int) := by
    rw [Int.tdiv_eq_ediv_of_nonneg (by omega)]; omega
  have hd : checkedDivRem i32 false ((hi - lo : Nat) : Int) 2 = some (((hi - lo) / 2 : Nat) : Int) := by
    unfold checkedDivRem
    rw [hq]
    have hvq : i32.valid (((hi - lo) / 2 : Nat) : Int) = true := validN _ (by omega)
    rw [if_neg (by decide), if_neg (by simp only [hvq, Bool.not_true]; decide)]
    exact conv_signed i32 rfl rfl _ hvq
  rw [hd, Option.bind_some]
  have hadd : binaryValue .add (lo : Int) (((hi - lo) / 2 : Nat) : Int) = ((lo + (hi - lo) / 2 : Nat) : Int) := by
    show (lo : Int) + _ = _; push_cast; rfl
  rw [hadd]
  exact conv_signed i32 rfl rfl _ (validN _ (by omega))

theorem idxM (P : List Cell) (x : Int) (lo hi mid : Nat) (h : mid < 2147483648) :
    (NExpr.cast u64 (.variable i32 4)).denote (penv1 (sM P x lo hi mid)) = some (mid : Int) := by
  rw [den_cast, den_variable, envM4 P x lo hi mid h, Option.bind_some, convert_u64]
  simp
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem ltE_val (vec : List Int) (P : List Cell) (x : Int) (lo hi mid : Nat) (xm : Int) (hmid : mid < 2147483648)
    (hxm : vec[mid]? = some xm) (hxmv : s64.valid xm = true) (hx : s64.valid x = true) :
    vdenL s64 vec (penv1 (sM P x lo hi mid)) ltE = some (if xm < x then 1 else 0) := by
  have hb : ltE.scalarOnly = false := rfl
  have hrc : rdMid.scalarOnly = false := rfl
  have vcur : vdenL s64 vec (penv1 (sM P x lo hi mid)) rdMid = some xm := by
    rw [vdenL_read _ _ _ _ _ hrc, if_pos ⟨rfl, rfl⟩, idxM P x lo hi mid hmid, Option.bind_some]
    simp [elemAtL, hxm, hxmv]
  have hv : vdenL s64 vec (penv1 (sM P x lo hi mid)) (NExpr.variable s64 1) = some x := by
    rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact envM1 P x lo hi mid hx
  rw [vdenL_binary _ _ _ _ _ _ _ hb, vcur, hv, Option.bind_some, Option.bind_some]
  have : binaryValue .lt xm x = if xm < x then 1 else 0 := rfl
  rw [this]
  simp only [bT]; unfold Ty.convert
  by_cases hh : xm < x <;> simp [hh]

theorem loE_val (vec : List Int) (P : List Cell) (x : Int) (lo hi mid : Nat) (h : mid + 1 < 2147483648) :
    vdenL s64 vec (penv1 (sM P x lo hi mid)) loE = some ((mid + 1 : Nat) : Int) := by
  have hs : loE.scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, den_binary, den_variable, envM4 P x lo hi mid (by omega), Option.bind_some,
    den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  have : binaryValue .add (mid : Int) 1 = ((mid + 1 : Nat) : Int) := by
    show (mid : Int) + 1 = _; push_cast; rfl
  rw [this]
  exact conv_signed i32 rfl rfl _ (validN _ h)

theorem hiE_val (vec : List Int) (P : List Cell) (x : Int) (lo hi mid : Nat) (h : mid < 2147483648) :
    vdenL s64 vec (penv1 (sM P x lo hi mid)) (NExpr.variable i32 4) = some (mid : Int) := by
  rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact envM4 P x lo hi mid h

theorem set_lo (P : List Cell) (x : Int) (lo hi mid lo' : Nat) :
    (⟨(sM P x lo hi mid).mem.set (P.length+1) ⟨i32,(lo' : Int)⟩,(sM P x lo hi mid).bs⟩ : PS) = sM P x lo' hi mid := by
  simp [sM, List.set_append_right]

theorem set_hi (P : List Cell) (x : Int) (lo hi mid hi' : Nat) :
    (⟨(sM P x lo hi mid).mem.set (P.length+2) ⟨i32,(hi' : Int)⟩,(sM P x lo hi mid).bs⟩ : PS) = sM P x lo hi' mid := by
  simp [sM, List.set_append_right]

theorem take_sM (P : List Cell) (x : Int) (lo hi mid lo' hi' : Nat) :
    (⟨(sM P x lo' hi' mid).mem.take (sL P x lo hi).mem.length, (sM P x lo' hi' mid).bs.take (sL P x lo hi).bs.length⟩ : PS)
      = sL P x lo' hi' := by
  simp [sM, sL, List.take_append, List.take_of_length_le]

theorem iterYes (P : List Cell) (vec : List Int) (x : Int) (lo hi : Nat) (hlt : lo < hi) (hhi : hi ≤ vec.length)
    (hn : vec.length < 2147483648) (hx : s64.valid x = true) (xm : Int)
    (hxm : vec[lo + (hi - lo) / 2]? = some xm) (hxmv : s64.valid xm = true) (hless : xm < x) (fu : Nat) :
    ∃ r1, pexecW s64 fu loopBodyL (sL P x lo hi) vec = some r1 ∧ r1.ps = sL P x (lo + (hi - lo) / 2 + 1) hi ∧
      r1.vec = vec ∧ r1.ret = none ∧ r1.cost ≤ 150 ∧ r1.need ≤ P.length + 60 ∧ r1.wk = 0 := by
  have hmid : lo + (hi - lo) / 2 < hi := by omega
  have hv := mid_val vec P x lo hi (by omega) (by omega)
  have d1 := pstmtW_declare_ok s64 (sL P x lo hi) vec i32 true midE ((lo + (hi - lo) / 2 : Nat) : Int) hv
    ((lo + (hi - lo) / 2 : Nat) : Int) (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  have st0 : (⟨(sL P x lo hi).mem ++ [(⟨i32,((lo + (hi - lo) / 2 : Nat) : Int)⟩ : Cell)],
      (sL P x lo hi).bs ++ [⟨(sL P x lo hi).mem.length,true⟩]⟩ : PS) = sM P x lo hi (lo + (hi - lo) / 2) := by
    simp [sL, sM]
  rw [st0] at d1
  have d1' := (pexecW_prim s64 fu declMid _ _).trans d1
  have cv := ltE_val vec P x lo hi (lo + (hi - lo) / 2) xm (by omega) hxm hxmv hx
  rw [if_pos hless] at cv
  have lv := loE_val vec P x lo hi (lo + (hi - lo) / 2) (by omega)
  have bA : (sM P x lo hi (lo + (hi - lo) / 2)).bs[1]? = some ⟨P.length+1,true⟩ := by simp [sM]
  have cA : (sM P x lo hi (lo + (hi - lo) / 2)).mem[P.length+1]? = some ⟨i32,(lo : Int)⟩ := by
    have := Proofs.ModIntExec.get_tail P [⟨s64,x⟩,⟨i32,(lo : Int)⟩,⟨i32,(hi : Int)⟩,⟨i32,((lo + (hi - lo) / 2 : Nat) : Int)⟩] 1
    simpa [sM] using this
  have stA := pstmtW_assign_ok s64 (sM P x lo hi (lo + (hi - lo) / 2)) vec 1 i32 loE
    ((lo + (hi - lo) / 2 + 1 : Nat) : Int) lv ⟨P.length+1,true⟩ ⟨i32,(lo : Int)⟩ bA cA rfl (validN _ (by omega)) rfl
    ((lo + (hi - lo) / 2 + 1 : Nat) : Int) (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  rw [set_lo] at stA
  have a1 := (pexecW_prim s64 fu setLo _ _).trans stA
  have a2 := seqW_some a1 rfl (pexecW_skip s64 fu (sM P x (lo + (hi - lo) / 2 + 1) hi (lo + (hi - lo) / 2)) vec)
  have a3 := pexecW_scope s64 fu _ _ _ _ a2
  have a4 := Proofs.PexecKit.scope_take (sM P x lo hi (lo + (hi - lo) / 2))
    (sM P x (lo + (hi - lo) / 2 + 1) hi (lo + (hi - lo) / 2)) (by simp [sM]) (by simp [sM])
  simp only [a4] at a3
  have a5 := seqW_some a3 rfl (pexecW_skip s64 fu (sM P x (lo + (hi - lo) / 2 + 1) hi (lo + (hi - lo) / 2)) vec)
  have br := pexecW_branch_trueB s64 fu ltE yesC noC (sM P x lo hi (lo + (hi - lo) / 2)) vec 1 cv (by simp) _ a5
  have e1 := seqW_some br rfl (pexecW_skip s64 fu _ _)
  have e2 := seqW_some d1' rfl e1
  have e3 := pexecW_scope s64 fu _ _ _ _ e2
  simp only [take_sM] at e3
  have c1 := seqW_some e3 rfl (pexecW_skip s64 fu (sL P x (lo + (hi - lo) / 2 + 1) hi) vec)
  refine ⟨_, c1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, Container.nodes]
  · simp [vwp, NExpr.nodes, Container.nodes, sM, sL]
  · simp

theorem iterNo (P : List Cell) (vec : List Int) (x : Int) (lo hi : Nat) (hlt : lo < hi) (hhi : hi ≤ vec.length)
    (hn : vec.length < 2147483648) (hx : s64.valid x = true) (xm : Int)
    (hxm : vec[lo + (hi - lo) / 2]? = some xm) (hxmv : s64.valid xm = true) (hge : ¬ xm < x) (fu : Nat) :
    ∃ r1, pexecW s64 fu loopBodyL (sL P x lo hi) vec = some r1 ∧ r1.ps = sL P x lo (lo + (hi - lo) / 2) ∧
      r1.vec = vec ∧ r1.ret = none ∧ r1.cost ≤ 150 ∧ r1.need ≤ P.length + 60 ∧ r1.wk = 0 := by
  have hmid : lo + (hi - lo) / 2 < hi := by omega
  have hv := mid_val vec P x lo hi (by omega) (by omega)
  have d1 := pstmtW_declare_ok s64 (sL P x lo hi) vec i32 true midE ((lo + (hi - lo) / 2 : Nat) : Int) hv
    ((lo + (hi - lo) / 2 : Nat) : Int) (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  have st0 : (⟨(sL P x lo hi).mem ++ [(⟨i32,((lo + (hi - lo) / 2 : Nat) : Int)⟩ : Cell)],
      (sL P x lo hi).bs ++ [⟨(sL P x lo hi).mem.length,true⟩]⟩ : PS) = sM P x lo hi (lo + (hi - lo) / 2) := by
    simp [sL, sM]
  rw [st0] at d1
  have d1' := (pexecW_prim s64 fu declMid _ _).trans d1
  have cv := ltE_val vec P x lo hi (lo + (hi - lo) / 2) xm (by omega) hxm hxmv hx
  rw [if_neg hge] at cv
  have lv := hiE_val vec P x lo hi (lo + (hi - lo) / 2) (by omega)
  have bA : (sM P x lo hi (lo + (hi - lo) / 2)).bs[2]? = some ⟨P.length+2,true⟩ := by simp [sM]
  have cA : (sM P x lo hi (lo + (hi - lo) / 2)).mem[P.length+2]? = some ⟨i32,(hi : Int)⟩ := by
    have := Proofs.ModIntExec.get_tail P [⟨s64,x⟩,⟨i32,(lo : Int)⟩,⟨i32,(hi : Int)⟩,⟨i32,((lo + (hi - lo) / 2 : Nat) : Int)⟩] 2
    simpa [sM] using this
  have stA := pstmtW_assign_ok s64 (sM P x lo hi (lo + (hi - lo) / 2)) vec 2 i32 (NExpr.variable i32 4)
    ((lo + (hi - lo) / 2 : Nat) : Int) lv ⟨P.length+2,true⟩ ⟨i32,(hi : Int)⟩ bA cA rfl (validN _ (by omega)) rfl
    ((lo + (hi - lo) / 2 : Nat) : Int) (conv_signed i32 rfl rfl _ (validN _ (by omega)))
  rw [set_hi] at stA
  have a1 := (pexecW_prim s64 fu setHi _ _).trans stA
  have a2 := seqW_some a1 rfl (pexecW_skip s64 fu (sM P x lo (lo + (hi - lo) / 2) (lo + (hi - lo) / 2)) vec)
  have a3 := pexecW_scope s64 fu _ _ _ _ a2
  have a4 := Proofs.PexecKit.scope_take (sM P x lo hi (lo + (hi - lo) / 2))
    (sM P x lo (lo + (hi - lo) / 2) (lo + (hi - lo) / 2)) (by simp [sM]) (by simp [sM])
  simp only [a4] at a3
  have a5 := seqW_some a3 rfl (pexecW_skip s64 fu (sM P x lo (lo + (hi - lo) / 2) (lo + (hi - lo) / 2)) vec)
  have br := pexecW_branch_falseB s64 fu ltE yesC noC (sM P x lo hi (lo + (hi - lo) / 2)) vec cv _ a5
  have e1 := seqW_some br rfl (pexecW_skip s64 fu _ _)
  have e2 := seqW_some d1' rfl e1
  have e3 := pexecW_scope s64 fu _ _ _ _ e2
  simp only [take_sM] at e3
  have c1 := seqW_some e3 rfl (pexecW_skip s64 fu (sL P x lo (lo + (hi - lo) / 2)) vec)
  refine ⟨_, c1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, Container.nodes]
  · simp [vwp, NExpr.nodes, Container.nodes, sM, sL]
  · simp

/-- `lo` and `hi` bracket the answer: everything below `lo` is `< x`, everything from `hi` on is `≥ x`. -/
def LInv (vec : List Int) (x : Int) (lo hi : Nat) : Prop :=
  (∀ j, j < lo → ∀ y : Int, vec[j]? = some y → y < x) ∧ (∀ j, hi ≤ j → ∀ y : Int, vec[j]? = some y → ¬ y < x)

abbrev SortedL (vec : List Int) : Prop := ∀ i j : Nat, i ≤ j → ∀ a b : Int, vec[i]? = some a → vec[j]? = some b → a ≤ b

def stepsL : Nat → Nat
  | 0 => 0
  | m+1 => 1 + stepsL ((m+1)/2)
decreasing_by omega

theorem stepsL_succ (m : Nat) (h : 0 < m) : stepsL m = 1 + stepsL (m / 2) := by
  obtain ⟨m0, rfl⟩ : ∃ m0, m = m0 + 1 := ⟨m - 1, by omega⟩
  rw [stepsL]

theorem stepsL_mono : ∀ b a, a ≤ b → stepsL a ≤ stepsL b := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro a hab
    by_cases ha : a = 0
    · subst ha; simp [stepsL]
    · have hb : 0 < b := by omega
      rw [stepsL_succ a (by omega), stepsL_succ b hb]
      have := ih (b / 2) (by omega) (a / 2) (by omega)
      omega

theorem stepsL_log : ∀ m, stepsL m ≤ Nat.log2 m + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases h0 : m = 0
    · subst h0; simp [stepsL]
    · rw [stepsL_succ m (by omega)]
      have h := ih (m / 2) (by omega)
      by_cases h2 : m / 2 = 0
      · have : m = 1 := by omega
        subst this; simp [stepsL]
      · have : Nat.log2 m = Nat.log2 (m / 2) + 1 := by
          rw [Nat.log2_def]; split
          · rfl
          · omega
        omega

theorem LInv_yes (vec : List Int) (x : Int) (lo hi : Nat) (hs : SortedL vec) (hinv : LInv vec x lo hi)
    (mid : Nat) (xm : Int) (hxm : vec[mid]? = some xm) (hless : xm < x) : LInv vec x (mid + 1) hi := by
  refine ⟨fun j hj y hy => ?_, hinv.2⟩
  have := hs j mid (by omega) y xm hy hxm
  omega

theorem LInv_no (vec : List Int) (x : Int) (lo hi : Nat) (hs : SortedL vec) (hinv : LInv vec x lo hi)
    (mid : Nat) (xm : Int) (hxm : vec[mid]? = some xm) (hge : ¬ xm < x) : LInv vec x lo mid := by
  refine ⟨hinv.1, fun j hj y hy => ?_⟩
  have := hs mid j hj xm y hxm hy
  omega

theorem vwp_cond : vwp loopCond = (3,3) := by decide

theorem loop_runL (P : List Cell) (vec : List Int) (x : Int) (hn : vec.length < 2147483648)
    (hx : s64.valid x = true) (hel : ∀ y ∈ vec, s64.valid y = true) (hs : SortedL vec) :
    ∀ (m lo hi : Nat), hi - lo = m → lo ≤ hi → hi ≤ vec.length → LInv vec x lo hi → ∀ fu, stepsL m + 1 ≤ fu →
      ∃ res r, pexecW s64 fu loopCL (sL P x lo hi) vec = some res ∧ res.ps = sL P x r r ∧ lo ≤ r ∧ r ≤ hi ∧
        LInv vec x r r ∧ res.vec = vec ∧ res.ret = none ∧ res.cost ≤ 157 * stepsL m + 7 ∧
        res.need ≤ P.length + 60 ∧ res.wk = 0 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro lo hi hm hle hhi hinv fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    have hc := cond_valL vec P x lo hi (by omega) (by omega)
    by_cases hlt : lo < hi
    · rw [if_pos hlt] at hc
      have hmid : lo + (hi - lo) / 2 < hi := by omega
      obtain ⟨xm, hxm⟩ : ∃ y, vec[lo + (hi - lo) / 2]? = some y := ⟨vec[lo + (hi - lo) / 2], by simp <;> omega⟩
      have hxmv := hel xm (List.mem_of_getElem? hxm)
      have hm' : stepsL m = 1 + stepsL (m / 2) := stepsL_succ m (by omega)
      by_cases hless : xm < x
      · obtain ⟨r1, h1, p1, v1, ret1, c1, n1, w1⟩ := iterYes P vec x lo hi hlt hhi hn hx xm hxm hxmv hless (fu'+1)
        have hinv' := LInv_yes vec x lo hi hs hinv _ xm hxm hless
        have hms := stepsL_mono (m / 2) (hi - (lo + (hi - lo) / 2 + 1)) (by omega)
        obtain ⟨r2, r, h2, p2, hlr, hrh, hinvr, v2, ret2, c2, n2, w2⟩ :=
          ih (hi - (lo + (hi - lo) / 2 + 1)) (by omega) (lo + (hi - lo) / 2 + 1) hi rfl (by omega) hhi hinv' fu'
            (by omega)
        rw [pexecW_while, hc]
        simp only [Bind.bind, Option.bind, h1, ret1, p1, v1, h2, vwp_cond]
        refine ⟨⟨r2.ps, r2.vec, r2.ret, 3+1+r1.cost+r2.cost, max ((sL P x lo hi).mem.length +
          (sL P x lo hi).bs.length + 3 + 2) (max r1.need r2.need), r1.wk+r2.wk⟩, r, by simp, p2, by omega, hrh, hinvr,
          v2, ret2, ?_, ?_, ?_⟩
        · simp <;> omega
        · simp [sL_size, n1, n2] <;> omega
        · simp [w1, w2]
      · obtain ⟨r1, h1, p1, v1, ret1, c1, n1, w1⟩ := iterNo P vec x lo hi hlt hhi hn hx xm hxm hxmv hless (fu'+1)
        have hinv' := LInv_no vec x lo hi hs hinv _ xm hxm hless
        have hms := stepsL_mono (m / 2) (lo + (hi - lo) / 2 - lo) (by omega)
        obtain ⟨r2, r, h2, p2, hlr, hrh, hinvr, v2, ret2, c2, n2, w2⟩ :=
          ih (lo + (hi - lo) / 2 - lo) (by omega) lo (lo + (hi - lo) / 2) rfl (by omega) (by omega) hinv' fu'
            (by omega)
        rw [pexecW_while, hc]
        simp only [Bind.bind, Option.bind, h1, ret1, p1, v1, h2, vwp_cond]
        refine ⟨⟨r2.ps, r2.vec, r2.ret, 3+1+r1.cost+r2.cost, max ((sL P x lo hi).mem.length +
          (sL P x lo hi).bs.length + 3 + 2) (max r1.need r2.need), r1.wk+r2.wk⟩, r, by simp, p2, by omega, by omega, hinvr,
          v2, ret2, ?_, ?_, ?_⟩
        · simp <;> omega
        · simp [sL_size, n1, n2] <;> omega
        · simp [w1, w2]
    · rw [if_neg hlt] at hc
      have : lo = hi := by omega
      subst this
      rw [pexecW_while, hc]
      simp only [Bind.bind, Option.bind, ite_true, vwp_cond]
      refine ⟨_, lo, rfl, rfl, Nat.le_refl _, Nat.le_refl _, ?_, rfl, rfl, ?_, ?_, rfl⟩
      · exact hinv
      · simp
      · simp [sL]

def s0 (P : List Cell) (x : Int) : PS := ⟨P ++ [⟨s64,x⟩],[⟨P.length,true⟩]⟩
def s1 (P : List Cell) (x : Int) : PS := ⟨P ++ [⟨s64,x⟩,⟨i32,(0 : Int)⟩],[⟨P.length,true⟩,⟨P.length+1,true⟩]⟩

theorem size_val (vec : List Int) (ps : PS) (hn : vec.length < 2147483648) :
    vdenL s64 vec (penv1 ps) (.cast i32 (.size (.integer s64) (.local 0))) = some (vec.length : Int) := by
  have hr2 : (NExpr.cast i32 (.size (.integer s64) (.local 0))).scalarOnly = false := rfl
  have hn' : i32.convert (vec.length : Int) = some (vec.length : Int) :=
    conv_signed i32 rfl rfl _ (validN _ hn)
  have hr : (NExpr.size (.integer s64) (.local 0)).scalarOnly = false := rfl
  have hsz : vdenL s64 vec (penv1 ps) (.size (.integer s64) (.local 0)) = some (vec.length : Int) := by
    simp [vdenL, hr]
  rw [vdenL_cast s64 vec _ _ _ hr2, hsz, Option.bind_some, hn']

theorem ret_val (P : List Cell) (vec : List Int) (x : Int) (r : Nat) (h : r < 2147483648) :
    vdenL s64 vec (penv1 (sL P x r r)) (NExpr.variable i32 2) = some (r : Int) := by
  rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact envL2 P x r r h

theorem body_execL (P : List Cell) (vec : List Int) (x : Int) (hn : vec.length < 2147483648)
    (hx : s64.valid x = true) (hel : ∀ y ∈ vec, s64.valid y = true) (hs : SortedL vec) (fu : Nat)
    (hfu : stepsL vec.length + 1 ≤ fu) :
    ∃ (res : PRW) (r : Nat), pexecW s64 fu bodyCmdL (s0 P x) vec = some res ∧ res.ret = some (r : Int) ∧ r ≤ vec.length ∧
      LInv vec x r r ∧ res.ps = sL P x r r ∧ res.vec = vec ∧ res.cost ≤ 157 * stepsL vec.length + 40 ∧ res.need ≤ P.length + 60 ∧
      res.wk = 0 := by
  have hv0 : vdenL s64 vec (penv1 (s0 P x)) (.literal i32 0) = some 0 := by
    rw [vdenL_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 0 = true from rfl)]
  have d1 := pstmtW_declare_ok s64 (s0 P x) vec i32 true (.literal i32 0) 0 hv0 0 (conv_signed i32 rfl rfl _ rfl)
  have st1 : (⟨(s0 P x).mem ++ [(⟨i32,(0 : Int)⟩ : Cell)], (s0 P x).bs ++ [⟨(s0 P x).mem.length,true⟩]⟩ : PS) = s1 P x := by
    simp [s0, s1]
  rw [st1] at d1
  have d1' := (pexecW_prim s64 fu declLo _ _).trans d1
  have d2 := pstmtW_declare_ok s64 (s1 P x) vec i32 true _ (vec.length : Int) (size_val vec _ hn) (vec.length : Int)
    (conv_signed i32 rfl rfl _ (validN _ hn))
  have st2 : (⟨(s1 P x).mem ++ [(⟨i32,(vec.length : Int)⟩ : Cell)], (s1 P x).bs ++ [⟨(s1 P x).mem.length,true⟩]⟩ : PS)
      = sL P x 0 vec.length := by
    simp [s1, sL]
  rw [st2] at d2
  have d2' := (pexecW_prim s64 fu declHi _ _).trans d2
  have linv : LInv vec x 0 vec.length := ⟨fun j hj => by omega, fun j hj y hy => by
    have := (List.getElem?_eq_some_iff.mp hy).1; omega⟩
  obtain ⟨rL, r, hL, pL, hlr, hrh, hinvr, vL, retL, cL, nL, wL⟩ :=
    loop_runL P vec x hn hx hel hs vec.length 0 vec.length (by omega) (by omega) (Nat.le_refl _) linv fu hfu
  have g1 := pstmtW_ret_ok s64 (sL P x r r) vec (NExpr.variable i32 2) (r : Int) (ret_val P vec x r (by omega))
  have g2 := (pexecW_prim s64 fu (.ret (.variable i32 2)) _ _).trans g1
  have g3 := seqW_ret (b := .primitive .skip) g2 rfl
  have h4 := seqW_some hL retL (by rw [pL, vL]; exact g3)
  have h5 := seqW_some d2' rfl h4
  have h6 := seqW_some d1' rfl h5
  refine ⟨_, r, h6, rfl, hrh, hinvr, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes, Container.nodes]
    omega
  · simp [vwp, NExpr.nodes, Container.nodes, s0, s1, sL]
    omega
  · simp [wL]
theorem prepare_lb (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : Proofs.VectorSumCall.VOK caller vslot vb V vsc m vbuf) (e : NExpr) (v : Int) (hs : e.scalarOnly = true)
    (hty : e.resultType = s64) (value : e.denote (envOf caller) = some v) (hv : s64.valid v = true) :
    ∃ t, Good (caller.charge 1 1) t e.nodes e.nodes ∧
      ∃ Sinit, prepare caller Proofs.SearchUtilInstance.lower_bound_index_std_vector_long_long.parameters [.vectorReference vslot,.value e] = some Sinit ∧
        Sinit.slots = [.vector 0,.scalar 0] ∧ Sinit.scalars.memory = callerP caller ++ [⟨s64,v⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer s64,false,.root vsc⟩]⟩ ∧
        Sinit.scalars.work = t.scalars.work+3 ∧ t.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc s64 false m vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (by simp)
  have rvec : resolve caller (.vector s64 false) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc s64 false) := by
    simp [resolve,ok.slot,ok.binding,resolved]
  obtain ⟨t,ran,good⟩ := scalar_eval e (caller.charge 1 1) v hs
    (by rw [envOf_core (core_charge caller 1 1)]; exact value)
  refine ⟨t,good,?_⟩
  have res : resolve (caller.charge 1 1) (.scalar s64 false true) (.value e) = some (t,.scalar s64 true v) := by
    simp [resolve,hty,ran]
  have frameT : t.frame = caller.frame := good.1.1
  have fs : t.frame.state = caller.frame.state := by rw [frameT]
  have fr : t.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t.scalars.memory = caller.scalars.memory := good.1.2.2.2.1
  have hbind : t.scalars.bindings = caller.scalars.bindings := good.1.2.2.2.2.1
  have hbase : t.scalars.baseMemory = caller.scalars.baseMemory := good.1.2.2.2.2.2
  have bound : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).bindRoot V (.integer s64) vsc false =
      some (⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer s64,false,.root vsc⟩]⟩,0) := by
    have vobject : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).object V (.integer s64) =
        some (vbuf,⟨.integer s64,none,some vsc,[]⟩) :=
      object_runs _ V _ vbuf _ ok.valid ok.vfound ok.vtag rfl
    have vrooted : caller.frame.state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ ok.vtag rfl
    have vmax : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).maximum V = some m :=
      maximum_runs _ V V m ok.lengths vrooted ok.flag
    simp only [Frame.bindRoot,vobject,vmax,Bind.bind,Option.bind]
    simp [Frame.addBinding]
  have hp : Proofs.SearchUtilInstance.lower_bound_index_std_vector_long_long.parameters = [.vector s64 false,.scalar s64 false true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec,res]
  simp [fs,fr,fb,hmem,hbind,hbase,bound,bindAll,bindOne,CppState.bindArgument,hv,callerP,
    NState.observe,CppState.State.observe]
  left
  have g := good.2.2.2.2.1
  simp [NState.charge,NState.observe,CppState.State.observe] at g
  omega


set_option maxHeartbeats 4000000 in
theorem lower_bound_index_correct (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : Proofs.VectorSumCall.VOK caller vslot vb V vsc m vbuf) (vec : List Int)
    (hitems : vbuf.items = vec.map Value.integer) (hn : vec.length < 2147483648)
    (hbvalid : vbuf.Valid (accepts (.integer s64))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit s64)
    (howner : vbuf.owner = V)
    (e : NExpr) (x : Int) (hs : e.scalarOnly = true) (ht : e.resultType = s64)
    (value : e.denote (envOf caller) = some x) (hx : s64.valid x = true)
    (hel : ∀ y ∈ vec, s64.valid y = true) (hsorted : SortedL vec) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (r : Nat), prepare caller Proofs.SearchUtilInstance.lower_bound_index_std_vector_long_long.parameters
        [.vectorReference vslot,.value e] = some Sinit ∧
      Proofs.SearchUtilInstance.lower_bound_index_std_vector_long_long.callFuel fuel caller [.vectorReference vslot,.value e] =
        .finished (res,.scalar (r : Int)) ∧ r ≤ vec.length ∧
      (∀ j, j < r → ∀ y : Int, vec[j]? = some y → y < x) ∧ (∀ j, r ≤ j → ∀ y : Int, vec[j]? = some y → ¬ y < x) ∧
      ScalarPost3 caller Sinit res e.nodes (157*Nat.log2 vec.length+260) caller.scalars.memory 0 V vec := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_lb caller ok e x hs ht value hx
  let vc : VCtx := ⟨s64,false,m,V,vsc,vbuf,vec,hitems,fun h => absurd h (by decide),by omega,
    caller.frame.state.liveSpace,caller.frame.state.storage.work,caller.scope+1,
    caller.frame.state.storage.objects.length⟩
  have fwS : FW vc vec vbuf 0 Sinit.frame := by
    rw [sFrame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,hitems,hbvalid,hlimit,howner,by omega⟩
    intro owner k h
    have := ok.strict owner k h
    show k < caller.scope+1
    omega
  have hsteps := stepsL_log vec.length
  obtain ⟨rr,r,hexec,hret,hrle,hinv,hrps,hrvec,hcost,hneed,hwk⟩ :=
    body_execL (callerP caller) vec x hn hx hel hsorted (Nat.log2 vec.length + 2) (by omega)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨s64,x⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := take_P caller _
  have gw1 := good.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hpost := call_vecw vc false (fun h => absurd h (by decide)) caller Proofs.SearchUtilInstance.lower_bound_index_std_vector_long_long
    [.vectorReference vslot,.value e] Sinit
    (callerP caller ++ [(⟨s64,x⟩ : Cell)]) [(⟨(callerP caller).length,true⟩ : CppState.Binding)]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok.base (by decide) (Nat.log2 vec.length + 2) rr
    (by rw [body_eq]; exact hexec) (r : Int) hret i32 rfl (validN r (by omega)) (by omega) (by simp) e.nodes
    (157*Nat.log2 vec.length+260) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,r,hprep,hrun,hrle,hinv.1,hinv.2,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [sL]
    exact take_P caller _
  rw [hs', hrvec, hwk] at post
  exact post
