import Proofs.FenwickCall
import Proofs.Generated.FenwickTree

namespace Proofs.FenwickRangeCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.VecStraight Proofs.VecCall Proofs.VecKit
open Proofs.CppNestedFacts Proofs.IntSim Proofs.ScalarCall Proofs.VecWrite Proofs.VecWriteCall Proofs.VecKitW
open Proofs.QuotientSearch Proofs.VectorFillCall Proofs.PrefixSumsCall Proofs.FenwickMath
open Proofs.VectorSumCall (conv_signed i32_valid psum psum_succ)
open Proofs.CppState (Cell)
open Proofs.PowModStep (Sk)
open Proofs.FenwickCall (chainS chain_last lowE_den stepsS_log)

-- The query loop of `fenwick_sum` on the locals with binding indices `j` (the node) and `j+1` (the accumulator).
abbrev vRg (j : Nat) : NExpr := .variable i32 (j+1)
abbrev vAg (j : Nat) : NExpr := .variable s64 (j+2)
abbrev lowEg (j : Nat) : NExpr := .cast i32 (.binary u32 .band (.cast u32 (vRg j))
  (.binary u32 .sub (.literal u32 0) (.cast u32 (vRg j))))
abbrev rdKg (j : Nat) : NExpr := .read s64 (.local 0) (.cast u64 (vRg j))
abbrev condSg (j : Nat) : NExpr := .binary bT .gt (vRg j) (.literal i32 0)
abbrev accEg (j : Nat) : NExpr := .binary s64 .add (vAg j) (rdKg j)
abbrev assign2g (j : Nat) : NStmt := .assign (j+2) s64 (accEg j)
abbrev subEg (j : Nat) : NExpr := .binary i32 .sub (vRg j) (lowEg j)
abbrev stepSg (j : Nat) : NStmt := .assign (j+1) i32 (subEg j)
abbrev loopBodySg (j : Nat) : Command := .sequence (.scope (.sequence (.primitive (assign2g j)) (.primitive .skip)))
  (.sequence (.primitive (stepSg j)) (.primitive .skip))
abbrev loopCSg (j : Nat) : Command := .whileLoop (condSg j) (loopBodySg j)

theorem vwp_condSg (j : Nat) : vwp (condSg j) = (3,3) := rfl
theorem vwp_accEg (j : Nat) : vwp (accEg j) = (7,7) := rfl
theorem vwp_subEg (j : Nat) : vwp (subEg j) = (10,10) := rfl

-- Bindings `j` and `j+1` are writable cells at `adr` (the node `r`) and `ada` (the accumulator `acc`).
def Loc2 (ps0 : PS) (j adr ada : Nat) (r acc : Int) : Prop :=
  ps0.bs[j]? = some ⟨adr,true⟩ ∧ ps0.bs[j+1]? = some ⟨ada,true⟩ ∧
  ps0.mem[adr]? = some ⟨i32,r⟩ ∧ ps0.mem[ada]? = some ⟨s64,acc⟩ ∧ adr ≠ ada

def upd2 (ps0 : PS) (adr ada : Nat) (r acc : Int) : PS :=
  ⟨(ps0.mem.set ada ⟨s64,acc⟩).set adr ⟨i32,r⟩,ps0.bs⟩

theorem upd2_size (ps0 : PS) (adr ada : Nat) (r acc : Int) :
    (upd2 ps0 adr ada r acc).mem.length + (upd2 ps0 adr ada r acc).bs.length = ps0.mem.length + ps0.bs.length := by
  simp [upd2]

theorem loc2_upd (ps0 : PS) (j adr ada : Nat) (r acc : Int) (r' acc' : Int) (h : Loc2 ps0 j adr ada r acc) :
    Loc2 (upd2 ps0 adr ada r' acc') j adr ada r' acc' := by
  obtain ⟨b1,b2,m1,m2,hne⟩ := h
  have l1 : adr < ps0.mem.length := (List.getElem?_eq_some_iff.mp m1).1
  have l2 : ada < ps0.mem.length := (List.getElem?_eq_some_iff.mp m2).1
  refine ⟨b1,b2,?_,?_,hne⟩
  · simp only [upd2]; rw [List.getElem?_set_self (by simp; exact l1)]
  · simp only [upd2]; rw [List.getElem?_set_ne hne, List.getElem?_set_self l2]

theorem upd2_upd2 (ps0 : PS) (adr ada : Nat) (hne : adr ≠ ada) (r acc r' acc' : Int) :
    upd2 (upd2 ps0 adr ada r acc) adr ada r' acc' = upd2 ps0 adr ada r' acc' := by
  simp only [upd2]
  congr 1
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_set, List.length_set]
  by_cases h1 : adr = i <;> by_cases h2 : ada = i <;> simp_all

theorem env_r (ps0 : PS) (j adr ada : Nat) (r acc : Int) (h : Loc2 ps0 j adr ada r acc) (hv : i32.valid r = true) :
    penv1 ps0 (j+1) i32 = some r := by
  obtain ⟨b1,b2,m1,m2,hne⟩ := h
  show penv ps0 j i32 = some r
  simp [penv, b1, m1, hv]

theorem env_a (ps0 : PS) (j adr ada : Nat) (r acc : Int) (h : Loc2 ps0 j adr ada r acc) (hv : s64.valid acc = true) :
    penv1 ps0 (j+2) s64 = some acc := by
  obtain ⟨b1,b2,m1,m2,hne⟩ := h
  show penv ps0 (j+1) s64 = some acc
  simp [penv, b2, m2, hv]

theorem lowEg_den (env : Nat → Ty → Option Int) (j k : Nat) (h0 : 0 < k) (h1 : k < 2147483648)
    (e : env (j+1) i32 = some (k : Int)) : (lowEg j).denote env = some (lowb k : Int) := by
  have hk32 : (k : Int) % 4294967296 = (k : Int) := Int.emod_eq_of_lt (by omega) (by omega)
  have c1 : (NExpr.cast u32 (.variable i32 (j+1))).denote env = some (k : Int) := by
    rw [den_cast, den_variable, e, Option.bind_some, convert_u32, hk32]
  have c0 : (NExpr.literal u32 0).denote env = some 0 := by
    rw [den_literal, if_pos (show u32.valid 0 = true from rfl)]
  have c2 : (NExpr.binary u32 .sub (.literal u32 0) (.cast u32 (.variable i32 (j+1)))).denote env =
      some (4294967296 - (k : Int)) := by
    rw [den_binary, c0, c1]
    simp only [Option.bind_some, convert_u32]
    have : binaryValue .sub 0 (k : Int) = -(k : Int) := by show 0 - (k : Int) = _; omega
    rw [this]
    congr 1
    omega
  have hl := lowb_pos k h0
  have hl' := lowb_le k h0
  have c3 : (NExpr.binary u32 .band (.cast u32 (.variable i32 (j+1)))
      (.binary u32 .sub (.literal u32 0) (.cast u32 (.variable i32 (j+1))))).denote env = some (lowb k : Int) := by
    rw [den_binary, c1, c2]
    simp only [Option.bind_some, convert_u32]
    have hband : binaryValue .band (k : Int) (4294967296 - (k : Int)) = (lowb k : Int) := by
      show (((k : Int).toNat &&& (4294967296 - (k : Int)).toNat : Nat) : Int) = _
      have a1 : (k : Int).toNat = k := by omega
      have a2 : (4294967296 - (k : Int)).toNat = 2^32 - k := by omega
      rw [a1, a2, lowbit_eval k h0 h1]
    rw [hband]
    congr 1
    omega
  rw [den_cast, c3, Option.bind_some]
  exact conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega))



theorem idxg (ps0 : PS) (j adr ada r : Nat) (acc : Int) (h : Loc2 ps0 j adr ada r acc) (hk : r < 2147483648) :
    (NExpr.cast u64 (vRg j)).denote (penv1 ps0) = some (r : Int) := by
  have e1 := env_r ps0 j adr ada r acc h (i32_valid r (by omega) (by omega))
  rw [den_cast]
  show ((penv1 ps0) (j+1) i32).bind u64.convert = _
  rw [e1, Option.bind_some, convert_u64]
  simp
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem condSg_valL (vec : List Int) (ps0 : PS) (j adr ada r : Nat) (acc : Int) (h : Loc2 ps0 j adr ada r acc)
    (hr : r < 2147483648) :
    vdenL s64 vec (penv1 ps0) (condSg j) = some (if 0 < r then 1 else 0) := by
  have e1 := env_r ps0 j adr ada r acc h (i32_valid r (by omega) (by omega))
  have hs : (condSg j).scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, den_binary, den_variable, e1, Option.bind_some, den_literal,
    if_pos (show i32.valid 0 = true from rfl), Option.bind_some]
  have : binaryValue .gt (r : Int) 0 = if 0 < r then 1 else 0 := by
    show (if (r : Int) > 0 then 1 else 0) = _
    by_cases h : 0 < r
    · have : (r : Int) > 0 := by omega
      simp [h]
    · have : ¬ ((r : Int) > 0) := by omega
      simp [h]
  rw [this]
  simp only [bT]; unfold Ty.convert
  by_cases h : 0 < r <;> simp [h]

theorem accEg_den (tree : List Int) (ps0 : PS) (j adr ada r : Nat) (acc x : Int) (h : Loc2 ps0 j adr ada r acc)
    (hr : r < 2147483648) (hx : tree[r]? = some x) (hxv : s64.valid x = true) (hacc : s64.valid acc = true)
    (hsum : s64.valid (acc + x) = true) :
    vdenL s64 tree (penv1 ps0) (accEg j) = some (acc + x) := by
  have hb : (accEg j).scalarOnly = false := rfl
  have hrc : (rdKg j).scalarOnly = false := rfl
  have vcur : vdenL s64 tree (penv1 ps0) (rdKg j) = some x := by
    rw [vdenL_read _ _ _ _ _ hrc, if_pos ⟨rfl, rfl⟩, idxg ps0 j adr ada r acc h hr, Option.bind_some]
    simp [elemAtL, hx, hxv]
  have hv : vdenL s64 tree (penv1 ps0) (vAg j) = some acc := by
    rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact env_a ps0 j adr ada r acc h hacc
  rw [vdenL_binary _ _ _ _ _ _ _ hb, hv, vcur, Option.bind_some, Option.bind_some]
  have : binaryValue .add acc x = acc + x := rfl
  rw [this]
  exact conv_signed s64 rfl rfl _ hsum

theorem subEg_den (tree : List Int) (ps0 : PS) (j adr ada r : Nat) (acc : Int) (h : Loc2 ps0 j adr ada r acc)
    (h0 : 0 < r) (hr : r < 1073741824) :
    vdenL s64 tree (penv1 ps0) (subEg j) = some ((r - lowb r : Nat) : Int) := by
  have e1 := env_r ps0 j adr ada r acc h (i32_valid r (by omega) (by omega))
  have hl := lowb_pos r h0
  have hl' := lowb_le r h0
  have hs : (subEg j).scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, den_binary, den_variable, e1, Option.bind_some,
    lowEg_den (penv1 ps0) j r h0 (by omega) e1, Option.bind_some]
  have : binaryValue .sub (r : Int) (lowb r : Int) = ((r - lowb r : Nat) : Int) := by
    show (r : Int) - (lowb r : Int) = _; omega
  rw [this]
  exact conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega))


theorem loc2_acc (ps0 : PS) (j adr ada : Nat) (r acc acc' : Int) (h : Loc2 ps0 j adr ada r acc) :
    Loc2 (⟨ps0.mem.set ada ⟨s64,acc'⟩,ps0.bs⟩ : PS) j adr ada r acc' := by
  obtain ⟨b1,b2,m1,m2,hne⟩ := h
  have l2 : ada < ps0.mem.length := (List.getElem?_eq_some_iff.mp m2).1
  refine ⟨b1,b2,?_,?_,hne⟩
  · show (ps0.mem.set ada _)[adr]? = _
    rw [List.getElem?_set_ne (Ne.symm hne)]; exact m1
  · show (ps0.mem.set ada _)[ada]? = _
    rw [List.getElem?_set_self l2]

theorem iterSg (tree : List Int) (ps0 : PS) (j adr ada r : Nat) (acc x : Int) (h : Loc2 ps0 j adr ada r acc)
    (h0 : 0 < r) (hr : r < tree.length) (hlen : tree.length ≤ 1073741824) (hx : tree[r]? = some x)
    (hxv : s64.valid x = true) (hacc : s64.valid acc = true) (hsum : s64.valid (acc + x) = true) (fu : Nat) :
    ∃ r1, pexecW s64 fu (loopBodySg j) ps0 tree = some r1 ∧
      r1.ps = upd2 ps0 adr ada ((r - lowb r : Nat) : Int) (acc + x) ∧
      r1.vec = tree ∧ r1.ret = none ∧ r1.cost ≤ 24 ∧ r1.need ≤ ps0.mem.length + ps0.bs.length + 26 ∧ r1.wk = 0 := by
  have hl := lowb_pos r h0
  have hl' := lowb_le r h0
  have hval := accEg_den tree ps0 j adr ada r acc x h (by omega) hx hxv hacc hsum
  obtain ⟨b1,b2,m1,m2,hne⟩ := h
  have st1 := pstmtW_assign_ok s64 ps0 tree (j+1) s64 (accEg j) (acc + x) hval ⟨ada,true⟩ ⟨s64,acc⟩ b2 m2 rfl hacc rfl
    (acc + x) (conv_signed s64 rfl rfl _ hsum)
  have a1 := (pexecW_prim s64 fu (assign2g j) _ _).trans st1
  have a2 := seqW_some a1 rfl (pexecW_skip s64 fu (⟨ps0.mem.set ada ⟨s64,acc + x⟩,ps0.bs⟩ : PS) tree)
  have a3 := pexecW_scope s64 fu _ _ _ _ a2
  have a4 := Proofs.PexecKit.scope_take ps0 (⟨ps0.mem.set ada ⟨s64,acc + x⟩,ps0.bs⟩ : PS) (by simp) (by simp)
  simp only [a4] at a3
  have h' : Loc2 ps0 j adr ada r acc := ⟨b1,b2,m1,m2,hne⟩
  have L1 := loc2_acc ps0 j adr ada r acc (acc + x) h'
  have hstep := subEg_den tree _ j adr ada r (acc + x) L1 h0 (by omega)
  have l1 : adr < ps0.mem.length := (List.getElem?_eq_some_iff.mp m1).1
  have c1 : (ps0.mem.set ada ⟨s64,acc + x⟩)[adr]? = some ⟨i32,(r : Int)⟩ := by
    rw [List.getElem?_set_ne (Ne.symm hne)]; exact m1
  have st2 := pstmtW_assign_ok s64 (⟨ps0.mem.set ada ⟨s64,acc + x⟩,ps0.bs⟩ : PS) tree j i32 (subEg j)
    ((r - lowb r : Nat) : Int) hstep ⟨adr,true⟩ ⟨i32,(r : Int)⟩ b1 c1 rfl
    (show i32.valid (r : Int) = true from i32_valid _ (by omega) (by omega)) rfl
    ((r - lowb r : Nat) : Int) (conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega)))
  have b1' := (pexecW_prim s64 fu (stepSg j) _ _).trans st2
  have b2' := seqW_some b1' rfl (pexecW_skip s64 fu (upd2 ps0 adr ada ((r - lowb r : Nat) : Int) (acc + x)) tree)
  have c1' := seqW_some a3 rfl b2'
  refine ⟨_, c1', rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp_accEg, vwp_subEg]
  · have := upd2_size ps0 adr ada ((r - lowb r : Nat) : Int) (acc + x)
    simp [vwp_accEg, vwp_subEg, Container.nodes]
    omega
  · simp


theorem upd2_same (ps0 : PS) (j adr ada : Nat) (acc : Int) (h : Loc2 ps0 j adr ada 0 acc) :
    upd2 ps0 adr ada 0 acc = ps0 := by
  obtain ⟨b1,b2,m1,m2,hne⟩ := h
  obtain ⟨mem,bs⟩ := ps0
  simp only [upd2, PS.mk.injEq, and_true]
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_set, List.length_set]
  have l1 : adr < mem.length := (List.getElem?_eq_some_iff.mp m1).1
  have l2 : ada < mem.length := (List.getElem?_eq_some_iff.mp m2).1
  by_cases h1 : adr = i <;> by_cases h2 : ada = i <;> simp_all

theorem loop_runSg (tree : List Int) (hlen : tree.length ≤ 1073741824) (hv : ∀ x ∈ tree, s64.valid x = true) :
    ∀ (r : Nat) (acc : Int) (ps0 : PS) (j adr ada : Nat), Loc2 ps0 j adr ada r acc → r < tree.length →
      s64.valid acc = true → (∀ x ∈ chainS tree r acc, s64.valid x = true) →
      ∀ fu, stepsS r + 1 ≤ fu →
      ∃ res, pexecW s64 fu (loopCSg j) ps0 tree = some res ∧
        res.ps = upd2 ps0 adr ada 0 (acc + fsumR tree r) ∧
        res.vec = tree ∧ res.ret = none ∧ res.cost ≤ 31 * stepsS r + 7 ∧
        res.need ≤ ps0.mem.length + ps0.bs.length + 26 ∧ res.wk = 0 := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro acc ps0 j adr ada hl hr hacc hch fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    have hc := condSg_valL tree ps0 j adr ada r acc hl (by omega)
    by_cases h0 : 0 < r
    · rw [if_pos h0] at hc
      obtain ⟨r0, rfl⟩ : ∃ r0, r = r0 + 1 := ⟨r - 1, by omega⟩
      have hL := lowb_pos (r0+1) (by omega)
      have hL' := lowb_le (r0+1) (by omega)
      obtain ⟨x, hx⟩ : ∃ x, tree[r0+1]? = some x := ⟨tree[r0+1], by simp [hr]⟩
      have hxv := hv x (List.mem_of_getElem? hx)
      have hget : tree.getD (r0+1) 0 = x := by simp [List.getD_eq_getElem?_getD, hx]
      have hch' : ∀ y ∈ chainS tree (r0 + 1 - lowb (r0+1)) (acc + x), s64.valid y = true := by
        intro y hy
        apply hch y
        rw [chainS]; rw [hget]
        exact List.mem_cons_of_mem _ hy
      have hsum : s64.valid (acc + x) = true := by
        apply hch
        rw [chainS, hget]; exact List.mem_cons_self
      obtain ⟨r1, h1', p1, v1, ret1, c1, n1, w1⟩ :=
        iterSg tree ps0 j adr ada (r0+1) acc x hl h0 hr hlen hx hxv hacc hsum (fu'+1)
      have hsteps : stepsS (r0+1) = 1 + stepsS (r0 + 1 - lowb (r0+1)) := by rw [stepsS]
      have hl1 := loc2_upd ps0 j adr ada ((r0+1 : Nat) : Int) acc ((r0 + 1 - lowb (r0+1) : Nat) : Int) (acc + x) hl
      obtain ⟨r2, h2, p2, v2, ret2, c2, n2, w2⟩ :=
        ih (r0 + 1 - lowb (r0+1)) (by omega) (acc + x) (upd2 ps0 adr ada ((r0 + 1 - lowb (r0+1) : Nat) : Int) (acc + x))
          j adr ada hl1 (by omega) hsum hch' fu' (by omega)
      rw [pexecW_while, hc]
      simp only [Bind.bind, Option.bind, h1', ret1, p1, v1, h2, vwp_condSg]
      refine ⟨⟨r2.ps, r2.vec, r2.ret, 3+1+r1.cost+r2.cost, max (ps0.mem.length +
        ps0.bs.length + 3 + 2) (max r1.need r2.need), r1.wk+r2.wk⟩, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show r2.ps = _
        rw [p2, upd2_upd2 ps0 adr ada hl.2.2.2.2, fsumR, hget, Int.add_assoc]
      · exact v2
      · exact ret2
      · simp; omega
      · have := upd2_size ps0 adr ada ((r0 + 1 - lowb (r0+1) : Nat) : Int) (acc + x)
        simp only [] at n2 ⊢
        simp [this] at n2
        simp
        omega
      · simp [w1, w2]
    · rw [if_neg h0] at hc
      have hr0 : r = 0 := by omega
      subst hr0
      rw [pexecW_while, hc]
      simp only [Bind.bind, Option.bind, ite_true, vwp_condSg]
      refine ⟨_, rfl, ?_, rfl, rfl, ?_, ?_, rfl⟩
      · simp [fsumR]
        exact (upd2_same ps0 j adr ada acc hl).symm
      · simp [stepsS]
      · simp


-- One writable binding `j` whose cell at `ad` holds `a` of type `ty`.
def LocT (ps0 : PS) (j ad : Nat) (ty : Ty) (a : Int) : Prop :=
  ps0.bs[j]? = some ⟨ad,true⟩ ∧ ps0.mem[ad]? = some ⟨ty,a⟩

def appT (ps : PS) (ty : Ty) (v : Int) : PS := ⟨ps.mem ++ [⟨ty,v⟩],ps.bs ++ [⟨ps.mem.length,true⟩]⟩

@[simp] theorem appT_mem_length (ps : PS) (ty : Ty) (v : Int) : (appT ps ty v).mem.length = ps.mem.length + 1 := by
  simp [appT]
@[simp] theorem appT_bs_length (ps : PS) (ty : Ty) (v : Int) : (appT ps ty v).bs.length = ps.bs.length + 1 := by
  simp [appT]
@[simp] theorem upd2_mem_length (ps : PS) (adr ada : Nat) (r acc : Int) : (upd2 ps adr ada r acc).mem.length = ps.mem.length := by
  simp [upd2]
@[simp] theorem upd2_bs_length (ps : PS) (adr ada : Nat) (r acc : Int) : (upd2 ps adr ada r acc).bs.length = ps.bs.length := by
  simp [upd2]

theorem locT_new (ps0 : PS) (ty : Ty) (v : Int) : LocT (appT ps0 ty v) ps0.bs.length ps0.mem.length ty v := by
  refine ⟨?_,?_⟩ <;> simp [appT]

theorem locT_app_old (ps0 : PS) (j ad : Nat) (ty ty' : Ty) (a v : Int) (h : LocT ps0 j ad ty a) :
    LocT (appT ps0 ty' v) j ad ty a := by
  obtain ⟨hb,hm⟩ := h
  have h1 : j < ps0.bs.length := (List.getElem?_eq_some_iff.mp hb).1
  have h2 : ad < ps0.mem.length := (List.getElem?_eq_some_iff.mp hm).1
  refine ⟨?_,?_⟩
  · simp only [appT]; rw [List.getElem?_append_left h1]; exact hb
  · simp only [appT]; rw [List.getElem?_append_left h2]; exact hm

theorem locT_upd2 (ps0 : PS) (j ad adr ada : Nat) (ty : Ty) (a r acc : Int) (h : LocT ps0 j ad ty a)
    (h1 : ad ≠ adr) (h2 : ad ≠ ada) : LocT (upd2 ps0 adr ada r acc) j ad ty a := by
  obtain ⟨hb,hm⟩ := h
  refine ⟨hb,?_⟩
  simp only [upd2]
  rw [List.getElem?_set_ne (Ne.symm h1), List.getElem?_set_ne (Ne.symm h2)]
  exact hm

theorem envT (ps0 : PS) (j ad : Nat) (ty : Ty) (a : Int) (h : LocT ps0 j ad ty a) (hv : ty.valid a = true) :
    penv1 ps0 (j+1) ty = some a := by
  obtain ⟨hb,hm⟩ := h
  show penv ps0 j ty = some a
  simp [penv, hb, hm, hv]

theorem decl_stepT (ps0 : PS) (vec : List Int) (ty : Ty) (j ad : Nat) (a : Int) (h : LocT ps0 j ad ty a)
    (hv : ty.valid a = true) (ty0 : Ty) :
    pstmtW ty0 (.declare ty true (.variable ty (j+1))) ps0 vec =
      some ⟨appT ps0 ty a,vec,none,2,ps0.mem.length+ps0.bs.length+5,0⟩ := by
  obtain ⟨hb,hm⟩ := h
  have hd : vdenL ty0 vec (penv1 ps0) (NExpr.variable ty (j+1)) = some a := by
    rw [vdenL_scalar _ _ _ _ rfl, den_variable]
    show penv ps0 j ty = some a
    simp [penv, hb, hm, hv]
  have := pstmtW_declare_ok ty0 ps0 vec ty true (.variable ty (j+1)) a hd a (Ty.convert_of_valid ty a hv)
  rw [this]
  simp [vwp, appT, NExpr.nodes]


abbrev dT (ty : Ty) (k : Nat) : Command := .primitive (.declare ty true (.variable ty k))
abbrev dZ : Command := .primitive (.declare s64 true (.cast s64 (.literal i32 0)))
abbrev scopedLoop (j : Nat) : Command := .scope (.sequence (loopCSg j) (.primitive .skip))
abbrev retE : NExpr := .binary s64 .sub (.variable s64 6) (.variable s64 10)
abbrev bodyRange : Command :=
  .sequence (dT i32 2) (.sequence dZ (.sequence (scopedLoop 2) (.sequence (dT s64 4) (.sequence (dT s64 5)
    (.sequence (dT i32 1) (.sequence dZ (.sequence (scopedLoop 6) (.sequence (dT s64 8) (.sequence (dT s64 9)
      (.sequence (.primitive (.ret retE)) Sk))))))))))

theorem body_eqRange : Proofs.FenwickTreeInstance.FenwickTree_long_long_sum_2.body = bodyRange := rfl

theorem step_declT {fu : Nat} {rest : Command} {ps0 : PS} {vec : List Int} {ty : Ty} {j ad : Nat} {a : Int}
    (h : LocT ps0 j ad ty a) (hv : ty.valid a = true) (ty0 : Ty) {r2 : PRW}
    (h2 : pexecW ty0 fu rest (appT ps0 ty a) vec = some r2) :
    pexecW ty0 fu (.sequence (dT ty (j+1)) rest) ps0 vec =
      some ⟨r2.ps,r2.vec,r2.ret,2+r2.cost,max (ps0.mem.length+ps0.bs.length+5) r2.need,0+r2.wk⟩ :=
  seqW_some ((pexecW_prim ty0 fu _ ps0 vec).trans (decl_stepT ps0 vec ty j ad a h hv ty0)) rfl h2

theorem step_declZ {fu : Nat} {rest : Command} {ps0 : PS} {vec : List Int} {r2 : PRW}
    (h2 : pexecW s64 fu rest (appT ps0 s64 0) vec = some r2) :
    pexecW s64 fu (.sequence dZ rest) ps0 vec =
      some ⟨r2.ps,r2.vec,r2.ret,3+r2.cost,max (ps0.mem.length+ps0.bs.length+6) r2.need,0+r2.wk⟩ := by
  have hv0 : vdenL s64 vec (penv1 ps0) (NExpr.cast s64 (.literal i32 0)) = some 0 := by
    rw [vdenL_scalar _ _ _ _ rfl, den_cast]
    show ((NExpr.literal i32 0).denote (penv1 ps0)).bind s64.convert = _
    rw [den_literal, if_pos (show i32.valid 0 = true from rfl), Option.bind_some]
    exact conv_signed s64 rfl rfl _ rfl
  have d := pstmtW_declare_ok s64 ps0 vec s64 true (NExpr.cast s64 (.literal i32 0)) 0 hv0 0
    (conv_signed s64 rfl rfl _ rfl)
  have := seqW_some ((pexecW_prim s64 fu _ ps0 vec).trans d) rfl h2
  rw [this]
  simp [vwp, NExpr.nodes, appT]

theorem scoped_loop (tree : List Int) (hlen : tree.length ≤ 1073741824) (hv : ∀ x ∈ tree, s64.valid x = true)
    (r : Nat) (ps0 : PS) (j adr ada : Nat) (hl : Loc2 ps0 j adr ada r 0) (hr : r < tree.length)
    (hch : ∀ x ∈ chainS tree r 0, s64.valid x = true) (fu : Nat) (hfu : stepsS r + 1 ≤ fu) :
    ∃ res, pexecW s64 fu (scopedLoop j) ps0 tree = some res ∧
      res.ps = upd2 ps0 adr ada 0 (0 + fsumR tree r) ∧ res.vec = tree ∧ res.ret = none ∧
      res.cost ≤ 31 * stepsS r + 8 ∧ res.need ≤ ps0.mem.length + ps0.bs.length + 26 ∧ res.wk = 0 := by
  obtain ⟨rL, hL, pL, vL, retL, cL, nL, wL⟩ := loop_runSg tree hlen hv r 0 ps0 j adr ada hl hr (by rfl) hch fu hfu
  have f2 := seqW_some hL retL (pexecW_skip s64 fu rL.ps rL.vec)
  have f3 := pexecW_scope s64 fu _ _ _ _ f2
  have take_eq : (⟨rL.ps.mem.take ps0.mem.length, rL.ps.bs.take ps0.bs.length⟩ : PS) =
      upd2 ps0 adr ada 0 (0 + fsumR tree r) := by
    rw [pL]
    have hm : (upd2 ps0 adr ada 0 (0 + fsumR tree r)).mem.take ps0.mem.length =
        (upd2 ps0 adr ada 0 (0 + fsumR tree r)).mem := List.take_of_length_le (by simp)
    have hb : (upd2 ps0 adr ada 0 (0 + fsumR tree r)).bs.take ps0.bs.length =
        (upd2 ps0 adr ada 0 (0 + fsumR tree r)).bs := List.take_of_length_le (by simp)
    show StraightLine.PS.mk _ _ = _
    rw [hm, hb]
  simp only [take_eq] at f3
  have hsz : rL.ps.mem.length + rL.ps.bs.length = ps0.mem.length + ps0.bs.length := by rw [pL]; simp
  refine ⟨_, f3, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [vL]
  · simp [retL]
  · simp; omega
  · simp; omega
  · simp [wL]


def R0 (P : List Cell) (l r : Int) : PS := ⟨P ++ [⟨i32,l⟩,⟨i32,r⟩],[⟨P.length,true⟩,⟨P.length+1,true⟩]⟩

@[simp] theorem R0_mem_length (P : List Cell) (l r : Int) : (R0 P l r).mem.length = P.length + 2 := by simp [R0]
@[simp] theorem R0_bs_length (P : List Cell) (l r : Int) : (R0 P l r).bs.length = 2 := by simp [R0]

theorem R0_loc0 (P : List Cell) (l r : Int) : LocT (R0 P l r) 0 P.length i32 l := by
  refine ⟨by simp [R0],?_⟩
  simp [R0]

theorem R0_loc1 (P : List Cell) (l r : Int) : LocT (R0 P l r) 1 (P.length+1) i32 r := by
  refine ⟨by simp [R0],?_⟩
  simp [R0]

def X2 (P : List Cell) (l r : Int) : PS := appT (appT (R0 P l r) i32 r) s64 0
def X3 (P : List Cell) (l r A : Int) : PS := upd2 (X2 P l r) (P.length+2) (P.length+3) 0 A
def X5 (P : List Cell) (l r A : Int) : PS := appT (appT (X3 P l r A) s64 A) s64 A
def X7 (P : List Cell) (l r A : Int) : PS := appT (appT (X5 P l r A) i32 l) s64 0
def X8 (P : List Cell) (l r A B : Int) : PS := upd2 (X7 P l r A) (P.length+6) (P.length+7) 0 B
def X10 (P : List Cell) (l r A B : Int) : PS := appT (appT (X8 P l r A B) s64 B) s64 B

@[simp] theorem X2_mem (P : List Cell) (l r : Int) : (X2 P l r).mem.length = P.length + 4 := by simp [X2]
@[simp] theorem X2_bs (P : List Cell) (l r : Int) : (X2 P l r).bs.length = 4 := by simp [X2]
@[simp] theorem X3_mem (P : List Cell) (l r A : Int) : (X3 P l r A).mem.length = P.length + 4 := by simp [X3]
@[simp] theorem X3_bs (P : List Cell) (l r A : Int) : (X3 P l r A).bs.length = 4 := by simp [X3]
@[simp] theorem X5_mem (P : List Cell) (l r A : Int) : (X5 P l r A).mem.length = P.length + 6 := by simp [X5]
@[simp] theorem X5_bs (P : List Cell) (l r A : Int) : (X5 P l r A).bs.length = 6 := by simp [X5]
@[simp] theorem X7_mem (P : List Cell) (l r A : Int) : (X7 P l r A).mem.length = P.length + 8 := by simp [X7]
@[simp] theorem X7_bs (P : List Cell) (l r A : Int) : (X7 P l r A).bs.length = 8 := by simp [X7]
@[simp] theorem X8_mem (P : List Cell) (l r A B : Int) : (X8 P l r A B).mem.length = P.length + 8 := by simp [X8]
@[simp] theorem X8_bs (P : List Cell) (l r A B : Int) : (X8 P l r A B).bs.length = 8 := by simp [X8]
@[simp] theorem X10_mem (P : List Cell) (l r A B : Int) : (X10 P l r A B).mem.length = P.length + 10 := by simp [X10]
@[simp] theorem X10_bs (P : List Cell) (l r A B : Int) : (X10 P l r A B).bs.length = 10 := by simp [X10]

theorem vwp_retE : vwp retE = (3,3) := rfl

theorem take_appT (ps : PS) (ty : Ty) (v : Int) (n : Nat) (h : n ≤ ps.mem.length) :
    (appT ps ty v).mem.take n = ps.mem.take n := by
  simp only [appT]; exact List.take_append_of_le_length h

theorem take_upd2 (ps : PS) (adr ada : Nat) (r acc : Int) (n : Nat) (h1 : n ≤ adr) (h2 : n ≤ ada) :
    (upd2 ps adr ada r acc).mem.take n = ps.mem.take n := by
  simp only [upd2]
  rw [List.take_set_of_le h1, List.take_set_of_le h2]

theorem R0_take (P : List Cell) (l r : Int) : (R0 P l r).mem.take P.length = P := by
  simp only [R0]; rw [List.take_append_of_le_length (le_refl _)]; simp

theorem X2_loc2 (P : List Cell) (l r : Int) : Loc2 (X2 P l r) 2 (P.length+2) (P.length+3) r 0 := by
  refine ⟨?_,?_,?_,?_,by omega⟩ <;> simp [X2, appT, R0]

theorem X7_loc2 (P : List Cell) (l r A : Int) : Loc2 (X7 P l r A) 6 (P.length+6) (P.length+7) l 0 := by
  refine ⟨?_,?_,?_,?_,by omega⟩ <;> simp [X7, appT, X5, X3, X2, upd2, R0]

theorem body_exec_range (P : List Cell) (tree : List Int) (hlen : tree.length ≤ 1073741824)
    (hv : ∀ x ∈ tree, s64.valid x = true) (l r : Nat) (hl : l < tree.length) (hr : r < tree.length)
    (hchr : ∀ x ∈ chainS tree r 0, s64.valid x = true) (hchl : ∀ x ∈ chainS tree l 0, s64.valid x = true)
    (hdiff : s64.valid (fsumR tree r - fsumR tree l) = true) (fu : Nat) (hfr : stepsS r + 1 ≤ fu)
    (hfl : stepsS l + 1 ≤ fu) :
    ∃ res, pexecW s64 fu bodyRange (R0 P l r) tree = some res ∧ res.ret = some (fsumR tree r - fsumR tree l) ∧
      res.vec = tree ∧ res.cost ≤ 31 * stepsS r + 31 * stepsS l + 100 ∧ res.need ≤ P.length + 70 ∧ res.wk = 0 ∧
      res.ps.mem.take P.length = P := by
  have hlv : i32.valid (l : Int) = true := i32_valid l (by omega) (by omega)
  have hrv : i32.valid (r : Int) = true := i32_valid r (by omega) (by omega)
  have resv : ∀ q : Nat, q < tree.length → (∀ x ∈ chainS tree q 0, s64.valid x = true) →
      s64.valid (0 + fsumR tree q) = true := by
    intro q hq hch
    rcases chain_last tree q 0 with h | h
    · subst h; simp [fsumR]; rfl
    · exact hch _ (by simpa using h)
  have Ar := resv r hr hchr
  have Al := resv l hl hchl
  -- the first query
  obtain ⟨q1, hq1, pq1, vq1, retq1, cq1, nq1, wq1⟩ :=
    scoped_loop tree hlen hv r (X2 P l r) 2 (P.length+2) (P.length+3) (X2_loc2 P l r) hr hchr fu hfr
  have h3 := loc2_upd _ 2 (P.length+2) (P.length+3) r 0 0 (0 + fsumR tree r) (X2_loc2 P l r)
  have LA3 : LocT (X3 P l r (0 + fsumR tree r)) 3 (P.length+3) s64 (0 + fsumR tree r) := ⟨h3.2.1,h3.2.2.2.1⟩
  have LA4 : LocT (appT (X3 P l r (0 + fsumR tree r)) s64 (0 + fsumR tree r)) 4 (P.length+4) s64 (0 + fsumR tree r) := by
    simpa using locT_new (X3 P l r (0 + fsumR tree r)) s64 (0 + fsumR tree r)
  have LA5 : LocT (X5 P l r (0 + fsumR tree r)) 5 (P.length+5) s64 (0 + fsumR tree r) := by
    simpa [X5] using locT_new (appT (X3 P l r (0 + fsumR tree r)) s64 (0 + fsumR tree r)) s64 (0 + fsumR tree r)
  have LL0 : LocT (X5 P l r (0 + fsumR tree r)) 0 P.length i32 l := by
    have a0 := R0_loc0 P l r
    have a1 := locT_app_old _ _ _ _ i32 _ r a0
    have a2 := locT_app_old _ _ _ _ s64 _ 0 a1
    have a3 := locT_upd2 _ _ _ (P.length+2) (P.length+3) _ _ 0 (0 + fsumR tree r) a2 (by omega) (by omega)
    have a4 := locT_app_old _ _ _ _ s64 _ (0 + fsumR tree r) a3
    exact locT_app_old _ _ _ _ s64 _ (0 + fsumR tree r) a4
  have LL6 : LocT (appT (X5 P l r (0 + fsumR tree r)) i32 l) 6 (P.length+6) i32 l := by
    simpa using locT_new (X5 P l r (0 + fsumR tree r)) i32 l
  -- the second query
  obtain ⟨q2, hq2, pq2, vq2, retq2, cq2, nq2, wq2⟩ :=
    scoped_loop tree hlen hv l (X7 P l r (0 + fsumR tree r)) 6 (P.length+6) (P.length+7)
      (X7_loc2 P l r (0 + fsumR tree r)) hl hchl fu hfl
  have h8 := loc2_upd _ 6 (P.length+6) (P.length+7) l 0 0 (0 + fsumR tree l) (X7_loc2 P l r (0 + fsumR tree r))
  have LB8 : LocT (X8 P l r (0 + fsumR tree r) (0 + fsumR tree l)) 7 (P.length+7) s64 (0 + fsumR tree l) :=
    ⟨h8.2.1,h8.2.2.2.1⟩
  have LB9 : LocT (appT (X8 P l r (0 + fsumR tree r) (0 + fsumR tree l)) s64 (0 + fsumR tree l)) 8 (P.length+8) s64
      (0 + fsumR tree l) := by
    simpa using locT_new (X8 P l r (0 + fsumR tree r) (0 + fsumR tree l)) s64 (0 + fsumR tree l)
  have LB10 : LocT (X10 P l r (0 + fsumR tree r) (0 + fsumR tree l)) 9 (P.length+9) s64 (0 + fsumR tree l) := by
    simpa [X10] using locT_new (appT (X8 P l r (0 + fsumR tree r) (0 + fsumR tree l)) s64 (0 + fsumR tree l)) s64
      (0 + fsumR tree l)
  have LA10 : LocT (X10 P l r (0 + fsumR tree r) (0 + fsumR tree l)) 5 (P.length+5) s64 (0 + fsumR tree r) := by
    have b1 := locT_app_old _ _ _ _ i32 _ l LA5
    have b2 := locT_app_old _ _ _ _ s64 _ 0 b1
    have b3 := locT_upd2 _ _ _ (P.length+6) (P.length+7) _ _ 0 (0 + fsumR tree l) b2 (by omega) (by omega)
    have b4 := locT_app_old _ _ _ _ s64 _ (0 + fsumR tree l) b3
    exact locT_app_old _ _ _ _ s64 _ (0 + fsumR tree l) b4
  -- the result
  have ev : vdenL s64 tree (penv1 (X10 P l r (0 + fsumR tree r) (0 + fsumR tree l))) retE =
      some ((0 + fsumR tree r) - (0 + fsumR tree l)) := by
    have e6 : penv1 (X10 P l r (0 + fsumR tree r) (0 + fsumR tree l)) 6 s64 = some (0 + fsumR tree r) := by
      exact envT _ 5 _ s64 _ LA10 Ar
    have e10 : penv1 (X10 P l r (0 + fsumR tree r) (0 + fsumR tree l)) 10 s64 = some (0 + fsumR tree l) := by
      exact envT _ 9 _ s64 _ LB10 Al
    rw [vdenL_scalar _ _ _ _ rfl, den_binary, den_variable, den_variable, e6, e10]
    simp only [Option.bind_some]
    have : binaryValue .sub (0 + fsumR tree r) (0 + fsumR tree l) = (0 + fsumR tree r) - (0 + fsumR tree l) := rfl
    rw [this]
    exact conv_signed s64 rfl rfl _ (by simpa using hdiff)
  have e11 := seqW_ret (b := Sk) ((pexecW_prim s64 fu _ _ tree).trans (pstmtW_ret_ok s64 _ tree retE _ ev)) rfl
  have e10 := step_declT (fu := fu) LB9 Al s64 e11
  have e9 := step_declT (fu := fu) LB8 Al s64 e10
  have e8 := seqW_some (b := _) hq2 retq2 (by rw [pq2, vq2]; exact e9)
  have e7 := step_declZ (fu := fu) e8
  have e6' := step_declT (fu := fu) LL0 hlv s64 e7
  have e5 := step_declT (fu := fu) LA4 Ar s64 e6'
  have e4 := step_declT (fu := fu) LA3 Ar s64 e5
  have e3 := seqW_some (b := _) hq1 retq1 (by rw [pq1, vq1]; exact e4)
  have e2 := step_declZ (fu := fu) e3
  have e1 := step_declT (fu := fu) (R0_loc1 P l r) hrv s64 e2
  refine ⟨_, e1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp [vq2]
  · simp [vwp_retE]
    omega
  · simp only [X2_mem, X2_bs, X7_mem, X7_bs] at nq1 nq2
    simp [vwp_retE]
    omega
  · simp [wq1, wq2]
  · simp only [X10, X8, X7, X5, X3, X2]
    rw [take_appT _ _ _ _ (by simp <;> omega), take_appT _ _ _ _ (by simp <;> omega), take_upd2 _ _ _ _ _ _ (by omega) (by omega),
      take_appT _ _ _ _ (by simp <;> omega), take_appT _ _ _ _ (by simp <;> omega), take_appT _ _ _ _ (by simp <;> omega),
      take_appT _ _ _ _ (by simp <;> omega), take_upd2 _ _ _ _ _ _ (by omega) (by omega),
      take_appT _ _ _ _ (by simp <;> omega), take_appT _ _ _ _ (by simp <;> omega), R0_take]


theorem prepare_frr (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : Proofs.VectorSumCall.VOK caller vslot vb V vsc m vbuf) (e1 e2 : NExpr) (v1 v2 : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (hty1 : e1.resultType = i32) (hty2 : e2.resultType = i32)
    (value1 : e1.denote (envOf caller) = some v1) (value2 : e2.denote (envOf caller) = some v2)
    (hv1 : i32.valid v1 = true) (hv2 : i32.valid v2 = true) :
    ∃ t, Good (caller.charge 1 1) t (e1.nodes+e2.nodes) (max e1.nodes e2.nodes) ∧
      ∃ Sinit, prepare caller Proofs.FenwickTreeInstance.FenwickTree_long_long_sum_2.parameters
          [.vectorReference vslot,.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.vector 0,.scalar 0,.scalar 1] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨i32,v1⟩,⟨i32,v2⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer s64,false,.root vsc⟩]⟩ ∧
        Sinit.scalars.work = t.scalars.work+4 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc s64 false m vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (by simp)
  have rvec : resolve caller (.vector s64 false) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc s64 false) := by
    simp [resolve,ok.slot,ok.binding,resolved]
  obtain ⟨t1,ran1,good1⟩ := scalar_eval e1 (caller.charge 1 1) v1 hs1
    (by rw [envOf_core (core_charge caller 1 1)]; exact value1)
  obtain ⟨t,ran2,good2⟩ := scalar_eval e2 t1 v2 hs2
    (by rw [envOf_core good1.1, envOf_core (core_charge caller 1 1)]; exact value2)
  have good := good1.trans good2
  refine ⟨t,good,?_⟩
  have res1 : resolve (caller.charge 1 1) (.scalar i32 false true) (.value e1) = some (t1,.scalar i32 true v1) := by
    simp [resolve,hty1,ran1]
  have res2 : resolve t1 (.scalar i32 false true) (.value e2) = some (t,.scalar i32 true v2) := by
    simp [resolve,hty2,ran2]
  have frameT : t.frame = caller.frame := by rw [good.1.1]; rfl
  have fs : t.frame.state = caller.frame.state := by rw [frameT]
  have fr : t.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t.scalars.memory = caller.scalars.memory := by rw [good.1.2.2.2.1]; rfl
  have hbind : t.scalars.bindings = caller.scalars.bindings := by rw [good.1.2.2.2.2.1]; rfl
  have hbase : t.scalars.baseMemory = caller.scalars.baseMemory := by rw [good.1.2.2.2.2.2]; rfl
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
  have hp : Proofs.FenwickTreeInstance.FenwickTree_long_long_sum_2.parameters =
      [.vector s64 false,.scalar i32 false true,.scalar i32 false true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec,res1,res2]
  simp [fs,fr,fb,hmem,hbind,hbase,bound,bindAll,bindOne,CppState.bindArgument,hv1,hv2,callerP,
    NState.observe,CppState.State.observe]
  left
  have g := good.2.2.2.2.1
  simp [NState.charge,NState.observe,CppState.State.observe] at g
  omega


set_option maxHeartbeats 4000000 in
theorem fenwick_range_correct (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : Proofs.VectorSumCall.VOK caller vslot vb V vsc m vbuf) (vec : List Int)
    (hitems : vbuf.items = vec.map Value.integer) (hlen : vec.length ≤ 1073741824)
    (hbvalid : vbuf.Valid (accepts (.integer s64))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit s64)
    (howner : vbuf.owner = V)
    (e1 e2 : NExpr) (l r : Nat) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = i32) (ht2 : e2.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (l : Int)) (value2 : e2.denote (envOf caller) = some (r : Int))
    (hl : l < vec.length) (hr : r < vec.length)
    (hv : ∀ x ∈ vec, s64.valid x = true) (hchr : ∀ x ∈ chainS vec r 0, s64.valid x = true)
    (hchl : ∀ x ∈ chainS vec l 0, s64.valid x = true)
    (hdiff : s64.valid (fsumR vec r - fsumR vec l) = true) :
    ∃ Sinit fuel res, prepare caller Proofs.FenwickTreeInstance.FenwickTree_long_long_sum_2.parameters
        [.vectorReference vslot,.value e1,.value e2] = some Sinit ∧
      Proofs.FenwickTreeInstance.FenwickTree_long_long_sum_2.callFuel fuel caller [.vectorReference vslot,.value e1,.value e2] =
        .finished (res,.scalar (fsumR vec r - fsumR vec l)) ∧
      ScalarPost3 caller Sinit res (e1.nodes+e2.nodes) (62*Nat.log2 vec.length+300) caller.scalars.memory 0 V vec := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_frr caller ok e1 e2 (l : Int) (r : Int) hs1 hs2 ht1 ht2 value1 value2
      (i32_valid l (by omega) (by omega)) (i32_valid r (by omega) (by omega))
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
  have hsr := stepsS_log vec.length r hr
  have hsl := stepsS_log vec.length l hl
  obtain ⟨rr,hexec,hret,hrvec,hcost,hneed,hwk,htake⟩ :=
    body_exec_range (callerP caller) vec hlen hv l r hl hr hchr hchl hdiff (Nat.log2 vec.length + 2) (by omega) (by omega)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have gw1 := good.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hpost := call_vecw vc false (fun h => absurd h (by decide)) caller Proofs.FenwickTreeInstance.FenwickTree_long_long_sum_2
    [.vectorReference vslot,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨i32,(l : Int)⟩ : Cell),⟨i32,(r : Int)⟩])
    [(⟨(callerP caller).length,true⟩ : CppState.Binding),⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [VectorFillCall.take_P caller]) ok.base (by decide) (Nat.log2 vec.length + 2) rr
    (by rw [body_eqRange]; exact hexec) _ hret s64 rfl hdiff (by omega) (by simp) (e1.nodes+e2.nodes)
    (62*Nat.log2 vec.length+300) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hle : caller.scalars.memory.length ≤ (callerP caller).length := by omega
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    calc rr.ps.mem.take caller.scalars.memory.length
        = (rr.ps.mem.take (callerP caller).length).take caller.scalars.memory.length := by
          rw [List.take_take, Nat.min_eq_left hle]
      _ = (callerP caller).take caller.scalars.memory.length := by rw [htake]
      _ = caller.scalars.memory := by simp only [callerP]; exact List.take_left' rfl
  rw [hs', hrvec, hwk] at post
  exact post

end Proofs.FenwickRangeCall
