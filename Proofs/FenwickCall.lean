import Proofs.PrefixSumsCall
import Proofs.FenwickMath
import Proofs.Generated.FenwickTree

namespace Proofs.FenwickCall
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

abbrev lowE : NExpr := .cast i32 (.binary u32 .band (.cast u32 (.variable i32 1))
  (.binary u32 .sub (.literal u32 0) (.cast u32 (.variable i32 1))))

theorem lowE_den (env : Nat → Ty → Option Int) (k : Nat) (h0 : 0 < k) (h1 : k < 2147483648)
    (e : env 1 i32 = some (k : Int)) : lowE.denote env = some (lowb k : Int) := by
  have hk32 : (k : Int) % 4294967296 = (k : Int) := Int.emod_eq_of_lt (by omega) (by omega)
  have c1 : (NExpr.cast u32 (.variable i32 1)).denote env = some (k : Int) := by
    rw [den_cast, den_variable, e, Option.bind_some, convert_u32, hk32]
  have c0 : (NExpr.literal u32 0).denote env = some 0 := by
    rw [den_literal, if_pos (show u32.valid 0 = true from rfl)]
  have c2 : (NExpr.binary u32 .sub (.literal u32 0) (.cast u32 (.variable i32 1))).denote env =
      some (4294967296 - (k : Int)) := by
    rw [den_binary, c0, c1]
    simp only [Option.bind_some, convert_u32]
    have : binaryValue .sub 0 (k : Int) = -(k : Int) := by show 0 - (k : Int) = _; omega
    rw [this]
    congr 1
    omega
  have hl := lowb_pos k h0
  have hl' := lowb_le k h0
  have c3 : (NExpr.binary u32 .band (.cast u32 (.variable i32 1))
      (.binary u32 .sub (.literal u32 0) (.cast u32 (.variable i32 1)))).denote env = some (lowb k : Int) := by
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

abbrev stepE : NExpr := .binary i32 .add (.variable i32 1) lowE
abbrev stepA : NStmt := .assign 1 i32 stepE
abbrev rdK1 : NExpr := .read s64 (.local 0) (.cast u64 (.variable i32 1))
abbrev valE : NExpr := .binary s64 .add rdK1 (.variable s64 2)
abbrev writeA : NStmt := .write (.local 0) s64 (.cast u64 (.variable i32 1)) valE
abbrev loopBodyA : Command := .sequence (.scope (.sequence (.primitive writeA) (.primitive .skip)))
  (.sequence (.primitive stepA) (.primitive .skip))
abbrev loopCA : Command := .whileLoop condE1 loopBodyA
abbrev bodyCmdA : Command := .sequence (.primitive assignI1)
  (.sequence (.scope (.sequence loopCA (.primitive .skip))) (.primitive .skip))

theorem body_eqA : Proofs.FenwickTreeInstance.FenwickTree_long_long_add.body = bodyCmdA := rfl

theorem vwp_stepE : vwp stepE = (10,10) := by decide
theorem vwp_valE : vwp valE = (7,7) := by decide
theorem vwp_idxK : vwp (NExpr.cast u64 (.variable i32 1)) = (2,2) := by decide

-- The callee state of `fenwick_add`: the index `i` and the value `val`.
def gA (P : List Cell) (i val : Int) : PS :=
  ⟨P ++ [⟨i32,i⟩,⟨s64,val⟩],[⟨P.length,true⟩,⟨P.length+1,true⟩]⟩

theorem gA_size (P : List Cell) (i val : Int) : (gA P i val).mem.length + (gA P i val).bs.length = P.length + 4 := by
  simp [gA]

theorem envA1 (P : List Cell) (i val : Int) (hi : i32.valid i = true) : penv1 (gA P i val) 1 i32 = some i := by
  show penv (gA P i val) 0 i32 = some i
  refine Proofs.PexecKit.penv_ok _ 0 i32 ⟨P.length,true⟩ ⟨i32,i⟩ rfl ?_ rfl hi
  show (P ++ [⟨i32,i⟩,⟨s64,val⟩])[P.length]? = _
  have := Proofs.ModIntExec.get_tail P [⟨i32,i⟩,⟨s64,val⟩] 0
  simpa using this

theorem envA2 (P : List Cell) (i val : Int) (hv : s64.valid val = true) : penv1 (gA P i val) 2 s64 = some val := by
  show penv (gA P i val) 1 s64 = some val
  refine Proofs.PexecKit.penv_ok _ 1 s64 ⟨P.length+1,true⟩ ⟨s64,val⟩ rfl ?_ rfl hv
  show (P ++ [⟨i32,i⟩,⟨s64,val⟩])[P.length+1]? = _
  have := Proofs.ModIntExec.get_tail P [⟨i32,i⟩,⟨s64,val⟩] 1
  simpa using this

theorem set_iA (P : List Cell) (i val i' : Int) :
    (⟨(gA P i val).mem.set P.length ⟨i32,i'⟩,(gA P i val).bs⟩ : PS) = gA P i' val := by
  simp [gA, List.set_append_right]

theorem condA_valL (vec : List Int) (P : List Cell) (i val : Int) (hn : vec.length < 2147483648) (hi : i32.valid i = true)
    (hi0 : 0 ≤ i) :
    vdenL s64 vec (penv1 (gA P i val)) condE1 = some (if i < (vec.length : Int) then 1 else 0) := by
  have e1 := envA1 P i val hi
  have hl : (NExpr.variable i32 1).scalarOnly = true := rfl
  have hc : condE1.scalarOnly = false := rfl
  have hr2 : (NExpr.cast i32 (.size (.integer s64) (.local 0))).scalarOnly = false := rfl
  have hn' : i32.convert (vec.length : Int) = some (vec.length : Int) :=
    conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega))
  have hr : (NExpr.size (.integer s64) (.local 0)).scalarOnly = false := rfl
  have hsz : vdenL s64 vec (penv1 (gA P i val)) (.size (.integer s64) (.local 0)) = some (vec.length : Int) := by
    simp [vdenL, hr]
  have hb : bT.convert (if i < (vec.length : Int) then 1 else 0) = some (if i < (vec.length : Int) then 1 else 0) := by
    simp only [bT]; unfold Ty.convert; by_cases hh : i < (vec.length : Int) <;> simp [hh]
  have step1 := vdenL_binary s64 vec (penv1 (gA P i val)) bT .lt (.variable i32 1) (.cast i32 (.size (.integer s64) (.local 0))) hc
  have step2 : vdenL s64 vec (penv1 (gA P i val)) (.cast i32 (.size (.integer s64) (.local 0))) = some (vec.length : Int) := by
    rw [vdenL_cast s64 vec _ _ _ hr2, hsz, Option.bind_some, hn']
  have step3 : vdenL s64 vec (penv1 (gA P i val)) (.variable i32 1) = some i := by
    rw [vdenL_scalar _ _ _ _ hl, den_variable]; exact e1
  rw [step1, step2, step3, Option.bind_some, Option.bind_some]
  have : binaryValue .lt i (vec.length : Int) = if i < (vec.length : Int) then 1 else 0 := rfl
  rw [this]; exact hb

theorem idxK_den (P : List Cell) (k : Nat) (val : Int) (hk : k < 2147483648) :
    (NExpr.cast u64 (.variable i32 1)).denote (penv1 (gA P k val)) = some (k : Int) := by
  have e1 := envA1 P k val (i32_valid k (by omega) (by omega))
  rw [den_cast]
  show ((penv1 (gA P k val)) 1 i32).bind u64.convert = _
  rw [e1, Option.bind_some, convert_u64]
  simp
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem valA_den (tree : List Int) (P : List Cell) (k : Nat) (val x : Int) (hk : k < 2147483648)
    (hx : tree[k]? = some x) (hxv : s64.valid x = true) (hval : s64.valid val = true)
    (hsum : s64.valid (x + val) = true) :
    vdenL s64 tree (penv1 (gA P k val)) valE = some (x + val) := by
  have hb : valE.scalarOnly = false := rfl
  have hrc : rdK1.scalarOnly = false := rfl
  have vcur : vdenL s64 tree (penv1 (gA P k val)) rdK1 = some x := by
    rw [vdenL_read _ _ _ _ _ hrc, if_pos ⟨rfl, rfl⟩, idxK_den P k val hk, Option.bind_some]
    simp [elemAtL, hx, hxv]
  have hv : vdenL s64 tree (penv1 (gA P k val)) (NExpr.variable s64 2) = some val := by
    rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact envA2 P k val hval
  rw [vdenL_binary _ _ _ _ _ _ _ hb, vcur, hv, Option.bind_some, Option.bind_some]
  have : binaryValue .add x val = x + val := rfl
  rw [this]
  exact conv_signed s64 rfl rfl _ hsum

theorem stepE_den (tree : List Int) (P : List Cell) (k : Nat) (val : Int) (h0 : 0 < k) (hk : k < 1073741824) :
    vdenL s64 tree (penv1 (gA P k val)) stepE = some ((k + lowb k : Nat) : Int) := by
  have e1 := envA1 P k val (i32_valid k (by omega) (by omega))
  have hl := lowb_pos k h0
  have hl' := lowb_le k h0
  have hs : stepE.scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, den_binary, den_variable, e1, Option.bind_some,
    lowE_den (penv1 (gA P k val)) k h0 (by omega) e1, Option.bind_some]
  have : binaryValue .add (k : Int) (lowb k : Int) = ((k + lowb k : Nat) : Int) := by
    show (k : Int) + (lowb k : Int) = _; push_cast; rfl
  rw [this]
  exact conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega))

theorem iterA (P : List Cell) (tree : List Int) (k : Nat) (val : Int) (h0 : 0 < k) (hk : k < tree.length)
    (hlen : tree.length ≤ 1073741824) (hv : ∀ x ∈ tree, s64.valid x = true) (hval : s64.valid val = true)
    (hsum : s64.valid (tree[k] + val) = true) (fu : Nat) :
    ∃ r1, pexecW s64 fu loopBodyA (gA P k val) tree = some r1 ∧ r1.ps = gA P ((k + lowb k : Nat) : Int) val ∧
      r1.vec = tree.set k (tree[k] + val) ∧ r1.ret = none ∧ r1.cost ≤ 24 ∧ r1.need ≤ P.length + 30 ∧ r1.wk = 1 := by
  have hxv := hv _ (List.getElem_mem hk)
  have hx : tree[k]? = some tree[k] := by simp [hk]
  have hval' := valA_den tree P k val tree[k] (by omega) hx hxv hval hsum
  have hp : vdenL s64 tree (penv1 (gA P k val)) (NExpr.cast u64 (.variable i32 1)) = some (k : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl]; exact idxK_den P k val (by omega)
  have w := pstmtW_write_ok s64 (gA P k val) tree (NExpr.cast u64 (.variable i32 1)) valE (tree[k] + val) k
    hval' hp hk hsum
  have a1 := (pexecW_prim s64 fu writeA _ _).trans w
  have a2 := seqW_some a1 rfl (pexecW_skip s64 fu (gA P k val) (tree.set k (tree[k] + val)))
  have a3 := pexecW_scope s64 fu _ _ _ _ a2
  have a4 := Proofs.PexecKit.scope_take (gA P k val) (gA P k val) rfl rfl
  simp only [a4] at a3
  have hstep := stepE_den (tree.set k (tree[k] + val)) P k val h0 (by omega)
  have bI : (gA P k val).bs[0]? = some ⟨P.length,true⟩ := by simp [gA]
  have cI : (gA P k val).mem[P.length]? = some ⟨i32,k⟩ := by
    have := Proofs.ModIntExec.get_tail P [⟨i32,k⟩,⟨s64,val⟩] 0
    simpa [gA] using this
  have hl := lowb_pos k h0
  have hl' := lowb_le k h0
  have stI' := pstmtW_assign_ok s64 (gA P k val) (tree.set k (tree[k] + val)) 0 i32 stepE ((k + lowb k : Nat) : Int) hstep
    ⟨P.length,true⟩ ⟨i32,k⟩ bI cI rfl (show i32.valid (k : Int) = true from i32_valid _ (by omega) (by omega)) rfl
    ((k + lowb k : Nat) : Int) (conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega)))
  rw [set_iA] at stI'
  have b1 := (pexecW_prim s64 fu stepA _ _).trans stI'
  have b2 := seqW_some b1 rfl (pexecW_skip s64 fu (gA P ((k + lowb k : Nat) : Int) val) (tree.set k (tree[k] + val)))
  have c1 := seqW_some a3 rfl b2
  refine ⟨_, c1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp_valE, vwp_idxK, vwp_stepE]
  · simp [vwp_valE, vwp_idxK, vwp_stepE, gA, NExpr.nodes, Container.nodes]
  · simp

theorem loop_runA (P : List Cell) (val : Int) (hval : s64.valid val = true) :
    ∀ (tree : List Int) (k : Nat), 0 < k → k < 2147483648 → tree.length ≤ 1073741824 →
      (∀ x ∈ tree, s64.valid x = true) → (∀ x ∈ fadd val tree k, s64.valid x = true) →
      ∀ fu, stepsA tree.length k + 1 ≤ fu →
      ∃ r, pexecW s64 fu loopCA (gA P k val) tree = some r ∧ r.vec = fadd val tree k ∧ r.ret = none ∧
        (∃ k' : Nat, r.ps = gA P k' val) ∧ r.cost ≤ 31 * stepsA tree.length k + 7 ∧ r.need ≤ P.length + 30 ∧
        r.wk = stepsA tree.length k := by
  intro tree k
  induction tree, k using fadd.induct val with
  | case1 tree k h ih =>
    intro hk0 hk1 hlen hv hfin fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    have hL := lowb_pos k hk0
    have hL' := lowb_le k hk0
    have hc := condA_valL tree P k val (by omega) (i32_valid k (by omega) (by omega)) (by omega)
    have ht : (k : Int) < (tree.length : Int) := by omega
    rw [if_pos ht] at hc
    have hfk : (fadd val tree k)[k]? = some (tree[k] + val) := by
      rw [fadd_spec val k tree k hk0 (by omega) (le_refl _) k]
      have : tree[k]? = some tree[k] := by simp [h.2]
      rw [this]; simp; omega
    have hsum : s64.valid (tree[k] + val) = true := hfin _ (List.mem_of_getElem? hfk)
    obtain ⟨r1, h1', p1, v1, ret1, c1, n1, w1⟩ := iterA P tree k val hk0 h.2 hlen hv hval hsum (fu'+1)
    have hsteps : stepsA tree.length k = 1 + stepsA tree.length (k + lowb k) := by
      rw [stepsA, dif_pos h]
    have hv' : ∀ x ∈ tree.set k (tree[k] + val), s64.valid x = true := by
      intro x hx
      rcases List.mem_or_eq_of_mem_set hx with hx | rfl
      · exact hv x hx
      · exact hsum
    have hfin' : ∀ x ∈ fadd val (tree.set k (tree[k] + val)) (k + lowb k), s64.valid x = true := by
      intro x hx
      apply hfin x
      rw [fadd, dif_pos h]; exact hx
    have hk1' : k + lowb k < 2147483648 := by omega
    have hlen' : (tree.set k (tree[k] + val)).length ≤ 1073741824 := by simpa using hlen
    have p1' : r1.ps = gA P ((k + lowb k : Nat) : Int) val := p1
    have hfeq : fadd val tree k = fadd val (tree.set k (tree[k] + val)) (k + lowb k) := by
      rw [fadd, dif_pos h]
    have hfuel : stepsA (tree.set k (tree[k] + val)).length (k + lowb k) + 1 ≤ fu' := by
      have : (tree.set k (tree[k] + val)).length = tree.length := by simp
      rw [this]; omega
    obtain ⟨r2, h2, v2, ret2, ⟨k', p2⟩, c2, n2, w2⟩ :=
      ih (by omega) hk1' hlen' hv' hfin' fu' hfuel
    have hlen2 : (tree.set k (tree[k] + val)).length = tree.length := by simp
    rw [hlen2] at c2 w2
    rw [pexecW_while, hc]
    simp only [Bind.bind, Option.bind, h1', ret1, p1', v1, h2, vwp_c1]
    refine ⟨⟨r2.ps, r2.vec, r2.ret, 6+1+r1.cost+r2.cost, max ((gA P k val).mem.length +
      (gA P k val).bs.length + 6 + 2) (max r1.need r2.need), r1.wk+r2.wk⟩, by simp, ?_, ?_, ⟨k', p2⟩, ?_, ?_, ?_⟩
    · show r2.vec = _
      rw [v2]; exact hfeq.symm
    · exact ret2
    · simp; omega
    · simp [gA_size, n1, n2]
    · simp [w1, w2]; omega
  | case2 tree k h =>
    intro hk0 hk1 hlen hv hfin fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    have hc := condA_valL tree P k val (by omega) (i32_valid k (by omega) (by omega)) (by omega)
    have hz : ¬ ((k : Int) < (tree.length : Int)) := by
      intro hh
      apply h
      exact ⟨hk0, by omega⟩
    rw [if_neg hz] at hc
    rw [pexecW_while, hc]
    simp only [Bind.bind, Option.bind, ite_true, vwp_c1]
    have hs : stepsA tree.length k = 0 := by rw [stepsA, dif_neg h]
    refine ⟨_, rfl, ?_, rfl, ⟨k, rfl⟩, ?_, ?_, ?_⟩
    · rw [fadd, dif_neg h]
    · simp [hs]
    · simp [gA]
    · simp [hs]

theorem incA_den (tree : List Int) (P : List Cell) (i : Nat) (val : Int) (hi : i < 2147483647) :
    vdenL s64 tree (penv1 (gA P i val)) incE1 = some ((i + 1 : Nat) : Int) := by
  have e1 := envA1 P i val (i32_valid i (by omega) (by omega))
  have hl : incE1.scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hl, den_binary, den_variable, e1, Option.bind_some, den_literal,
    if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  have : binaryValue .add (i : Int) 1 = ((i + 1 : Nat) : Int) := by
    show (i : Int) + 1 = _; push_cast; rfl
  rw [this]
  exact conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega))

theorem body_execA (P : List Cell) (tree : List Int) (i : Nat) (val : Int) (hi : i < 2147483647)
    (hlen : tree.length ≤ 1073741824) (hv : ∀ x ∈ tree, s64.valid x = true) (hval : s64.valid val = true)
    (hfin : ∀ x ∈ fadd val tree (i+1), s64.valid x = true) (fu : Nat) (hfu : stepsA tree.length (i+1) + 1 ≤ fu) :
    ∃ (r : PRW) (k' : Nat), pexecW s64 fu bodyCmdA (gA P i val) tree = some r ∧ r.ps = gA P k' val ∧
      r.vec = fadd val tree (i+1) ∧ r.ret = none ∧ r.cost ≤ 31 * stepsA tree.length (i+1) + 12 ∧
      r.need ≤ P.length + 30 ∧ r.wk = stepsA tree.length (i+1) := by
  have hinc := incA_den tree P i val hi
  have bI : (gA P i val).bs[0]? = some ⟨P.length,true⟩ := by simp [gA]
  have cI : (gA P i val).mem[P.length]? = some ⟨i32,i⟩ := by
    have := Proofs.ModIntExec.get_tail P [⟨i32,i⟩,⟨s64,val⟩] 0
    simpa [gA] using this
  have st := pstmtW_assign_ok s64 (gA P i val) tree 0 i32 incE1 ((i + 1 : Nat) : Int) hinc
    ⟨P.length,true⟩ ⟨i32,i⟩ bI cI rfl (show i32.valid (i : Int) = true from i32_valid _ (by omega) (by omega)) rfl
    ((i + 1 : Nat) : Int) (conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega)))
  rw [set_iA] at st
  have a1 := (pexecW_prim s64 fu assignI1 _ _).trans st
  obtain ⟨rL, hL, vL, retL, ⟨k', pL⟩, cL, nL, wL⟩ :=
    loop_runA P val hval tree (i+1) (by omega) (by omega) hlen hv hfin fu hfu
  have f2 := seqW_some hL retL (pexecW_skip s64 fu rL.ps rL.vec)
  have f3 := pexecW_scope s64 fu _ _ _ _ f2
  have take_eq : (⟨rL.ps.mem.take (gA P ((i + 1 : Nat) : Int) val).mem.length,
      rL.ps.bs.take (gA P ((i + 1 : Nat) : Int) val).bs.length⟩ : PS) = gA P k' val := by
    rw [pL]
    have hm : (gA P k' val).mem.take (gA P ((i + 1 : Nat) : Int) val).mem.length = (gA P k' val).mem :=
      List.take_of_length_le (by simp [gA])
    have hb : (gA P k' val).bs.take (gA P ((i + 1 : Nat) : Int) val).bs.length = (gA P k' val).bs :=
      List.take_of_length_le (by simp [gA])
    rw [hm, hb]
  have hsz : rL.ps.mem.length + rL.ps.bs.length = P.length + 4 := by rw [pL]; simp [gA]
  simp only [take_eq] at f3
  have f4 := seqW_some f3 rfl (pexecW_skip s64 fu (gA P k' val) rL.vec)
  have h5 := seqW_some a1 rfl f4
  refine ⟨_, k', h5, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · simp [vL]
  · simp [vwp_inc1]
    omega
  · simp [vwp_inc1, gA]
    omega
  · simp [wL]

theorem prepare_fa (caller : NState) {vslot vb V vsc : Nat} {vbuf : Buffer Value}
    (ok : VOKW caller vslot vb V vsc vbuf) (eI eV : NExpr) (vi vv : Int) (hsI : eI.scalarOnly = true)
    (hsV : eV.scalarOnly = true) (htI : eI.resultType = i32) (htV : eV.resultType = s64)
    (dI : eI.denote (envOf caller) = some vi) (dV : eV.denote (envOf caller) = some vv)
    (hvi : i32.valid vi = true) (hvv : s64.valid vv = true) :
    ∃ t1 t2, Good (caller.charge 1 1) t1 eI.nodes eI.nodes ∧ Good t1 t2 eV.nodes eV.nodes ∧
      ∃ Sinit, prepare caller Proofs.FenwickTreeInstance.FenwickTree_long_long_add.parameters
          [.vectorReference vslot,.value eI,.value eV] = some Sinit ∧
        Sinit.slots = [.vector 0,.scalar 0,.scalar 1] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨i32,vi⟩,⟨s64,vv⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer s64,true,.root vsc⟩]⟩ ∧
        Sinit.scalars.work = t2.scalars.work+4 ∧ t2.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc s64 true true vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (fun _ => rfl)
  have rvec : resolve caller (.vector s64 true) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc s64 true) := by
    simp [resolve,ok.slot,ok.binding,resolved]
  obtain ⟨t1,ran1,g1⟩ := scalar_eval eI (caller.charge 1 1) vi hsI
    (by rw [envOf_core (core_charge caller 1 1)]; exact dI)
  obtain ⟨t2,ran2,g2⟩ := scalar_eval eV t1 vv hsV
    (by rw [envOf_core g1.1, envOf_core (core_charge caller 1 1)]; exact dV)
  refine ⟨t1,t2,g1,g2,?_⟩
  have res1 : resolve (caller.charge 1 1) (.scalar i32 false true) (.value eI) = some (t1,.scalar i32 true vi) := by
    simp [resolve,htI,ran1]
  have res2 : resolve t1 (.scalar s64 false true) (.value eV) = some (t2,.scalar s64 true vv) := by
    simp [resolve,htV,ran2]
  have frameT : t2.frame = caller.frame := by rw [g2.1.1, g1.1.1]; rfl
  have fs : t2.frame.state = caller.frame.state := by rw [frameT]
  have fr : t2.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t2.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t2.scalars.memory = caller.scalars.memory := by
    have a := g2.1.2.2.2.1; have b := g1.1.2.2.2.1; rw [a, b]; rfl
  have hbind : t2.scalars.bindings = caller.scalars.bindings := by
    have a := g2.1.2.2.2.2.1; have b := g1.1.2.2.2.2.1; rw [a, b]; rfl
  have hbase : t2.scalars.baseMemory = caller.scalars.baseMemory := by
    have a := g2.1.2.2.2.2.2; have b := g1.1.2.2.2.2.2; rw [a, b]; rfl
  have bound : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).bindRoot V (.integer s64) vsc true =
      some (⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer s64,true,.root vsc⟩]⟩,0) := by
    have vobject : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).object V (.integer s64) =
        some (vbuf,⟨.integer s64,none,some vsc,[]⟩) :=
      object_runs _ V _ vbuf _ ok.valid ok.vfound ok.vtag rfl
    have vrooted : caller.frame.state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ ok.vtag rfl
    have vmax : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).maximum V = some true :=
      maximum_runs _ V V true ok.lengths vrooted ok.flag
    simp only [Frame.bindRoot,vobject,vmax,Bind.bind,Option.bind]
    simp [Frame.addBinding]
  have hp : Proofs.FenwickTreeInstance.FenwickTree_long_long_add.parameters = [.vector s64 true,.scalar i32 false true,.scalar s64 false true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec,res1,res2]
  simp [fs,fr,fb,hmem,hbind,hbase,bound,bindAll,bindOne,CppState.bindArgument,hvi,hvv,callerP,
    NState.observe,CppState.State.observe]
  left
  have ga := g1.2.2.2.2.1
  have gb := g2.2.2.2.2.1
  simp [NState.charge,NState.observe,CppState.State.observe] at ga
  omega

theorem stepsA_log (len k : Nat) : stepsA len k ≤ Nat.log2 len + 1 := by
  by_cases h : 0 < k ∧ k < len
  · have := stepsA_le len (len - k) k rfl h.1 h.2
    omega
  · rw [stepsA, dif_neg h]; omega

set_option maxHeartbeats 4000000 in
theorem fenwick_add_correct (caller : NState) {vslot vb V vsc : Nat} {vbuf : Buffer Value}
    (ok : VOKW caller vslot vb V vsc vbuf) (vec : List Int) (hitems : vbuf.items = vec.map Value.integer)
    (hbvalid : vbuf.Valid (accepts (.integer s64))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit s64)
    (howner : vbuf.owner = V) (hlen : vec.length ≤ 1073741824)
    (eI eV : NExpr) (i : Nat) (val : Int) (hsI : eI.scalarOnly = true) (hsV : eV.scalarOnly = true)
    (htI : eI.resultType = i32) (htV : eV.resultType = s64)
    (dI : eI.denote (envOf caller) = some (i : Int)) (dV : eV.denote (envOf caller) = some val)
    (hi : i < 2147483647) (hval : s64.valid val = true)
    (hv : ∀ x ∈ vec, s64.valid x = true) (hfin : ∀ x ∈ fadd val vec (i+1), s64.valid x = true) :
    ∃ Sinit fuel res, prepare caller Proofs.FenwickTreeInstance.FenwickTree_long_long_add.parameters
        [.vectorReference vslot,.value eI,.value eV] = some Sinit ∧
      Proofs.FenwickTreeInstance.FenwickTree_long_long_add.callFuel fuel caller [.vectorReference vslot,.value eI,.value eV] =
        .finished (res,Ret.unit) ∧
      ScalarPost3 caller Sinit res (eI.nodes+eV.nodes) (31*Nat.log2 vec.length+80) caller.scalars.memory
        (Nat.log2 vec.length + 1) V (fadd val vec (i+1)) := by
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_fa caller ok eI eV (i : Int) val hsI hsV htI htV dI dV (i32_valid i (by omega) (by omega)) hval
  let vc : VCtx := ⟨s64,true,true,V,vsc,vbuf,vec,hitems,fun _ => rfl,by omega,caller.frame.state.liveSpace,
    caller.frame.state.storage.work,caller.scope+1,caller.frame.state.storage.objects.length⟩
  have fwS : FW vc vec vbuf 0 Sinit.frame := by
    rw [sFrame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,hitems,hbvalid,hlimit,howner,by omega⟩
    intro owner k h
    have := ok.strict owner k h
    show k < caller.scope+1
    omega
  have hsteps := stepsA_log vec.length (i+1)
  have hfuel : stepsA vec.length (i+1) + 1 ≤ Nat.log2 vec.length + 2 := by omega
  obtain ⟨r,k',hexec,hrps,hrvec,hret,hcost,hneed,hwk⟩ :=
    body_execA (callerP caller) vec i val hi hlen hv hval hfin (Nat.log2 vec.length + 2) hfuel
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(i : Int)⟩ : Cell),(⟨s64,val⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := take_P caller _
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hpost := call_vecw_unit vc true (fun _ => ⟨rfl,rfl⟩) caller Proofs.FenwickTreeInstance.FenwickTree_long_long_add [.vectorReference vslot,.value eI,.value eV] Sinit
    (callerP caller ++ [(⟨i32,(i : Int)⟩ : Cell),(⟨s64,val⟩ : Cell)])
    [(⟨(callerP caller).length,true⟩ : CppState.Binding),(⟨(callerP caller).length+1,true⟩ : CppState.Binding)]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok.base (by decide) (Nat.log2 vec.length + 2) r
    (by rw [body_eqA]; exact hexec) hret rfl (by omega) (by simp) (eI.nodes+eV.nodes) (31*Nat.log2 vec.length+80) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gA]
    exact take_P caller _
  rw [hs', hrvec] at post
  exact post.relax (le_refl _) (by omega) (by omega)

-- `fenwick_sum`: the accumulator `s` lives in the cell after the counter `r`.
abbrev condS : NExpr := .binary bT .gt (.variable i32 1) (.literal i32 0)
abbrev accE : NExpr := .binary s64 .add (.variable s64 2) rdK1
abbrev assign2 : NStmt := .assign 2 s64 accE
abbrev subE : NExpr := .binary i32 .sub (.variable i32 1) lowE
abbrev stepS : NStmt := .assign 1 i32 subE
abbrev loopBodyS : Command := .sequence (.scope (.sequence (.primitive assign2) (.primitive .skip)))
  (.sequence (.primitive stepS) (.primitive .skip))
abbrev loopCS : Command := .whileLoop condS loopBodyS
abbrev declAcc : NStmt := .declare s64 true (.cast s64 (.literal i32 0))
abbrev bodyCmdS : Command := .sequence (.primitive declAcc)
  (.sequence (.scope (.sequence loopCS (.primitive .skip))) (.sequence (.primitive (.ret (.variable s64 2))) (.primitive .skip)))

theorem body_eqS : Proofs.FenwickTreeInstance.FenwickTree_long_long_sum_1.body = bodyCmdS := rfl

theorem vwp_condS : vwp condS = (3,3) := by decide
theorem vwp_accE : vwp accE = (7,7) := by decide
theorem vwp_subE : vwp subE = (10,10) := by decide
theorem vwp_var2 : vwp (NExpr.variable s64 2) = (1,1) := by decide
theorem vwp_zero : vwp (NExpr.cast s64 (.literal i32 0)) = (2,2) := by decide

theorem set_sA (P : List Cell) (i val val' : Int) :
    (⟨(gA P i val).mem.set (P.length+1) ⟨s64,val'⟩,(gA P i val).bs⟩ : PS) = gA P i val' := by
  simp [gA, List.set_append_right]

theorem condS_valV (vc : VCtx) (P : List Cell) (r : Nat) (acc : Int) (hr : r < 2147483648) (hacc : s64.valid acc = true) :
    vden vc (penv1 (gA P r acc)) condS = some (if 0 < r then 1 else 0) := by
  have e1 := envA1 P r acc (i32_valid r (by omega) (by omega))
  have hs : condS.scalarOnly = true := rfl
  rw [vden_scalar vc _ _ hs, den_binary, den_variable, e1, Option.bind_some, den_literal,
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

theorem accE_den (tree : List Int) (P : List Cell) (r : Nat) (acc x : Int) (hr : r < 2147483648)
    (hx : tree[r]? = some x) (hxv : s64.valid x = true) (hacc : s64.valid acc = true) (hsum : s64.valid (acc + x) = true) :
    vdenL s64 tree (penv1 (gA P r acc)) accE = some (acc + x) := by
  have hb : accE.scalarOnly = false := rfl
  have hrc : rdK1.scalarOnly = false := rfl
  have vcur : vdenL s64 tree (penv1 (gA P r acc)) rdK1 = some x := by
    rw [vdenL_read _ _ _ _ _ hrc, if_pos ⟨rfl, rfl⟩, idxK_den P r acc hr, Option.bind_some]
    simp [elemAtL, hx, hxv]
  have hv : vdenL s64 tree (penv1 (gA P r acc)) (NExpr.variable s64 2) = some acc := by
    rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact envA2 P r acc hacc
  rw [vdenL_binary _ _ _ _ _ _ _ hb, hv, vcur, Option.bind_some, Option.bind_some]
  have : binaryValue .add acc x = acc + x := rfl
  rw [this]
  exact conv_signed s64 rfl rfl _ hsum

theorem subE_den (tree : List Int) (P : List Cell) (r : Nat) (acc : Int) (h0 : 0 < r) (hr : r < 1073741824) :
    vdenL s64 tree (penv1 (gA P r acc)) subE = some ((r - lowb r : Nat) : Int) := by
  have e1 := envA1 P r acc (i32_valid r (by omega) (by omega))
  have hl := lowb_pos r h0
  have hl' := lowb_le r h0
  have hs : subE.scalarOnly = true := rfl
  rw [vdenL_scalar _ _ _ _ hs, den_binary, den_variable, e1, Option.bind_some,
    lowE_den (penv1 (gA P r acc)) r h0 (by omega) e1, Option.bind_some]
  have : binaryValue .sub (r : Int) (lowb r : Int) = ((r - lowb r : Nat) : Int) := by
    show (r : Int) - (lowb r : Int) = _; omega
  rw [this]
  exact conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega))

theorem iterS (P : List Cell) (tree : List Int) (r : Nat) (acc x : Int) (h0 : 0 < r) (hr : r < tree.length)
    (hlen : tree.length ≤ 1073741824) (hx : tree[r]? = some x) (hxv : s64.valid x = true)
    (hacc : s64.valid acc = true) (hsum : s64.valid (acc + x) = true) (fu : Nat) :
    ∃ r1, pexecW s64 fu loopBodyS (gA P r acc) tree = some r1 ∧ r1.ps = gA P ((r - lowb r : Nat) : Int) (acc + x) ∧
      r1.vec = tree ∧ r1.ret = none ∧ r1.cost ≤ 24 ∧ r1.need ≤ P.length + 30 ∧ r1.wk = 0 := by
  have hl := lowb_pos r h0
  have hl' := lowb_le r h0
  have hval := accE_den tree P r acc x (by omega) hx hxv hacc hsum
  have bA : (gA P r acc).bs[1]? = some ⟨P.length+1,true⟩ := by simp [gA]
  have cA : (gA P r acc).mem[P.length+1]? = some ⟨s64,acc⟩ := by
    have := Proofs.ModIntExec.get_tail P [⟨i32,r⟩,⟨s64,acc⟩] 1
    simpa [gA] using this
  have st1 := pstmtW_assign_ok s64 (gA P r acc) tree 1 s64 accE (acc + x) hval ⟨P.length+1,true⟩ ⟨s64,acc⟩ bA cA rfl hacc rfl
    (acc + x) (conv_signed s64 rfl rfl _ hsum)
  rw [set_sA] at st1
  have a1 := (pexecW_prim s64 fu assign2 _ _).trans st1
  have a2 := seqW_some a1 rfl (pexecW_skip s64 fu (gA P r (acc + x)) tree)
  have a3 := pexecW_scope s64 fu _ _ _ _ a2
  have a4 := Proofs.PexecKit.scope_take (gA P r acc) (gA P r (acc + x)) (by simp [gA]) (by simp [gA])
  simp only [a4] at a3
  have hstep := subE_den tree P r (acc + x) h0 (by omega)
  have bI : (gA P r (acc + x)).bs[0]? = some ⟨P.length,true⟩ := by simp [gA]
  have cI : (gA P r (acc + x)).mem[P.length]? = some ⟨i32,r⟩ := by
    have := Proofs.ModIntExec.get_tail P [⟨i32,r⟩,⟨s64,acc + x⟩] 0
    simpa [gA] using this
  have st2 := pstmtW_assign_ok s64 (gA P r (acc + x)) tree 0 i32 subE ((r - lowb r : Nat) : Int) hstep
    ⟨P.length,true⟩ ⟨i32,r⟩ bI cI rfl (show i32.valid (r : Int) = true from i32_valid _ (by omega) (by omega)) rfl
    ((r - lowb r : Nat) : Int) (conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega)))
  rw [set_iA] at st2
  have b1 := (pexecW_prim s64 fu stepS _ _).trans st2
  have b2 := seqW_some b1 rfl (pexecW_skip s64 fu (gA P ((r - lowb r : Nat) : Int) (acc + x)) tree)
  have c1 := seqW_some a3 rfl b2
  refine ⟨_, c1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp_accE, vwp_subE]
  · simp [vwp_accE, vwp_subE, gA, NExpr.nodes, Container.nodes]
  · simp

theorem condS_valL (vec : List Int) (P : List Cell) (r : Nat) (acc : Int) (hr : r < 2147483648) :
    vdenL s64 vec (penv1 (gA P r acc)) condS = some (if 0 < r then 1 else 0) := by
  have e1 := envA1 P r acc (i32_valid r (by omega) (by omega))
  have hs : condS.scalarOnly = true := rfl
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

-- The partial sums formed by the query loop starting from `acc` at node `r`.
def chainS (tree : List Int) : Nat → Int → List Int
  | 0, _ => []
  | r+1, acc => (acc + tree.getD (r+1) 0) :: chainS tree (r + 1 - lowb (r+1)) (acc + tree.getD (r+1) 0)
termination_by r => r
decreasing_by have := lowb_pos (r+1) (by omega); omega

theorem loop_runS (P : List Cell) (tree : List Int) (hlen : tree.length ≤ 1073741824)
    (hv : ∀ x ∈ tree, s64.valid x = true) :
    ∀ (r : Nat) (acc : Int), r < tree.length → s64.valid acc = true → (∀ x ∈ chainS tree r acc, s64.valid x = true) →
      ∀ fu, stepsS r + 1 ≤ fu →
      ∃ res, pexecW s64 fu loopCS (gA P r acc) tree = some res ∧ res.ps = gA P 0 (acc + fsumR tree r) ∧
        res.vec = tree ∧ res.ret = none ∧ res.cost ≤ 31 * stepsS r + 7 ∧ res.need ≤ P.length + 30 ∧ res.wk = 0 := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro acc hr hacc hch fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    have hc := condS_valL tree P r acc (by omega)
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
        iterS P tree (r0+1) acc x (by omega) hr hlen hx hxv hacc hsum (fu'+1)
      have hsteps : stepsS (r0+1) = 1 + stepsS (r0 + 1 - lowb (r0+1)) := by rw [stepsS]
      obtain ⟨r2, h2, p2, v2, ret2, c2, n2, w2⟩ :=
        ih (r0 + 1 - lowb (r0+1)) (by omega) (acc + x) (by omega) hsum hch' fu' (by omega)
      rw [pexecW_while, hc]
      simp only [Bind.bind, Option.bind, h1', ret1, p1, v1, h2, vwp_condS]
      refine ⟨⟨r2.ps, r2.vec, r2.ret, 3+1+r1.cost+r2.cost, max ((gA P ((r0+1 : Nat) : Int) acc).mem.length +
        (gA P ((r0+1 : Nat) : Int) acc).bs.length + 3 + 2) (max r1.need r2.need), r1.wk+r2.wk⟩, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · show r2.ps = _
        rw [p2, fsumR, hget, Int.add_assoc]
      · exact v2
      · exact ret2
      · simp; omega
      · simp [gA_size, n1, n2]
      · simp [w1, w2]
    · rw [if_neg h0] at hc
      have hr0 : r = 0 := by omega
      subst hr0
      rw [pexecW_while, hc]
      simp only [Bind.bind, Option.bind, ite_true, vwp_condS]
      refine ⟨_, rfl, ?_, rfl, rfl, ?_, ?_, rfl⟩
      · simp [fsumR]
      · simp [stepsS]
      · simp [gA]

theorem chain_last (tree : List Int) : ∀ (r : Nat) (acc : Int), r = 0 ∨ (acc + fsumR tree r) ∈ chainS tree r acc := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro acc
    cases r with
    | zero => exact Or.inl rfl
    | succ r0 =>
      right
      have hL := lowb_pos (r0+1) (by omega)
      rw [chainS, fsumR]
      rcases ih (r0 + 1 - lowb (r0+1)) (by omega) (acc + tree.getD (r0+1) 0) with h | h
      · rw [h]
        simp [fsumR, chainS]
      · have := List.mem_cons_of_mem (acc + tree.getD (r0+1) 0) h
        rw [← Int.add_assoc]
        exact this

theorem body_execS (P : List Cell) (tree : List Int) (r : Nat) (hr : r < tree.length)
    (hlen : tree.length ≤ 1073741824) (hv : ∀ x ∈ tree, s64.valid x = true)
    (hch : ∀ x ∈ chainS tree r 0, s64.valid x = true) (fu : Nat) (hfu : stepsS r + 1 ≤ fu) :
    ∃ res, pexecW s64 fu bodyCmdS (stI P r) tree = some res ∧ res.ret = some (fsumR tree r) ∧
      res.ps = gA P 0 (fsumR tree r) ∧ res.vec = tree ∧ res.cost ≤ 31 * stepsS r + 25 ∧ res.need ≤ P.length + 30 ∧ res.wk = 0 := by
  have hres : s64.valid (fsumR tree r) = true := by
    rcases chain_last tree r 0 with h | h
    · subst h; simp [fsumR]; rfl
    · exact hch _ (by simpa using h)
  have hv0 : vdenL s64 tree (penv1 (stI P r)) (NExpr.cast s64 (.literal i32 0)) = some 0 := by
    rw [vdenL_scalar _ _ _ _ rfl, den_cast]
    show ((NExpr.literal i32 0).denote (penv1 (stI P r))).bind s64.convert = _
    rw [den_literal, if_pos (show i32.valid 0 = true from rfl), Option.bind_some]
    exact conv_signed s64 rfl rfl _ rfl
  have d := pstmtW_declare_ok s64 (stI P r) tree s64 true (NExpr.cast s64 (.literal i32 0)) 0 hv0 0
    (conv_signed s64 rfl rfl _ rfl)
  have st0 : (⟨(stI P r).mem ++ [(⟨s64,0⟩ : Cell)],(stI P r).bs ++ [⟨(stI P r).mem.length,true⟩]⟩ : PS) = gA P r 0 := by
    simp [stI, gA]
  rw [st0] at d
  have d' := (pexecW_prim s64 fu declAcc _ _).trans d
  obtain ⟨rL, hL, pL, vL, retL, cL, nL, wL⟩ :=
    loop_runS P tree hlen hv r 0 hr (by rfl) hch fu hfu
  have f2 := seqW_some hL retL (pexecW_skip s64 fu rL.ps rL.vec)
  have f3 := pexecW_scope s64 fu _ _ _ _ f2
  have take_eq : (⟨rL.ps.mem.take (gA P r 0).mem.length, rL.ps.bs.take (gA P r 0).bs.length⟩ : PS) =
      gA P 0 (0 + fsumR tree r) := by
    rw [pL]
    have hm : (gA P 0 (0 + fsumR tree r)).mem.take (gA P r 0).mem.length = (gA P 0 (0 + fsumR tree r)).mem :=
      List.take_of_length_le (by simp [gA])
    have hb : (gA P 0 (0 + fsumR tree r)).bs.take (gA P r 0).bs.length = (gA P 0 (0 + fsumR tree r)).bs :=
      List.take_of_length_le (by simp [gA])
    rw [hm, hb]
  simp only [take_eq] at f3
  have hret : vdenL s64 rL.vec (penv1 (gA P 0 (0 + fsumR tree r))) (NExpr.variable s64 2) = some (fsumR tree r) := by
    rw [vdenL_scalar _ _ _ _ rfl, den_variable]
    have := envA2 P 0 (fsumR tree r) hres
    simpa using this
  have g1 := pstmtW_ret_ok s64 (gA P 0 (0 + fsumR tree r)) rL.vec (NExpr.variable s64 2) (fsumR tree r) hret
  have g2 := (pexecW_prim s64 fu (.ret (.variable s64 2)) _ _).trans g1
  have g3 := seqW_ret (b := .primitive .skip) g2 rfl
  have h4 := seqW_some f3 rfl g3
  have h5 := seqW_some d' rfl h4
  have hsz : rL.ps.mem.length + rL.ps.bs.length = P.length + 4 := by rw [pL]; simp [gA]
  refine ⟨_, h5, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp [vL]
  · simp [vwp_zero, vwp_var2]
    omega
  · simp [vwp_zero, vwp_var2, stI, gA]
    omega
  · simp [wL]

theorem prepare_fs (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : Proofs.VectorSumCall.VOK caller vslot vb V vsc m vbuf) (e : NExpr) (v : Int) (hs : e.scalarOnly = true)
    (hty : e.resultType = i32) (value : e.denote (envOf caller) = some v) (hv : i32.valid v = true) :
    ∃ t, Good (caller.charge 1 1) t e.nodes e.nodes ∧
      ∃ Sinit, prepare caller Proofs.FenwickTreeInstance.FenwickTree_long_long_sum_1.parameters [.vectorReference vslot,.value e] = some Sinit ∧
        Sinit.slots = [.vector 0,.scalar 0] ∧ Sinit.scalars.memory = callerP caller ++ [⟨i32,v⟩] ∧
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
  have res : resolve (caller.charge 1 1) (.scalar i32 false true) (.value e) = some (t,.scalar i32 true v) := by
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
  have hp : Proofs.FenwickTreeInstance.FenwickTree_long_long_sum_1.parameters = [.vector s64 false,.scalar i32 false true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec,res]
  simp [fs,fr,fb,hmem,hbind,hbase,bound,bindAll,bindOne,CppState.bindArgument,hv,callerP,
    NState.observe,CppState.State.observe]
  left
  have g := good.2.2.2.2.1
  simp [NState.charge,NState.observe,CppState.State.observe] at g
  omega

theorem stepsS_log (len r : Nat) (hr : r < len) : stepsS r ≤ Nat.log2 len + 1 := by
  by_cases h : 0 < r
  · have := stepsS_le r h
    have hm : Nat.log2 r ≤ Nat.log2 len := log2_mono _ _ h (by omega)
    omega
  · have : r = 0 := by omega
    subst this
    simp [stepsS]

set_option maxHeartbeats 4000000 in
theorem fenwick_sum_correct (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : Proofs.VectorSumCall.VOK caller vslot vb V vsc m vbuf) (vec : List Int)
    (hitems : vbuf.items = vec.map Value.integer) (hlen : vec.length ≤ 1073741824)
    (hbvalid : vbuf.Valid (accepts (.integer s64))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit s64)
    (howner : vbuf.owner = V)
    (e : NExpr) (r : Nat) (hs : e.scalarOnly = true) (ht : e.resultType = i32)
    (value : e.denote (envOf caller) = some (r : Int)) (hr : r < vec.length)
    (hv : ∀ x ∈ vec, s64.valid x = true) (hch : ∀ x ∈ chainS vec r 0, s64.valid x = true) :
    ∃ Sinit fuel res, prepare caller Proofs.FenwickTreeInstance.FenwickTree_long_long_sum_1.parameters
        [.vectorReference vslot,.value e] = some Sinit ∧
      Proofs.FenwickTreeInstance.FenwickTree_long_long_sum_1.callFuel fuel caller [.vectorReference vslot,.value e] =
        .finished (res,.scalar (fsumR vec r)) ∧
      ScalarPost3 caller Sinit res e.nodes (31*Nat.log2 vec.length+80) caller.scalars.memory 0 V vec := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_fs caller ok e (r : Int) hs ht value (i32_valid r (by omega) (by omega))
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
  have hsteps := stepsS_log vec.length r hr
  obtain ⟨rr,hexec,hret,hrps,hrvec,hcost,hneed,hwk⟩ :=
    body_execS (callerP caller) vec r hr hlen hv hch (Nat.log2 vec.length + 2) (by omega)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(r : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := take_P caller _
  have gw1 := good.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hres : s64.valid (fsumR vec r) = true := by
    rcases chain_last vec r 0 with h | h
    · subst h; simp [fsumR]; rfl
    · exact hch _ (by simpa using h)
  have hpost := call_vecw vc false (fun h => absurd h (by decide)) caller Proofs.FenwickTreeInstance.FenwickTree_long_long_sum_1
    [.vectorReference vslot,.value e] Sinit
    (callerP caller ++ [(⟨i32,(r : Int)⟩ : Cell)]) [(⟨(callerP caller).length,true⟩ : CppState.Binding)]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok.base (by decide) (Nat.log2 vec.length + 2) rr
    (by rw [body_eqS]; exact hexec) (fsumR vec r) hret s64 rfl hres (by omega) (by simp) e.nodes
    (31*Nat.log2 vec.length+80) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gA]
    exact take_P caller _
  rw [hs', hrvec, hwk] at post
  exact post

theorem pexecW_branch_trueB (ty0 : Ty) (fu : Nat) (c : NExpr) (y n : Command) (ps : PS) (vec : List Int) (v : Int)
    (hv : vdenL ty0 vec (penv1 ps) c = some v) (hne : v ≠ 0) (r : PRW) (hr : pexecW ty0 fu y ps vec = some r) :
    pexecW ty0 fu (.branch c y n) ps vec =
      some ⟨r.ps,r.vec,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need,r.wk⟩ := by
  rw [pexecW]
  simp [hv, hne, hr]

theorem pexecW_branch_falseB (ty0 : Ty) (fu : Nat) (c : NExpr) (y n : Command) (ps : PS) (vec : List Int)
    (hv : vdenL ty0 vec (penv1 ps) c = some 0) (r : PRW) (hr : pexecW ty0 fu n ps vec = some r) :
    pexecW ty0 fu (.branch c y n) ps vec =
      some ⟨r.ps,r.vec,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need,r.wk⟩ := by
  rw [pexecW]
  simp [hv, hr]

end Proofs.FenwickCall
