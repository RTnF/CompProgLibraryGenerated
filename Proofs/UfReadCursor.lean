import Proofs.UfRootCall

namespace Proofs.UfReadCursor
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

open Proofs.UfRootCall

def cursor (P : List Cell) (bindings : List Proofs.CppState.Binding) (a : Int) : PS :=
  ⟨P++[⟨i32,a⟩],bindings++[⟨P.length,true⟩]⟩
abbrev readCursor (bindings : List Proofs.CppState.Binding) : NExpr :=
  .read i32 (.local 0) (.cast u64 (.variable i32 (bindings.length+1)))
abbrev condition (bindings : List Proofs.CppState.Binding) : NExpr :=
  .binary bT .ge (readCursor bindings) (.literal i32 0)
abbrev assignCursor (bindings : List Proofs.CppState.Binding) : NStmt :=
  .assign (bindings.length+1) i32 (readCursor bindings)
abbrev iteration (bindings : List Proofs.CppState.Binding) : Command :=
  .sequence (.scope (.sequence (.primitive (assignCursor bindings)) (.primitive .skip))) (.primitive .skip)
abbrev loop (bindings : List Proofs.CppState.Binding) : Command := .whileLoop (condition bindings) (iteration bindings)
abbrev body (bindings : List Proofs.CppState.Binding) : Command :=
  .sequence (loop bindings) (.sequence (.primitive (.ret (.variable i32 (bindings.length+1)))) (.primitive .skip))

theorem cursor_size (P : List Cell) (bindings : List Proofs.CppState.Binding) (a : Int) :
    (cursor P bindings a).mem.length+(cursor P bindings a).bs.length = P.length+bindings.length+2 := by
  simp [cursor]; omega

theorem env_cursor (P : List Cell) (bindings : List Proofs.CppState.Binding) (a : Int) (valid : i32.valid a = true) :
    penv1 (cursor P bindings a) (bindings.length+1) i32 = some a := by
  show penv (cursor P bindings a) bindings.length i32 = some a
  apply Proofs.PexecKit.penv_ok _ _ i32 ⟨P.length,true⟩ ⟨i32,a⟩
  · simp [cursor]
  · simp [cursor]
  · rfl
  · exact valid

theorem idx_cursor (_vec : List Int) (P : List Cell) (bindings : List Proofs.CppState.Binding)
    (i : Nat) (inside : i < 2147483648) :
    (NExpr.cast u64 (.variable i32 (bindings.length+1))).denote (penv1 (cursor P bindings i)) = some (i : Int) := by
  have env := env_cursor P bindings i (i32_valid i (by omega) (by omega))
  rw [den_cast]
  show ((penv1 (cursor P bindings i)) (bindings.length+1) i32).bind u64.convert = _
  rw [env,Option.bind_some,convert_u64]
  simp
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem set_cursor (P : List Cell) (bindings : List Proofs.CppState.Binding) (a b : Int) :
    (⟨(cursor P bindings a).mem.set P.length ⟨i32,b⟩,(cursor P bindings a).bs⟩ : PS) = cursor P bindings b := by
  simp [cursor,List.set_append_right]

theorem vwp_readCursor (bindings : List Proofs.CppState.Binding) : vwp (readCursor bindings) = (5,5) := rfl
theorem vwp_varCursor (bindings : List Proofs.CppState.Binding) : vwp (.variable i32 (bindings.length+1)) = (1,1) := rfl
theorem vwp_condition (bindings : List Proofs.CppState.Binding) : vwp (condition bindings) = (7,7) := rfl

theorem condition_value (ps : List Int) (P : List Cell) (bindings : List Proofs.CppState.Binding) (a : Nat) (x : Int) (hn : ps.length < 2147483648)
    (ha : a < ps.length) (hx : ps[a]? = some x) (hxv : i32.valid x = true) :
    vdenL i32 ps (penv1 (cursor P bindings a)) (condition bindings) = some (if 0 ≤ x then 1 else 0) := by
  have hb : (condition bindings).scalarOnly = false := rfl
  have hrd : (readCursor bindings).scalarOnly = false := rfl
  have vcur : vdenL i32 ps (penv1 (cursor P bindings a)) (readCursor bindings) = some x := by
    rw [vdenL_read _ _ _ _ _ hrd, ite_eq_left ⟨rfl, rfl⟩, idx_cursor ps P bindings a (by omega), Option.bind_some]
    simp [elemAtL, hx, hxv]
  have hl : vdenL i32 ps (penv1 (cursor P bindings a)) (NExpr.literal i32 0) = some 0 := by
    rw [vdenL_scalar _ _ _ _ rfl, den_literal, ite_eq_left (show i32.valid 0 = true from rfl)]
  rw [vdenL_binary _ _ _ _ _ _ _ hb, vcur, hl, Option.bind_some, Option.bind_some]
  have : binaryValue .ge x 0 = if 0 ≤ x then 1 else 0 := by
    show (if x ≥ 0 then 1 else 0) = _
    by_cases h : 0 ≤ x <;> simp [h]
  rw [this]
  simp only [bT]; unfold Ty.convert
  by_cases h : 0 ≤ x <;> simp [h]

theorem read_value (ps : List Int) (P : List Cell) (bindings : List Proofs.CppState.Binding) (a : Nat) (x : Int) (hn : ps.length < 2147483648)
    (ha : a < ps.length) (hx : ps[a]? = some x) (hxv : i32.valid x = true) :
    vdenL i32 ps (penv1 (cursor P bindings a)) (readCursor bindings) = some x := by
  have hrd : (readCursor bindings).scalarOnly = false := rfl
  rw [vdenL_read _ _ _ _ _ hrd, ite_eq_left ⟨rfl, rfl⟩, idx_cursor ps P bindings a (by omega), Option.bind_some]
  simp [elemAtL, hx, hxv]

theorem iteration_run (P : List Cell) (bindings : List Proofs.CppState.Binding) (ps : List Int) (a : Nat) (x : Int) (hn : ps.length < 2147483648) (ha : a < ps.length)
    (hx : ps[a]? = some x) (hxv : i32.valid x = true) (_hx0 : 0 ≤ x) (_hxl : x < ps.length) (fu : Nat) :
    ∃ r1, pexecW i32 fu (iteration bindings) (cursor P bindings a) ps = some r1 ∧ r1.ps = cursor P bindings x ∧ r1.vec = ps ∧ r1.ret = none ∧
      r1.cost ≤ 8 ∧ r1.need ≤ P.length + bindings.length + 20 ∧ r1.wk = 0 := by
  have hval := read_value ps P bindings a x hn ha hx hxv
  have bI : (cursor P bindings a).bs[bindings.length]? = some ⟨P.length,true⟩ := by simp [cursor]
  have cI : (cursor P bindings a).mem[P.length]? = some ⟨i32,a⟩ := by
    simp [cursor]
  have st := pstmtW_assign_ok i32 (cursor P bindings a) ps bindings.length i32 (readCursor bindings) x hval ⟨P.length,true⟩ ⟨i32,a⟩ bI cI rfl
    (show i32.valid (a : Int) = true from i32_valid _ (by omega) (by omega)) rfl x (conv_signed i32 rfl rfl _ hxv)
  rw [set_cursor] at st
  have a1 := (pexecW_prim i32 fu (assignCursor bindings) _ _).trans st
  have a2 := seqW_some a1 rfl (pexecW_skip i32 fu (cursor P bindings x) ps)
  have a3 := pexecW_scope i32 fu _ _ _ _ a2
  have a4 := Proofs.PexecKit.scope_take (cursor P bindings a) (cursor P bindings x) (by simp [cursor]) (by simp [cursor])
  simp only [a4] at a3
  have a5 := seqW_some a3 rfl (pexecW_skip i32 fu (cursor P bindings x) ps)
  refine ⟨_, a5, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simp [vwp_readCursor]
  · simp [vwp_readCursor, cursor]; omega

theorem loop_run (P : List Cell) (bindings : List Proofs.CppState.Binding) (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank)
    (hn : ps.length < 2147483648) :
    ∀ (m a : Nat), a < ps.length → rank a ≤ m → ∀ fu, m + 2 ≤ fu →
      ∃ (res : PRW) (r : Nat), pexecW i32 fu (loop bindings) (cursor P bindings a) ps = some res ∧ res.ps = cursor P bindings r ∧ res.vec = ps ∧
        res.ret = none ∧ Reach ps a r ∧ r < ps.length ∧ (∃ v, ps[r]? = some v ∧ v < 0) ∧
        res.cost ≤ 16 * m + 8 ∧ res.need ≤ P.length + bindings.length + 20 ∧ res.wk = 0 := by
  intro m
  induction m with
  | zero =>
    intro a ha hr fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    obtain ⟨x, hx⟩ : ∃ x, ps[a]? = some x := ⟨ps[a], by simp [ha]⟩
    have hxv := hF.valid x (List.mem_of_getElem? hx)
    have hneg : x < 0 := by
      by_contra h
      have := hF.decrease a x hx (by omega)
      omega
    have hc := condition_value ps P bindings a x hn ha hx hxv
    rw [ite_eq_right (by omega)] at hc
    rw [pexecW_while, hc]
    simp only [Bind.bind, Option.bind, ite_true, vwp_condition]
    refine ⟨_, a, rfl, rfl, rfl, rfl, Reach.refl a, ha, ⟨x, hx, hneg⟩, ?_, ?_, rfl⟩
    · simp
    · simp [cursor]; omega
  | succ m ih =>
    intro a ha hr fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    obtain ⟨x, hx⟩ : ∃ x, ps[a]? = some x := ⟨ps[a], by simp [ha]⟩
    have hxv := hF.valid x (List.mem_of_getElem? hx)
    have hc := condition_value ps P bindings a x hn ha hx hxv
    by_cases hx0 : 0 ≤ x
    · rw [ite_eq_left hx0] at hc
      have hxl := hF.inside a x hx hx0
      have hdec := hF.decrease a x hx hx0
      obtain ⟨r1, h1, p1, v1, ret1, c1, n1, w1⟩ := iteration_run P bindings ps a x hn ha hx hxv hx0 hxl (fu'+1)
      obtain ⟨r2, r, h2, p2, v2, ret2, hreach, hrl, hroot, c2, n2, w2⟩ :=
        ih x.toNat (by omega) (by omega) fu' (by omega)
      have hxn : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg hx0
      have p1' : r1.ps = cursor P bindings ((x.toNat : Nat) : Int) := by rw [p1, hxn]
      rw [pexecW_while, hc]
      simp only [Bind.bind, Option.bind, h1, ret1, p1', v1, h2, vwp_condition]
      refine ⟨⟨r2.ps, r2.vec, r2.ret, 7+1+r1.cost+r2.cost, max ((cursor P bindings a).mem.length +
        (cursor P bindings a).bs.length + 7 + 2) (max r1.need r2.need), r1.wk+r2.wk⟩, r, by simp, p2, v2, ret2,
        Reach.step a x.toNat r (by simp [Parent, hxn, hx]) hreach, hrl, hroot, ?_, ?_, ?_⟩
      · simp; omega
      · simp [cursor_size, n1, n2]
      · simp [w1, w2]
    · rw [ite_eq_right hx0] at hc
      rw [pexecW_while, hc]
      simp only [Bind.bind, Option.bind, ite_true, vwp_condition]
      refine ⟨_, a, rfl, rfl, rfl, rfl, Reach.refl a, ha, ⟨x, hx, by omega⟩, ?_, ?_, rfl⟩
      · simp
      · simp [cursor]; omega

theorem body_run (P : List Cell) (bindings : List Proofs.CppState.Binding) (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank)
    (hn : ps.length < 2147483648) (a : Nat) (ha : a < ps.length) (fu : Nat) (hfu : rank a + 2 ≤ fu) :
    ∃ (res : PRW) (r : Nat), pexecW i32 fu (body bindings) (cursor P bindings a) ps = some res ∧ res.ret = some (r : Int) ∧
      res.ps = cursor P bindings r ∧ res.vec = ps ∧ Reach ps a r ∧ r < ps.length ∧ (∃ v, ps[r]? = some v ∧ v < 0) ∧
      res.cost ≤ 16 * rank a + 18 ∧ res.need ≤ P.length + bindings.length + 20 ∧ res.wk = 0 := by
  obtain ⟨rL, r, hL, pL, vL, retL, hreach, hrl, hroot, cL, nL, wL⟩ :=
    loop_run P bindings ps rank hF hn (rank a) a ha (le_refl _) fu hfu
  have hret : vdenL i32 rL.vec (penv1 (cursor P bindings r)) (NExpr.variable i32 (bindings.length+1)) = some (r : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl, den_variable]
    exact env_cursor P bindings r (i32_valid r (by omega) (by omega))
  have g1 := pstmtW_ret_ok i32 (cursor P bindings r) rL.vec (NExpr.variable i32 (bindings.length+1)) (r : Int) hret
  have g2 := (pexecW_prim i32 fu (.ret (.variable i32 (bindings.length+1))) _ _).trans g1
  have g3 := seqW_ret (b := .primitive .skip) g2 rfl
  rw [← pL] at g3
  have h4 := seqW_some hL retL g3
  have hsz : rL.ps.mem.length + rL.ps.bs.length = P.length + bindings.length + 2 := by rw [pL]; exact cursor_size P bindings r
  refine ⟨_, r, h4, rfl, ?_, ?_, hreach, hrl, hroot, ?_, ?_, ?_⟩
  · simp [pL]
  · simp [vL]
  · simp [vwp_varCursor]
    omega
  · simp [vwp_varCursor]
    omega
  · simp [wL]


end Proofs.UfReadCursor
