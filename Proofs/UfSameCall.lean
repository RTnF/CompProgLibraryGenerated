import Proofs.UfRootCall
import Proofs.Generated.UnionFind

namespace Proofs.UfSameCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.VecStraight Proofs.VecCall Proofs.VecKit
open Proofs.CppNestedFacts Proofs.IntSim Proofs.ScalarCall Proofs.VecWrite Proofs.VecWriteCall Proofs.VecKitW
open Proofs.QuotientSearch Proofs.VectorFillCall Proofs.PrefixSumsCall Proofs.UfRootCall
open Proofs.VectorSumCall (conv_signed i32_valid)
open Proofs.CppState (Cell)
open Proofs.PowModStep (Sk)

-- The union-find root loop on the scalar local with binding index `j` (variable index `j+1`), in any state.
abbrev rdK (j : Nat) : NExpr := .read i32 (.local 0) (.cast u64 (.variable i32 (j+1)))
abbrev condK (j : Nat) : NExpr := .binary bT .ge (rdK j) (.literal i32 0)
abbrev assignK (j : Nat) : NStmt := .assign (j+1) i32 (rdK j)
abbrev loopBodyK (j : Nat) : Command := .sequence (.scope (.sequence (.primitive (assignK j)) (.primitive .skip))) (.primitive .skip)
abbrev loopCK (j : Nat) : Command := .whileLoop (condK j) (loopBodyK j)

theorem vwp_rdK (j : Nat) : vwp (rdK j) = (5,5) := by simp [vwp, NExpr.scalarOnly, NExpr.nodes, Container.nodes]
theorem vwp_condK (j : Nat) : vwp (condK j) = (7,7) := by simp [vwp, NExpr.scalarOnly, NExpr.nodes, Container.nodes]

-- Binding `j` is a writable cell at `ad` holding the `int` value `a`.
def Loc (ps0 : PS) (j ad : Nat) (a : Int) : Prop :=
  ps0.bs[j]? = some ⟨ad,true⟩ ∧ ps0.mem[ad]? = some ⟨i32,a⟩

def setP (ps0 : PS) (ad : Nat) (x : Int) : PS := ⟨ps0.mem.set ad ⟨i32,x⟩,ps0.bs⟩

theorem setP_size (ps0 : PS) (ad : Nat) (x : Int) :
    (setP ps0 ad x).mem.length + (setP ps0 ad x).bs.length = ps0.mem.length + ps0.bs.length := by
  simp [setP]

theorem loc_set (ps0 : PS) (j ad : Nat) (a x : Int) (h : Loc ps0 j ad a) : Loc (setP ps0 ad x) j ad x := by
  obtain ⟨hb,hm⟩ := h
  refine ⟨hb,?_⟩
  have : ad < ps0.mem.length := (List.getElem?_eq_some_iff.mp hm).1
  simp [setP, List.getElem?_set_self this]

theorem env_loc (ps0 : PS) (j ad : Nat) (a : Int) (h : Loc ps0 j ad a) (hv : i32.valid a = true) :
    penv1 ps0 (j+1) i32 = some a := by
  obtain ⟨hb,hm⟩ := h
  show penv ps0 j i32 = some a
  simp [penv, hb, hm, hv]

theorem idxK (ps0 : PS) (j ad a : Nat) (h : Loc ps0 j ad a) (hn : a < 2147483648) :
    (NExpr.cast u64 (.variable i32 (j+1))).denote (penv1 ps0) = some (a : Int) := by
  have e1 := env_loc ps0 j ad a h (i32_valid a (by omega) (by omega))
  rw [den_cast]
  show ((penv1 ps0) (j+1) i32).bind u64.convert = _
  rw [e1, Option.bind_some, convert_u64]
  simp
  exact Int.emod_eq_of_lt (by omega) (by omega)

theorem rdK_val (ps : List Int) (ps0 : PS) (j ad a : Nat) (h : Loc ps0 j ad a) (hn : ps.length < 2147483648)
    (ha : a < ps.length) (x : Int) (hx : ps[a]? = some x) (hxv : i32.valid x = true) :
    vdenL i32 ps (penv1 ps0) (rdK j) = some x := by
  have hrd : (rdK j).scalarOnly = false := rfl
  rw [vdenL_read _ _ _ _ _ hrd, if_pos ⟨rfl, rfl⟩, idxK ps0 j ad a h (by omega), Option.bind_some]
  simp [elemAtL, hx, hxv]

theorem cond_valK (ps : List Int) (ps0 : PS) (j ad a : Nat) (h : Loc ps0 j ad a) (hn : ps.length < 2147483648)
    (ha : a < ps.length) (x : Int) (hx : ps[a]? = some x) (hxv : i32.valid x = true) :
    vdenL i32 ps (penv1 ps0) (condK j) = some (if 0 ≤ x then 1 else 0) := by
  have hb : (condK j).scalarOnly = false := rfl
  have vcur := rdK_val ps ps0 j ad a h hn ha x hx hxv
  have hl : vdenL i32 ps (penv1 ps0) (NExpr.literal i32 0) = some 0 := by
    rw [vdenL_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 0 = true from rfl)]
  rw [vdenL_binary _ _ _ _ _ _ _ hb, vcur, hl, Option.bind_some, Option.bind_some]
  have : binaryValue .ge x 0 = if 0 ≤ x then 1 else 0 := by
    show (if x ≥ 0 then 1 else 0) = _
    by_cases h : 0 ≤ x <;> simp [h]
  rw [this]
  simp only [bT]; unfold Ty.convert
  by_cases h : 0 ≤ x <;> simp [h]

theorem iterK (ps : List Int) (ps0 : PS) (j ad a : Nat) (h : Loc ps0 j ad a) (hn : ps.length < 2147483648)
    (ha : a < ps.length) (x : Int) (hx : ps[a]? = some x) (hxv : i32.valid x = true) (hx0 : 0 ≤ x)
    (fu : Nat) :
    ∃ r1, pexecW i32 fu (loopBodyK j) ps0 ps = some r1 ∧ r1.ps = setP ps0 ad x ∧ r1.vec = ps ∧ r1.ret = none ∧
      r1.cost ≤ 8 ∧ r1.need ≤ ps0.mem.length + ps0.bs.length + 16 ∧ r1.wk = 0 := by
  have hval := rdK_val ps ps0 j ad a h hn ha x hx hxv
  obtain ⟨hb,hm⟩ := h
  have st := pstmtW_assign_ok i32 ps0 ps j i32 (rdK j) x hval ⟨ad,true⟩ ⟨i32,a⟩ hb hm rfl
    (show i32.valid (a : Int) = true from i32_valid _ (by omega) (by omega)) rfl x (conv_signed i32 rfl rfl _ hxv)
  have a1 := (pexecW_prim i32 fu (assignK j) _ _).trans st
  have a2 := seqW_some a1 rfl (pexecW_skip i32 fu (setP ps0 ad x) ps)
  have a3 := pexecW_scope i32 fu _ _ _ _ a2
  have a4 := Proofs.PexecKit.scope_take ps0 (setP ps0 ad x) (by simp [setP]) (by simp [setP])
  simp only [a4] at a3
  have a5 := seqW_some a3 rfl (pexecW_skip i32 fu (setP ps0 ad x) ps)
  refine ⟨_, a5, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simp [vwp_rdK]
  · simp [vwp_rdK, setP, NExpr.nodes, Container.nodes]

theorem setP_same (ps0 : PS) (j ad : Nat) (a : Int) (h : Loc ps0 j ad a) : setP ps0 ad a = ps0 := by
  obtain ⟨hb,hm⟩ := h
  have hl : ad < ps0.mem.length := (List.getElem?_eq_some_iff.mp hm).1
  have hg : ps0.mem[ad] = ⟨i32,a⟩ := by
    have := List.getElem?_eq_getElem hl
    rw [this] at hm
    exact Option.some.inj hm
  obtain ⟨mem,bs⟩ := ps0
  simp only [setP] at hg ⊢
  simp only [PS.mk.injEq, and_true]
  rw [← hg]
  exact List.set_getElem_self hl

theorem setP_setP (ps0 : PS) (ad : Nat) (x y : Int) : setP (setP ps0 ad x) ad y = setP ps0 ad y := by
  simp [setP, List.set_set]

theorem loop_runK (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank) (hn : ps.length < 2147483648) :
    ∀ (m a : Nat) (ps0 : PS) (j ad : Nat), Loc ps0 j ad a → a < ps.length → rank a ≤ m → ∀ fu, m + 2 ≤ fu →
      ∃ (res : PRW) (r : Nat), pexecW i32 fu (loopCK j) ps0 ps = some res ∧ res.ps = setP ps0 ad r ∧ res.vec = ps ∧
        res.ret = none ∧ Reach ps a r ∧ r < ps.length ∧ (∃ v, ps[r]? = some v ∧ v < 0) ∧
        res.cost ≤ 16 * m + 8 ∧ res.need ≤ ps0.mem.length + ps0.bs.length + 16 ∧ res.wk = 0 := by
  intro m
  induction m with
  | zero =>
    intro a ps0 j ad hl ha hr fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    obtain ⟨x, hx⟩ : ∃ x, ps[a]? = some x := ⟨ps[a], by simp [ha]⟩
    have hxv := hF.valid x (List.mem_of_getElem? hx)
    have hneg : x < 0 := by
      by_contra hh
      have := hF.decrease a x hx (by omega)
      omega
    have hc := cond_valK ps ps0 j ad a hl hn ha x hx hxv
    rw [if_neg (by omega)] at hc
    rw [pexecW_while, hc]
    simp only [Bind.bind, Option.bind, ite_true, vwp_condK]
    refine ⟨_, a, rfl, (setP_same ps0 j ad a hl).symm, rfl, rfl, Reach.refl a, ha, ⟨x, hx, hneg⟩, ?_, ?_, rfl⟩
    · simp
    · simp
  | succ m ih =>
    intro a ps0 j ad hl ha hr fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    obtain ⟨x, hx⟩ : ∃ x, ps[a]? = some x := ⟨ps[a], by simp [ha]⟩
    have hxv := hF.valid x (List.mem_of_getElem? hx)
    have hc := cond_valK ps ps0 j ad a hl hn ha x hx hxv
    by_cases hx0 : 0 ≤ x
    · rw [if_pos hx0] at hc
      have hxl := hF.inside a x hx hx0
      have hdec := hF.decrease a x hx hx0
      obtain ⟨r1, h1, p1, v1, ret1, c1, n1, w1⟩ := iterK ps ps0 j ad a hl hn ha x hx hxv hx0 (fu'+1)
      have hxn : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg hx0
      have hl1 : Loc (setP ps0 ad ((x.toNat : Nat) : Int)) j ad ((x.toNat : Nat) : Int) := loc_set ps0 j ad a _ hl
      obtain ⟨r2, r, h2, p2, v2, ret2, hreach, hrl, hroot, c2, n2, w2⟩ :=
        ih x.toNat (setP ps0 ad ((x.toNat : Nat) : Int)) j ad hl1 (by omega) (by omega) fu' (by omega)
      have p1' : r1.ps = setP ps0 ad ((x.toNat : Nat) : Int) := by rw [p1, hxn]
      rw [pexecW_while, hc]
      simp only [Bind.bind, Option.bind, h1, ret1, p1', v1, h2, vwp_condK]
      refine ⟨⟨r2.ps, r2.vec, r2.ret, 7+1+r1.cost+r2.cost, max (ps0.mem.length +
        ps0.bs.length + 7 + 2) (max r1.need r2.need), r1.wk+r2.wk⟩, r, by simp, ?_, v2, ret2,
        Reach.step a x.toNat r (by simp [Parent, hxn, hx]) hreach, hrl, hroot, ?_, ?_, ?_⟩
      · simp only [p2, setP_setP]
      · simp; omega
      · simp [setP] at n2 ⊢
        omega
      · simp [w1, w2]
    · rw [if_neg hx0] at hc
      rw [pexecW_while, hc]
      simp only [Bind.bind, Option.bind, ite_true, vwp_condK]
      refine ⟨_, a, rfl, (setP_same ps0 j ad a hl).symm, rfl, rfl, Reach.refl a, ha, ⟨x, hx, by omega⟩, ?_, ?_, rfl⟩
      · simp
      · simp


def appI (ps : PS) (v : Int) : PS := ⟨ps.mem ++ [⟨i32,v⟩],ps.bs ++ [⟨ps.mem.length,true⟩]⟩

theorem loc_app_new (ps0 : PS) (v : Int) : Loc (appI ps0 v) ps0.bs.length ps0.mem.length v := by
  refine ⟨?_,?_⟩ <;> simp [appI]

theorem loc_app_old (ps0 : PS) (j ad : Nat) (a v : Int) (h : Loc ps0 j ad a) : Loc (appI ps0 v) j ad a := by
  obtain ⟨hb,hm⟩ := h
  have h1 : j < ps0.bs.length := (List.getElem?_eq_some_iff.mp hb).1
  have h2 : ad < ps0.mem.length := (List.getElem?_eq_some_iff.mp hm).1
  refine ⟨?_,?_⟩
  · simp only [appI]; rw [List.getElem?_append_left h1]; exact hb
  · simp only [appI]; rw [List.getElem?_append_left h2]; exact hm

theorem loc_set_other (ps0 : PS) (j ad ad' : Nat) (a x : Int) (h : Loc ps0 j ad a) (hne : ad' ≠ ad) :
    Loc (setP ps0 ad' x) j ad a := by
  obtain ⟨hb,hm⟩ := h
  refine ⟨hb,?_⟩
  simp only [setP]
  rw [List.getElem?_set_ne hne]
  exact hm

theorem decl_step (ps0 : PS) (vec : List Int) (j ad : Nat) (a : Int) (h : Loc ps0 j ad a) (hv : i32.valid a = true) :
    pstmtW i32 (.declare i32 true (.variable i32 (j+1))) ps0 vec =
      some ⟨appI ps0 a,vec,none,2,ps0.mem.length+ps0.bs.length+5,0⟩ := by
  have hd : vdenL i32 vec (penv1 ps0) (NExpr.variable i32 (j+1)) = some a := by
    rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact env_loc ps0 j ad a h hv
  have := pstmtW_declare_ok i32 ps0 vec i32 true (.variable i32 (j+1)) a hd a (conv_signed i32 rfl rfl _ hv)
  rw [this]
  simp [vwp, appI, NExpr.nodes]


abbrev dV (k : Nat) : Command := .primitive (.declare i32 true (.variable i32 k))
abbrev eqE : NExpr := .binary bT .eq (.variable i32 5) (.variable i32 8)
abbrev bodySame : Command :=
  .sequence (dV 1) (.sequence (loopCK 2) (.sequence (dV 3) (.sequence (dV 4) (.sequence (dV 2)
    (.sequence (loopCK 5) (.sequence (dV 6) (.sequence (dV 7) (.sequence (.primitive (.ret eqE)) Sk))))))))

theorem body_eqSame : Proofs.UnionFindInstance.UnionFind_same.body = UfBounds.bounds 1 (UfBounds.bounds 2 (bodySame)) := rfl

theorem step_decl {fu : Nat} {rest : Command} {ps0 : PS} {vec : List Int} {j ad : Nat} {a : Int}
    (h : Loc ps0 j ad a) (hv : i32.valid a = true) {r2 : PRW}
    (h2 : pexecW i32 fu rest (appI ps0 a) vec = some r2) :
    pexecW i32 fu (.sequence (dV (j+1)) rest) ps0 vec =
      some ⟨r2.ps,r2.vec,r2.ret,2+r2.cost,max (ps0.mem.length+ps0.bs.length+5) r2.need,0+r2.wk⟩ :=
  seqW_some ((pexecW_prim i32 fu _ ps0 vec).trans (decl_step ps0 vec j ad a h hv)) rfl h2

def S0 (P : List Cell) (a b : Int) : PS := ⟨P ++ [⟨i32,a⟩,⟨i32,b⟩],[⟨P.length,true⟩,⟨P.length+1,true⟩]⟩

theorem S0_loc0 (P : List Cell) (a b : Int) : Loc (S0 P a b) 0 P.length a := by
  refine ⟨by simp [S0],?_⟩
  simp [S0]

theorem S0_loc1 (P : List Cell) (a b : Int) : Loc (S0 P a b) 1 (P.length+1) b := by
  refine ⟨by simp [S0],?_⟩
  simp [S0, List.getElem?_append_right]


theorem step_loop {fu : Nat} {rest : Command} {ps0 : PS} {vec : List Int} {j : Nat} {r1 r2 : PRW}
    (h1 : pexecW i32 fu (loopCK j) ps0 vec = some r1) (hr : r1.ret = none)
    (h2 : pexecW i32 fu rest r1.ps r1.vec = some r2) :
    pexecW i32 fu (.sequence (loopCK j) rest) ps0 vec =
      some ⟨r2.ps,r2.vec,r2.ret,r1.cost+r2.cost,max r1.need r2.need,r1.wk+r2.wk⟩ :=
  seqW_some h1 hr h2

theorem eqE_val (ps0 : PS) (vec : List Int) (j1 ad1 j2 ad2 : Nat) (a b : Int) (hj1 : j1 = 4) (hj2 : j2 = 7)
    (h1 : Loc ps0 j1 ad1 a) (h2 : Loc ps0 j2 ad2 b) (ha : i32.valid a = true) (hb : i32.valid b = true) :
    vdenL i32 vec (penv1 ps0) eqE = some (if a = b then 1 else 0) := by
  subst hj1 hj2
  have e1 := env_loc ps0 4 ad1 a h1 ha
  have e2 := env_loc ps0 7 ad2 b h2 hb
  rw [vdenL_scalar _ _ _ _ rfl, den_binary, den_variable, den_variable, e1, e2]
  simp only [Option.bind_some]
  have : binaryValue .eq a b = if a = b then 1 else 0 := by
    by_cases h : a = b <;> simp [binaryValue, h]
  rw [this]
  simp only [bT]; unfold Ty.convert
  by_cases h : a = b <;> simp [h]

theorem vwp_eqE : vwp eqE = (3,3) := by simp [vwp, NExpr.scalarOnly, NExpr.nodes]


@[simp] theorem appI_mem_length (ps : PS) (v : Int) : (appI ps v).mem.length = ps.mem.length + 1 := by simp [appI]
@[simp] theorem appI_bs_length (ps : PS) (v : Int) : (appI ps v).bs.length = ps.bs.length + 1 := by simp [appI]
@[simp] theorem setP_mem_length (ps : PS) (ad : Nat) (x : Int) : (setP ps ad x).mem.length = ps.mem.length := by simp [setP]
@[simp] theorem setP_bs_length (ps : PS) (ad : Nat) (x : Int) : (setP ps ad x).bs.length = ps.bs.length := by simp [setP]
@[simp] theorem S0_mem_length (P : List Cell) (a b : Int) : (S0 P a b).mem.length = P.length + 2 := by simp [S0]
@[simp] theorem S0_bs_length (P : List Cell) (a b : Int) : (S0 P a b).bs.length = 2 := by simp [S0]

theorem take_appI (ps : PS) (v : Int) (n : Nat) (h : n ≤ ps.mem.length) :
    (appI ps v).mem.take n = ps.mem.take n := by
  simp only [appI]; exact List.take_append_of_le_length h

theorem take_setP (ps : PS) (ad : Nat) (x : Int) (n : Nat) (h : n ≤ ad) :
    (setP ps ad x).mem.take n = ps.mem.take n := by
  simp only [setP]; exact List.take_set_of_le h

theorem S0_take (P : List Cell) (a b : Int) : (S0 P a b).mem.take P.length = P := by
  simp only [S0]; rw [List.take_append_of_le_length (le_refl _)]; simp

theorem body_exec_same (P : List Cell) (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank)
    (hn : ps.length < 2147483648) (a b : Nat) (ha : a < ps.length) (hb : b < ps.length) (fu : Nat)
    (hfa : rank a + 2 ≤ fu) (hfb : rank b + 2 ≤ fu) :
    ∃ (res : PRW) (r1 r2 : Nat), pexecW i32 fu bodySame (S0 P a b) ps = some res ∧
      res.ret = some (if (r1 : Int) = (r2 : Int) then 1 else 0) ∧ Reach ps a r1 ∧ Reach ps b r2 ∧
      r1 < ps.length ∧ (∃ v, ps[r1]? = some v ∧ v < 0) ∧ r2 < ps.length ∧ (∃ v, ps[r2]? = some v ∧ v < 0) ∧
      res.cost ≤ 16 * rank a + 16 * rank b + 60 ∧ res.need ≤ P.length + 60 ∧ res.wk = 0 ∧
      res.vec = ps ∧ res.ps.mem.take P.length = P := by
  have hav : i32.valid (a : Int) = true := i32_valid a (by omega) (by omega)
  have hbv : i32.valid (b : Int) = true := i32_valid b (by omega) (by omega)
  have L0 := S0_loc0 P a b
  have L1b := S0_loc1 P a b
  -- the first loop, on the copy of `a`
  have La : Loc (appI (S0 P a b) a) 2 (P.length+2) a := by simpa using loc_app_new (S0 P a b) (a : Int)
  obtain ⟨q1, r1, hq1, pq1, vq1, retq1, reach1, hr1, hroot1, cq1, nq1, wq1⟩ :=
    loop_runK ps rank hF hn (rank a) a (appI (S0 P a b) a) 2 (P.length+2) La ha (le_refl _) fu hfa
  have hr1v : i32.valid (r1 : Int) = true := i32_valid r1 (by omega) (by omega)
  -- state after the first loop
  have L2 : Loc (setP (appI (S0 P a b) a) (P.length+2) r1) 2 (P.length+2) r1 := loc_set _ _ _ _ _ La
  have L3 : Loc (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) 3 (P.length+3) r1 := by
    simpa using loc_app_new (setP (appI (S0 P a b) a) (P.length+2) r1) (r1 : Int)
  have L4 : Loc (appI (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) r1) 4 (P.length+4) r1 := by
    simpa using loc_app_new (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) (r1 : Int)
  have L4' : Loc (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) 3 (P.length+3) r1 := by
    simpa using loc_app_new (setP (appI (S0 P a b) a) (P.length+2) r1) (r1 : Int)
  have Lb4 : Loc (appI (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) r1) 1 (P.length+1) b := by
    exact loc_app_old _ _ _ _ _ (loc_app_old _ _ _ _ _ (loc_set_other _ _ _ _ _ _
      (loc_app_old _ _ _ _ _ L1b) (by omega)))
  have Lb5 : Loc (appI (appI (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) r1) b) 5 (P.length+5) b := by
    simpa using loc_app_new (appI (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) r1) (b : Int)
  obtain ⟨q2, r2, hq2, pq2, vq2, retq2, reach2, hr2, hroot2, cq2, nq2, wq2⟩ :=
    loop_runK ps rank hF hn (rank b) b _ 5 (P.length+5) Lb5 hb (le_refl _) fu hfb
  have hr2v : i32.valid (r2 : Int) = true := i32_valid r2 (by omega) (by omega)
  have L6 := loc_set _ 5 (P.length+5) (b : Int) (r2 : Int) Lb5
  have L7 : Loc (appI (setP (appI (appI (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) r1) b) (P.length+5) r2) r2) 6
      (P.length+6) r2 := by
    simpa using loc_app_new (setP (appI (appI (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) r1) b) (P.length+5) r2) (r2 : Int)
  have L8 : Loc (appI (appI (setP (appI (appI (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) r1) b) (P.length+5) r2) r2) r2) 7
      (P.length+7) r2 := by
    simpa using loc_app_new (appI (setP (appI (appI (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) r1) b) (P.length+5) r2) r2) (r2 : Int)
  have L84 : Loc (appI (appI (setP (appI (appI (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) r1) b) (P.length+5) r2) r2) r2) 4
      (P.length+4) r1 :=
    loc_app_old _ _ _ _ _ (loc_app_old _ _ _ _ _ (loc_set_other _ _ _ _ _ _ (loc_app_old _ _ _ _ _ L4) (by omega)))
  have ev := eqE_val (appI (appI (setP (appI (appI (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) r1) b) (P.length+5) r2) r2) r2)
    ps 4 (P.length+4) 7 (P.length+7) (r1 : Int) (r2 : Int) rfl rfl L84 L8 hr1v hr2v
  have e9 := seqW_ret (b := Sk) ((pexecW_prim i32 fu _ _ ps).trans (pstmtW_ret_ok i32 _ ps eqE _ ev)) rfl
  have e8 := step_decl (fu := fu) L7 hr2v e9
  have e7 := step_decl (fu := fu) L6 hr2v e8
  rw [← pq2, ← vq2] at e7
  have e6 := step_loop (rest := _) hq2 retq2 e7
  have e5 := step_decl (fu := fu) Lb4 hbv e6
  have e4 := step_decl (fu := fu) L4' hr1v e5
  have e3 := step_decl (fu := fu) L2 hr1v e4
  rw [← pq1, ← vq1] at e3
  have e2 := step_loop (rest := _) hq1 retq1 e3
  have e1 := step_decl (fu := fu) L0 hav e2
  refine ⟨_, r1, r2, e1, rfl, reach1, reach2, hr1, hroot1, hr2, hroot2, ?_, ?_, ?_, ?_, ?_⟩
  · simp [vwp_eqE]
    omega
  · simp only [pq1, pq2, setP_mem_length, setP_bs_length, appI_mem_length, appI_bs_length, S0_mem_length,
      S0_bs_length] at nq1 nq2
    simp [vwp_eqE, pq1, pq2]
    omega
  · simp [wq1, wq2]
  · simp [vq2]
  · show (appI (appI q2.ps r2) r2).mem.take P.length = P
    have side : ∀ n : Nat, n ≤ P.length → n ≤ q2.ps.mem.length := by
      intro n hn'; simp [pq2]; omega
    rw [take_appI _ _ _ (by simp [pq2]; omega), take_appI _ _ _ (by first | omega | (simp [pq2]; omega) | simp [pq2]),
      pq2, take_setP _ _ _ _ (by omega)]
    rw [take_appI _ _ _ (by simp; try omega), take_appI _ _ _ (by simp; try omega), take_appI _ _ _ (by simp; try omega),
      take_setP _ _ _ _ (by omega), take_appI _ _ _ (by simp; try omega), S0_take]


theorem prepare_urr (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : VOKI caller vslot vb V vsc m vbuf) (e1 e2 : NExpr) (v1 v2 : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (hty1 : e1.resultType = i32) (hty2 : e2.resultType = i32)
    (value1 : e1.denote (envOf caller) = some v1) (value2 : e2.denote (envOf caller) = some v2)
    (hv1 : i32.valid v1 = true) (hv2 : i32.valid v2 = true) :
    ∃ t, Good (caller.charge 1 1) t (e1.nodes+e2.nodes) (max e1.nodes e2.nodes) ∧
      ∃ Sinit, prepare caller Proofs.UnionFindInstance.UnionFind_same.parameters
          [.vectorReference vslot,.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.vector 0,.scalar 0,.scalar 1] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨i32,v1⟩,⟨i32,v2⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,false,.root vsc⟩]⟩ ∧
        Sinit.scalars.work = t.scalars.work+4 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc i32 false m vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (by simp)
  have rvec : resolve caller (.vector i32 false) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc i32 false) := by
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
  have bound : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).bindRoot V (.integer i32) vsc false =
      some (⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,false,.root vsc⟩]⟩,0) := by
    have vobject : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).object V (.integer i32) =
        some (vbuf,⟨.integer i32,none,some vsc,[]⟩) :=
      object_runs _ V _ vbuf _ ok.valid ok.vfound ok.vtag rfl
    have vrooted : caller.frame.state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ ok.vtag rfl
    have vmax : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).maximum V = some m :=
      maximum_runs _ V V m ok.lengths vrooted ok.flag
    simp only [Frame.bindRoot,vobject,vmax,Bind.bind,Option.bind]
    simp [Frame.addBinding]
  have hp : Proofs.UnionFindInstance.UnionFind_same.parameters = [.vector i32 false,.scalar i32 false true,.scalar i32 false true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec,res1,res2]
  simp [fs,fr,fb,hmem,hbind,hbase,bound,bindAll,bindOne,CppState.bindArgument,hv1,hv2,callerP,
    NState.observe,CppState.State.observe]
  left
  have g := good.2.2.2.2.1
  simp [NState.charge,NState.observe,CppState.State.observe] at g
  omega


theorem uf_same_correct (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : VOKI caller vslot vb V vsc m vbuf) (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank)
    (hitems : vbuf.items = ps.map Value.integer) (hn : ps.length < 2147483648)
    (hbvalid : vbuf.Valid (accepts (.integer i32))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit i32)
    (howner : vbuf.owner = V)
    (e1 e2 : NExpr) (a b : Nat) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = i32) (ht2 : e2.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (a : Int)) (value2 : e2.denote (envOf caller) = some (b : Int))
    (ha : a + 1 < ps.length) (hb : b + 1 < ps.length) :
    ∃ Sinit fuel res, ∃ r1 r2 : Nat, prepare caller Proofs.UnionFindInstance.UnionFind_same.parameters
        [.vectorReference vslot,.value e1,.value e2] = some Sinit ∧
      Proofs.UnionFindInstance.UnionFind_same.callFuel fuel caller [.vectorReference vslot,.value e1,.value e2] =
        .finished (res,.scalar (if (r1 : Int) = (r2 : Int) then 1 else 0)) ∧
      Reach ps a r1 ∧ Reach ps b r2 ∧ r1 < ps.length ∧ (∃ v, ps[r1]? = some v ∧ v < 0) ∧
      r2 < ps.length ∧ (∃ v, ps[r2]? = some v ∧ v < 0) ∧
      ScalarPost3 caller Sinit res (e1.nodes+e2.nodes) (16 * rank a + 16 * rank b + 180) caller.scalars.memory 0 V ps := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_urr caller ok e1 e2 (a : Int) (b : Int) hs1 hs2 ht1 ht2 value1 value2
      (i32_valid a (by omega) (by omega)) (i32_valid b (by omega) (by omega))
  let vc : VCtx := ⟨i32,false,m,V,vsc,vbuf,ps,hitems,fun h => absurd h (by decide),by omega,
    caller.frame.state.liveSpace,caller.frame.state.storage.work,caller.scope+1,
    caller.frame.state.storage.objects.length⟩
  have fwS : FW vc ps vbuf 0 Sinit.frame := by
    rw [sFrame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,hitems,hbvalid,hlimit,howner,by omega⟩
    intro owner k h
    have := ok.strict owner k h
    show k < caller.scope+1
    omega
  have hbody := body_exec_same (callerP caller) ps rank hF hn a b (by omega) (by omega) (max (rank a) (rank b) + 2)
    (by omega) (by omega)
  obtain ⟨rr,r1,r2,hexec,hret,hreach1,hreach2,hrl1,hroot1,hrl2,hroot2,hcost,hneed,hwk,hvec,htake⟩ := hbody
  have ea := env_loc (S0 (callerP caller) a b) 0 (callerP caller).length a
    (S0_loc0 _ _ _) (i32_valid a (by omega) (by omega))
  have eb := env_loc (S0 (callerP caller) a b) 1 ((callerP caller).length+1) b
    (S0_loc1 _ _ _) (i32_valid b (by omega) (by omega))
  have hexec' := UfBounds.prepend_bounds ea hn (by omega) (by omega)
    (UfBounds.prepend_bounds eb hn (by omega) (by omega) hexec)
  have hneed' : (UfBounds.bounded (S0 (callerP caller) a b) (UfBounds.bounded (S0 (callerP caller) a b) rr)).need ≤ (callerP caller).length+112 := by
    simp only [UfBounds.bounded,S0,List.length_append,List.length_cons,List.length_nil]
    omega
  have hcost' : (UfBounds.bounded (S0 (callerP caller) a b) (UfBounds.bounded (S0 (callerP caller) a b) rr)).cost ≤ 16 * rank a + 16 * rank b + 160 := by
    dsimp [UfBounds.bounded]; omega
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have gw1 := good.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hres : bT.valid (if (r1 : Int) = (r2 : Int) then 1 else 0) = true := by
    by_cases h : (r1 : Int) = (r2 : Int) <;> simp [h, bT, Ty.valid]
  have hpost := call_vecw vc false (fun h => absurd h (by decide)) caller Proofs.UnionFindInstance.UnionFind_same
    [.vectorReference vslot,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨i32,(a : Int)⟩ : Cell),⟨i32,(b : Int)⟩])
    [(⟨(callerP caller).length,true⟩ : CppState.Binding),⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [UfRootCall.take_P caller]) ok.base (by decide) (max (rank a) (rank b) + 2) (UfBounds.bounded (S0 (callerP caller) a b) (UfBounds.bounded (S0 (callerP caller) a b) rr))
    (by rw [body_eqSame]; exact hexec') _ hret bT rfl hres hneed' (by simp) (e1.nodes+e2.nodes)
    (16 * rank a + 16 * rank b + 180) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  dsimp only [UfBounds.bounded,UfBounds.charged] at post
  refine ⟨Sinit,fuel,res,r1,r2,hprep,hrun,hreach1,hreach2,hrl1,hroot1,hrl2,hroot2,?_⟩
  have hle : caller.scalars.memory.length ≤ (callerP caller).length := by omega
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    calc rr.ps.mem.take caller.scalars.memory.length
        = (rr.ps.mem.take (callerP caller).length).take caller.scalars.memory.length := by
          rw [List.take_take, Nat.min_eq_left hle]
      _ = (callerP caller).take caller.scalars.memory.length := by rw [htake]
      _ = caller.scalars.memory := by simp only [callerP]; exact List.take_left' rfl
  rw [hs', hvec, hwk] at post
  exact post

end Proofs.UfSameCall
