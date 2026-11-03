import Proofs.UfSameCall
import Proofs.UfFindCall
import Proofs.Generated.UnionFind

namespace Proofs.UfUniteCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.VecStraight Proofs.VecCall Proofs.VecKit
open Proofs.CppNestedFacts Proofs.IntSim Proofs.ScalarCall Proofs.VecWrite Proofs.VecWriteCall Proofs.VecKitW
open Proofs.QuotientSearch Proofs.VectorFillCall Proofs.PrefixSumsCall Proofs.UfRootCall Proofs.UfSameCall
open Proofs.VectorSumCall (conv_signed i32_valid)
open Proofs.CppState (Cell)
open Proofs.PowModStep (Sk)
open Proofs.UfFindCall (reach_det reach_trans reach_rank root_reach)

def T8 (P : List Cell) (a b : Nat) (r1 r2 : Nat) : PS :=
  appI (appI (setP (appI (appI (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) r1) b) (P.length+5) r2) r2) r2

abbrev preCmd (tail : Command) : Command :=
  .sequence (dV 1) (.sequence (loopCK 2) (.sequence (dV 3) (.sequence (dV 4) (.sequence (dV 2)
    (.sequence (loopCK 5) (.sequence (dV 6) (.sequence (dV 7) tail)))))))

theorem prefix_exec (tail : Command) (P : List Cell) (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank)
    (hn : ps.length < 2147483648) (a b : Nat) (ha : a < ps.length) (hb : b < ps.length) (fu : Nat)
    (hfa : rank a + 2 ≤ fu) (hfb : rank b + 2 ≤ fu)
    (htail : ∀ r1 r2 : Nat, Reach ps a r1 → Reach ps b r2 → r1 < ps.length → (∃ v, ps[r1]? = some v ∧ v < 0) →
      r2 < ps.length → (∃ v, ps[r2]? = some v ∧ v < 0) → ∃ rt, pexecW i32 fu tail (T8 P a b r1 r2) ps = some rt) :
    ∃ (r1 r2 : Nat) (rt res : PRW), Reach ps a r1 ∧ Reach ps b r2 ∧ r1 < ps.length ∧ (∃ v, ps[r1]? = some v ∧ v < 0) ∧
      r2 < ps.length ∧ (∃ v, ps[r2]? = some v ∧ v < 0) ∧
      pexecW i32 fu tail (T8 P a b r1 r2) ps = some rt ∧ pexecW i32 fu (preCmd tail) (S0 P a b) ps = some res ∧
      res.ps = rt.ps ∧ res.vec = rt.vec ∧ res.ret = rt.ret ∧ res.cost ≤ 16 * rank a + 16 * rank b + 40 + rt.cost ∧
      res.need ≤ max (P.length + 40) rt.need ∧ res.wk = rt.wk := by
  have hav : i32.valid (a : Int) = true := i32_valid a (by omega) (by omega)
  have hbv : i32.valid (b : Int) = true := i32_valid b (by omega) (by omega)
  have L0 := S0_loc0 P a b
  have L1b := S0_loc1 P a b
  have La : Loc (appI (S0 P a b) a) 2 (P.length+2) a := by simpa using loc_app_new (S0 P a b) (a : Int)
  obtain ⟨q1, r1, hq1, pq1, vq1, retq1, reach1, hr1, hroot1, cq1, nq1, wq1⟩ :=
    loop_runK ps rank hF hn (rank a) a (appI (S0 P a b) a) 2 (P.length+2) La ha (le_refl _) fu hfa
  have hr1v : i32.valid (r1 : Int) = true := i32_valid r1 (by omega) (by omega)
  have L2 : Loc (setP (appI (S0 P a b) a) (P.length+2) r1) 2 (P.length+2) r1 := loc_set _ _ _ _ _ La
  have L4' : Loc (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) 3 (P.length+3) r1 := by
    simpa using loc_app_new (setP (appI (S0 P a b) a) (P.length+2) r1) (r1 : Int)
  have L4 : Loc (appI (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) r1) 4 (P.length+4) r1 := by
    simpa using loc_app_new (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) (r1 : Int)
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
  obtain ⟨rt, hrt⟩ := htail r1 r2 reach1 reach2 hr1 hroot1 hr2 hroot2
  have e8 := step_decl (fu := fu) L7 hr2v (show pexecW i32 fu tail
    (appI (appI (setP (appI (appI (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) r1) b) (P.length+5) r2) r2) r2) ps = some rt from hrt)
  have e7 := step_decl (fu := fu) L6 hr2v e8
  rw [← pq2, ← vq2] at e7
  have e6 := step_loop (rest := _) hq2 retq2 e7
  have e5 := step_decl (fu := fu) Lb4 hbv e6
  have e4 := step_decl (fu := fu) L4' hr1v e5
  have e3 := step_decl (fu := fu) L2 hr1v e4
  rw [← pq1, ← vq1] at e3
  have e2 := step_loop (rest := _) hq1 retq1 e3
  have e1 := step_decl (fu := fu) L0 hav e2
  refine ⟨r1, r2, rt, _, reach1, reach2, hr1, hroot1, hr2, hroot2, hrt, e1, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · simp [vq2]
  · simp
    omega
  · simp only [pq1, pq2, setP_mem_length, setP_bs_length, appI_mem_length, appI_bs_length, S0_mem_length,
      S0_bs_length] at nq1 nq2
    simp [pq1, pq2]
    omega
  · simp [wq1, wq2]


abbrev negK (j : Nat) : NExpr := .binary i32 .sub (.literal i32 0) (rdK j)
abbrev cond2U : NExpr := .binary bT .lt (negK 4) (negK 7)
abbrev swapBlock : Command :=
  .sequence (.scope (.sequence (.primitive (.declare i32 true (.variable i32 5)))
    (.sequence (.primitive (.assign 5 i32 (.variable i32 8)))
      (.sequence (.primitive (.assign 8 i32 (.variable i32 9))) Sk)))) Sk
abbrev B1 : Command := .branch eqE (.sequence (.scope (.sequence (.primitive (.ret (.variable i32 5))) Sk)) Sk) Sk
abbrev B2 : Command := .branch cond2U swapBlock Sk
abbrev W1 : Command := .primitive (.write (.local 0) i32 (.cast u64 (.variable i32 5)) (.binary i32 .add (rdK 4) (rdK 7)))
abbrev W2 : Command := .primitive (.write (.local 0) i32 (.cast u64 (.variable i32 8)) (.variable i32 5))
abbrev lastE : NExpr := .binary i32 .sub (.cast i32 (.size (.integer i32) (.local 0))) (.literal i32 1)
abbrev declLast : Command := .primitive (.declare i32 true lastE)
abbrev W3 : Command := .primitive (.write (.local 0) i32 (.cast u64 (.variable i32 9)) (.binary i32 .add (rdK 8) (.literal i32 1)))
abbrev retX : Command := .sequence (.primitive (.ret (.variable i32 5))) Sk
abbrev tailU : Command :=
  .sequence B1 (.sequence B2 (.sequence W1 (.sequence W2 (.sequence declLast (.sequence W3 retX)))))

theorem body_eqU : Proofs.UnionFindInstance.UnionFind_unite.body = UfBounds.bounds 1 (UfBounds.bounds 2 (preCmd tailU)) := rfl

theorem vwp_negK (j : Nat) : vwp (negK j) = (7,7) := rfl
theorem vwp_cond2U : vwp cond2U = (15,15) := rfl

theorem negK_val (ps : List Int) (ps0 : PS) (j ad a : Nat) (h : Loc ps0 j ad a) (hn : ps.length < 2147483648)
    (ha : a < ps.length) (x : Int) (hx : ps[a]? = some x) (hxv : i32.valid x = true) (hneg : i32.valid (0 - x) = true) :
    vdenL i32 ps (penv1 ps0) (negK j) = some (0 - x) := by
  have hb : (negK j).scalarOnly = false := rfl
  have hl : vdenL i32 ps (penv1 ps0) (NExpr.literal i32 0) = some 0 := by
    rw [vdenL_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 0 = true from rfl)]
  rw [vdenL_binary _ _ _ _ _ _ _ hb, hl, rdK_val ps ps0 j ad a h hn ha x hx hxv, Option.bind_some, Option.bind_some]
  have : binaryValue .sub 0 x = 0 - x := rfl
  rw [this]
  exact conv_signed i32 rfl rfl _ hneg

theorem cond2_val (ps : List Int) (ps0 : PS) (ad1 ad2 a1 a2 : Nat) (h1 : Loc ps0 4 ad1 a1) (h2 : Loc ps0 7 ad2 a2)
    (hn : ps.length < 2147483648) (ha1 : a1 < ps.length) (ha2 : a2 < ps.length) (x1 x2 : Int)
    (hx1 : ps[a1]? = some x1) (hx2 : ps[a2]? = some x2) (hv1 : i32.valid x1 = true) (hv2 : i32.valid x2 = true)
    (hn1 : i32.valid (0 - x1) = true) (hn2 : i32.valid (0 - x2) = true) :
    vdenL i32 ps (penv1 ps0) cond2U = some (if 0 - x1 < 0 - x2 then 1 else 0) := by
  have hb : cond2U.scalarOnly = false := rfl
  rw [vdenL_binary _ _ _ _ _ _ _ hb, negK_val ps ps0 4 ad1 a1 h1 hn ha1 x1 hx1 hv1 hn1,
    negK_val ps ps0 7 ad2 a2 h2 hn ha2 x2 hx2 hv2 hn2, Option.bind_some, Option.bind_some]
  have : binaryValue .lt (0 - x1) (0 - x2) = if 0 - x1 < 0 - x2 then 1 else 0 := by
    show (if 0 - x1 < 0 - x2 then 1 else 0) = _
    rfl
  rw [this]
  simp only [bT]; unfold Ty.convert
  by_cases h : 0 - x1 < 0 - x2
  · have h' : x2 < x1 := by omega
    simp [h, h']
  · have h' : ¬ x2 < x1 := by omega
    simp [h, h']


theorem scope_swap_eq (ps0 : PS) (ad4 ad7 : Nat) (x y : Int) (hbs : ps0.bs.length = 8)
    (l4 : ad4 < ps0.mem.length) (l7 : ad7 < ps0.mem.length) :
    (⟨(setP (setP (appI ps0 x) ad4 y) ad7 x).mem.take ps0.mem.length,
      (setP (setP (appI ps0 x) ad4 y) ad7 x).bs.take ps0.bs.length⟩ : PS) = setP (setP ps0 ad4 y) ad7 x := by
  obtain ⟨mem,bs⟩ := ps0
  simp only [setP, appI] at *
  simp only [PS.mk.injEq]
  constructor
  · apply List.ext_getElem?
    intro i
    simp only [List.getElem?_take, List.getElem?_set, List.length_set, List.length_append, List.getElem?_append]
    by_cases h1 : ad4 = i <;> by_cases h2 : ad7 = i <;> by_cases h3 : i < mem.length <;> simp_all <;> omega
  · simp [List.take_append_of_le_length]

theorem swap_exec (ps0 : PS) (vec : List Int) (ad4 ad7 x y : Nat) (h4 : Loc ps0 4 ad4 x) (h7 : Loc ps0 7 ad7 y)
    (hne : ad4 ≠ ad7) (hbs : ps0.bs.length = 8) (hx : i32.valid (x : Int) = true) (hy : i32.valid (y : Int) = true)
    (fu : Nat) :
    ∃ r, pexecW i32 fu swapBlock ps0 vec = some r ∧ r.ps = setP (setP ps0 ad4 (y : Int)) ad7 (x : Int) ∧
      r.vec = vec ∧ r.ret = none ∧ r.cost ≤ 20 ∧ r.need ≤ ps0.mem.length + ps0.bs.length + 20 ∧ r.wk = 0 := by
  have l4 : ad4 < ps0.mem.length := (List.getElem?_eq_some_iff.mp h4.2).1
  have d := decl_step ps0 vec 4 ad4 (x : Int) h4 hx
  have d' := (pexecW_prim i32 fu (.declare i32 true (.variable i32 5)) _ _).trans d
  have L8 : Loc (appI ps0 (x : Int)) 8 ps0.mem.length x := by
    have := loc_app_new ps0 (x : Int)
    rw [hbs] at this
    exact this
  have L7 := loc_app_old ps0 7 ad7 (y : Int) (x : Int) h7
  have L4 := loc_app_old ps0 4 ad4 (x : Int) (x : Int) h4
  obtain ⟨hb4, hm4⟩ := L4
  have s1 := pstmtW_assign_ok i32 (appI ps0 (x : Int)) vec 4 i32 (.variable i32 8) (y : Int)
    (by rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact env_loc _ 7 ad7 y L7 hy) ⟨ad4,true⟩ ⟨i32,(x : Int)⟩ hb4 hm4
    rfl hx rfl (y : Int) (conv_signed i32 rfl rfl _ hy)
  have a1 := (pexecW_prim i32 fu (.assign 5 i32 (.variable i32 8)) _ _).trans s1
  have L8' : Loc (setP (appI ps0 (x : Int)) ad4 (y : Int)) 8 ps0.mem.length x :=
    loc_set_other _ _ _ _ _ _ L8 (by omega)
  have L7' : Loc (setP (appI ps0 (x : Int)) ad4 (y : Int)) 7 ad7 y := loc_set_other _ _ _ _ _ _ L7 hne
  obtain ⟨hb7, hm7⟩ := L7'
  have s2 := pstmtW_assign_ok i32 (setP (appI ps0 (x : Int)) ad4 (y : Int)) vec 7 i32 (.variable i32 9) (x : Int)
    (by rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact env_loc _ 8 _ x L8' hx) ⟨ad7,true⟩ ⟨i32,(y : Int)⟩ hb7 hm7
    rfl hy rfl (x : Int) (conv_signed i32 rfl rfl _ hx)
  have a2 := (pexecW_prim i32 fu (.assign 8 i32 (.variable i32 9)) _ _).trans s2
  have c3 := seqW_some a2 rfl (pexecW_skip i32 fu (setP (setP (appI ps0 (x : Int)) ad4 (y : Int)) ad7 (x : Int)) vec)
  have c2 := seqW_some a1 rfl c3
  have c1 := seqW_some d' rfl c2
  have sc := pexecW_scope i32 fu _ _ _ _ c1
  have l7 : ad7 < ps0.mem.length := (List.getElem?_eq_some_iff.mp h7.2).1
  have tk := scope_swap_eq ps0 ad4 ad7 (x : Int) (y : Int) hbs l4 l7
  simp only [tk] at sc
  have c4 := seqW_some sc rfl (pexecW_skip i32 fu (setP (setP ps0 ad4 (y : Int)) ad7 (x : Int)) vec)
  refine ⟨_, c4, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes]
  · simp [vwp, NExpr.nodes, hbs]
  · simp


theorem pexecW_branch_true (ty0 : Ty) (fu : Nat) (c : NExpr) (y n : Command) (ps : PS) (vec : List Int) (v : Int)
    (hv : vdenL ty0 vec (penv1 ps) c = some v) (hne : v ≠ 0) (r : PRW) (hr : pexecW ty0 fu y ps vec = some r) :
    pexecW ty0 fu (.branch c y n) ps vec =
      some ⟨r.ps,r.vec,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need,r.wk⟩ := by
  rw [pexecW]
  simp [hv, hne, hr]

theorem pexecW_branch_false (ty0 : Ty) (fu : Nat) (c : NExpr) (y n : Command) (ps : PS) (vec : List Int)
    (hv : vdenL ty0 vec (penv1 ps) c = some 0) (r : PRW) (hr : pexecW ty0 fu n ps vec = some r) :
    pexecW ty0 fu (.branch c y n) ps vec =
      some ⟨r.ps,r.vec,r.ret,r.cost+(vwp c).1+1,max (ps.mem.length+ps.bs.length+(vwp c).2+2) r.need,r.wk⟩ := by
  rw [pexecW]
  simp [hv, hr]

@[simp] theorem T8_mem_length (P : List Cell) (a b r1 r2 : Nat) : (T8 P a b r1 r2).mem.length = P.length + 8 := by
  simp [T8]
@[simp] theorem T8_bs_length (P : List Cell) (a b r1 r2 : Nat) : (T8 P a b r1 r2).bs.length = 8 := by
  simp [T8]

theorem T8_loc4 (P : List Cell) (a b r1 r2 : Nat) : Loc (T8 P a b r1 r2) 4 (P.length+4) r1 := by
  have L4 : Loc (appI (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) r1) 4 (P.length+4) r1 := by
    simpa using loc_app_new (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) (r1 : Int)
  exact loc_app_old _ _ _ _ _ (loc_app_old _ _ _ _ _ (loc_set_other _ _ _ _ _ _ (loc_app_old _ _ _ _ _ L4) (by omega)))

theorem T8_loc7 (P : List Cell) (a b r1 r2 : Nat) : Loc (T8 P a b r1 r2) 7 (P.length+7) r2 := by
  simpa [T8] using loc_app_new (appI (setP (appI (appI (appI (setP (appI (S0 P a b) a) (P.length+2) r1) r1) r1) b)
    (P.length+5) r2) r2) (r2 : Int)

theorem tail_same (P : List Cell) (a b r : Nat) (ps : List Int) (hr : r < 2147483648) (fu : Nat) :
    ∃ rt, pexecW i32 fu tailU (T8 P a b r r) ps = some rt ∧ rt.ret = some (r : Int) ∧ rt.vec = ps ∧
      rt.wk = 0 ∧ rt.cost ≤ 40 ∧ rt.need ≤ P.length + 40 ∧ rt.ps = T8 P a b r r := by
  have hrv : i32.valid (r : Int) = true := i32_valid r (by omega) (by omega)
  have ev := eqE_val (T8 P a b r r) ps 4 (P.length+4) 7 (P.length+7) (r : Int) (r : Int) rfl rfl
    (T8_loc4 P a b r r) (T8_loc7 P a b r r) hrv hrv
  rw [if_pos rfl] at ev
  have rv : vdenL i32 ps (penv1 (T8 P a b r r)) (NExpr.variable i32 5) = some (r : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact env_loc _ 4 _ r (T8_loc4 P a b r r) hrv
  have rs := pstmtW_ret_ok i32 (T8 P a b r r) ps (.variable i32 5) (r : Int) rv
  have in1 := seqW_ret (b := Sk) ((pexecW_prim i32 fu (.ret (.variable i32 5)) _ _).trans rs) rfl
  have sc := pexecW_scope i32 fu _ _ _ _ in1
  have in2 := seqW_ret (b := Sk) sc rfl
  have br := pexecW_branch_true i32 fu eqE _ Sk (T8 P a b r r) ps 1 ev (by simp) _ in2
  refine ⟨_, seqW_ret br rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp, NExpr.nodes]
  · simp [vwp, NExpr.nodes]
  · simp
    have h1 : List.take (P.length + 8) (T8 P a b r r).mem = (T8 P a b r r).mem :=
      List.take_of_length_le (le_of_eq (T8_mem_length P a b r r))
    have h2 : List.take 8 (T8 P a b r r).bs = (T8 P a b r r).bs :=
      List.take_of_length_le (le_of_eq (T8_bs_length P a b r r))
    rw [h1, h2]


theorem lastE_val (ps : List Int) (ps0 : PS) (hn : ps.length < 2147483648) (hl : 1 ≤ ps.length) :
    vdenL i32 ps (penv1 ps0) lastE = some ((ps.length - 1 : Nat) : Int) := by
  have hb : lastE.scalarOnly = false := rfl
  have hr2 : (NExpr.cast i32 (.size (.integer i32) (.local 0))).scalarOnly = false := rfl
  have hr : (NExpr.size (.integer i32) (.local 0)).scalarOnly = false := rfl
  have hsz : vdenL i32 ps (penv1 ps0) (.size (.integer i32) (.local 0)) = some (ps.length : Int) := by
    simp [vdenL, hr]
  have hn' : i32.convert (ps.length : Int) = some (ps.length : Int) :=
    conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega))
  have c1 : vdenL i32 ps (penv1 ps0) (.cast i32 (.size (.integer i32) (.local 0))) = some (ps.length : Int) := by
    rw [vdenL_cast i32 ps _ _ _ hr2, hsz, Option.bind_some, hn']
  have c2 : vdenL i32 ps (penv1 ps0) (NExpr.literal i32 1) = some 1 := by
    rw [vdenL_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 1 = true from rfl)]
  rw [vdenL_binary _ _ _ _ _ _ _ hb, c1, c2, Option.bind_some, Option.bind_some]
  have : binaryValue .sub (ps.length : Int) 1 = ((ps.length - 1 : Nat) : Int) := by
    show (ps.length : Int) - 1 = _; omega
  rw [this]
  exact conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega))

theorem tail_writes (T9 : PS) (ps : List Int) (ad4 ad7 X Y : Nat) (vX vY vL : Int) (h4 : Loc T9 4 ad4 X)
    (h7 : Loc T9 7 ad7 Y) (hn : ps.length < 2147483648) (hX : X < ps.length) (hY : Y < ps.length)
    (hbs : T9.bs.length = 8) (hXL : X ≠ ps.length - 1) (hYL : Y ≠ ps.length - 1) (hvL : ps[ps.length - 1]? = some vL)
    (hvX : ps[X]? = some vX) (hvY : ps[Y]? = some vY) (gX : i32.valid vX = true) (gY : i32.valid vY = true)
    (gL : i32.valid vL = true) (hsum : i32.valid (vX + vY) = true) (hL1 : i32.valid (vL + 1) = true) (fu : Nat) :
    ∃ rt, pexecW i32 fu (.sequence W1 (.sequence W2 (.sequence declLast (.sequence W3 retX)))) T9 ps = some rt ∧
      rt.ret = some (X : Int) ∧ rt.vec = ((ps.set X (vX + vY)).set Y (X : Int)).set (ps.length - 1) (vL + 1) ∧
      rt.wk = 3 ∧ rt.cost ≤ 120 ∧ rt.need ≤ T9.mem.length + T9.bs.length + 50 ∧
      rt.ps = appI T9 ((ps.length - 1 : Nat) : Int) := by
  have hXv : i32.valid (X : Int) = true := i32_valid X (by omega) (by omega)
  have hYv : i32.valid (Y : Int) = true := i32_valid Y (by omega) (by omega)
  have hL : 1 ≤ ps.length := by omega
  have hLl : ps.length - 1 < ps.length := by omega
  -- first write
  have iX : vdenL i32 ps (penv1 T9) (NExpr.cast u64 (.variable i32 5)) = some (X : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl]; exact idxK T9 4 ad4 X h4 (by omega)
  have sumv : vdenL i32 ps (penv1 T9) (NExpr.binary i32 .add (rdK 4) (rdK 7)) = some (vX + vY) := by
    have hb : (NExpr.binary i32 .add (rdK 4) (rdK 7)).scalarOnly = false := rfl
    rw [vdenL_binary _ _ _ _ _ _ _ hb, rdK_val ps T9 4 ad4 X h4 hn hX vX hvX gX,
      rdK_val ps T9 7 ad7 Y h7 hn hY vY hvY gY, Option.bind_some, Option.bind_some]
    have : binaryValue .add vX vY = vX + vY := rfl
    rw [this]
    exact conv_signed i32 rfl rfl _ hsum
  have w1 := pstmtW_write_ok i32 T9 ps (.cast u64 (.variable i32 5)) (.binary i32 .add (rdK 4) (rdK 7)) (vX + vY) X
    sumv iX hX hsum
  -- second write
  have iY : vdenL i32 (ps.set X (vX + vY)) (penv1 T9) (NExpr.cast u64 (.variable i32 8)) = some (Y : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl]; exact idxK T9 7 ad7 Y h7 (by omega)
  have vX5 : vdenL i32 (ps.set X (vX + vY)) (penv1 T9) (NExpr.variable i32 5) = some (X : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact env_loc _ 4 ad4 X h4 hXv
  have w2 := pstmtW_write_ok i32 T9 (ps.set X (vX + vY)) (.cast u64 (.variable i32 8)) (.variable i32 5) (X : Int) Y
    vX5 iY (by simpa using hY) hXv
  -- int last = size - 1;
  have hlen2 : ((ps.set X (vX + vY)).set Y (X : Int)).length = ps.length := by simp
  have lv := lastE_val ((ps.set X (vX + vY)).set Y (X : Int)) T9 (by omega) (by omega)
  rw [hlen2] at lv
  have d3 := pstmtW_declare_ok i32 T9 ((ps.set X (vX + vY)).set Y (X : Int)) i32 true lastE ((ps.length - 1 : Nat) : Int) lv
    ((ps.length - 1 : Nat) : Int) (conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega)))
  have e3 : (⟨T9.mem ++ [(⟨i32,((ps.length - 1 : Nat) : Int)⟩ : Cell)],T9.bs ++ [⟨T9.mem.length,true⟩]⟩ : PS) =
      appI T9 ((ps.length - 1 : Nat) : Int) := rfl
  rw [e3] at d3
  -- ps[last] = ps[last] + 1;
  have T10 := loc_app_new T9 ((ps.length - 1 : Nat) : Int)
  have L10 : Loc (appI T9 ((ps.length - 1 : Nat) : Int)) 8 T9.mem.length ((ps.length - 1 : Nat) : Int) := by
    simpa [hbs] using loc_app_new T9 ((ps.length - 1 : Nat) : Int)
  have hget : (((ps.set X (vX + vY)).set Y (X : Int))[ps.length - 1]?) = some vL := by
    rw [List.getElem?_set_ne hYL, List.getElem?_set_ne hXL]
    exact hvL
  have hlt3 : ps.length - 1 < ((ps.set X (vX + vY)).set Y (X : Int)).length := by simp; omega
  have rl := rdK_val ((ps.set X (vX + vY)).set Y (X : Int)) (appI T9 ((ps.length - 1 : Nat) : Int)) 8 T9.mem.length
    (ps.length - 1) L10 (by omega) hlt3 vL hget gL
  have addv : vdenL i32 ((ps.set X (vX + vY)).set Y (X : Int)) (penv1 (appI T9 ((ps.length - 1 : Nat) : Int)))
      (NExpr.binary i32 .add (rdK 8) (.literal i32 1)) = some (vL + 1) := by
    have hb : (NExpr.binary i32 .add (rdK 8) (.literal i32 1)).scalarOnly = false := rfl
    have one : vdenL i32 ((ps.set X (vX + vY)).set Y (X : Int)) (penv1 (appI T9 ((ps.length - 1 : Nat) : Int)))
        (NExpr.literal i32 1) = some 1 := by
      rw [vdenL_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 1 = true from rfl)]
    rw [vdenL_binary _ _ _ _ _ _ _ hb, rl, one, Option.bind_some, Option.bind_some]
    have : binaryValue .add vL 1 = vL + 1 := rfl
    rw [this]
    exact conv_signed i32 rfl rfl _ hL1
  have iL : vdenL i32 ((ps.set X (vX + vY)).set Y (X : Int)) (penv1 (appI T9 ((ps.length - 1 : Nat) : Int)))
      (NExpr.cast u64 (.variable i32 9)) = some ((ps.length - 1 : Nat) : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl]; exact idxK (appI T9 ((ps.length - 1 : Nat) : Int)) 8 T9.mem.length (ps.length - 1) L10 (by omega)
  have w3 := pstmtW_write_ok i32 (appI T9 ((ps.length - 1 : Nat) : Int)) ((ps.set X (vX + vY)).set Y (X : Int))
    (NExpr.cast u64 (.variable i32 9)) (NExpr.binary i32 .add (rdK 8) (.literal i32 1)) (vL + 1) (ps.length - 1)
    addv iL hlt3 hL1
  have h4' : Loc (appI T9 ((ps.length - 1 : Nat) : Int)) 4 ad4 X := loc_app_old _ _ _ _ _ h4
  have rs := pstmtW_ret_ok i32 (appI T9 ((ps.length - 1 : Nat) : Int))
    (((ps.set X (vX + vY)).set Y (X : Int)).set (ps.length - 1) (vL + 1)) (.variable i32 5) (X : Int)
    (by rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact env_loc _ 4 ad4 X h4' hXv)
  have t4 := seqW_ret (b := Sk) ((pexecW_prim i32 fu (.ret (.variable i32 5)) _ _).trans rs) rfl
  have t3 := seqW_some ((pexecW_prim i32 fu _ _ _).trans w3) rfl t4
  have t2 := seqW_some ((pexecW_prim i32 fu _ _ _).trans d3) rfl t3
  have t1 := seqW_some ((pexecW_prim i32 fu _ _ _).trans w2) rfl t2
  have t0 := seqW_some ((pexecW_prim i32 fu _ _ _).trans w1) rfl t1
  refine ⟨_, t0, rfl, rfl, ?_, ?_, ?_, rfl⟩
  · simp
  · simp [vwp, NExpr.nodes, Container.nodes]
  · simp [vwp, NExpr.nodes, Container.nodes, appI]; omega

theorem T8_take (P : List Cell) (a b : Nat) (r1 r2 : Nat) : (T8 P a b r1 r2).mem.take P.length = P := by
  simp only [T8]
  rw [take_appI _ _ _ (by simp <;> omega), take_appI _ _ _ (by simp <;> omega), take_setP _ _ _ _ (by omega),
    take_appI _ _ _ (by simp <;> omega), take_appI _ _ _ (by simp <;> omega), take_appI _ _ _ (by simp <;> omega),
    take_setP _ _ _ _ (by omega), take_appI _ _ _ (by simp <;> omega), S0_take]

theorem tail_diff (P : List Cell) (a b r1 r2 : Nat) (ps : List Int) (hn : ps.length < 2147483648)
    (hr1 : r1 < ps.length) (hr2 : r2 < ps.length) (hL1 : r1 ≠ ps.length - 1) (hL2 : r2 ≠ ps.length - 1)
    (v1 v2 vL : Int) (hv1 : ps[r1]? = some v1) (hv2 : ps[r2]? = some v2) (hvL : ps[ps.length - 1]? = some vL)
    (g1 : i32.valid v1 = true) (g2 : i32.valid v2 = true) (gL : i32.valid vL = true) (hLn : i32.valid (vL + 1) = true)
    (n1 : i32.valid (0 - v1) = true)
    (n2 : i32.valid (0 - v2) = true) (hne : r1 ≠ r2) (hsum : i32.valid (v1 + v2) = true) (fu : Nat) :
    ∃ rt, pexecW i32 fu tailU (T8 P a b r1 r2) ps = some rt ∧
      rt.ret = some ((if 0 - v1 < 0 - v2 then r2 else r1 : Nat) : Int) ∧
      rt.vec = ((ps.set (if 0 - v1 < 0 - v2 then r2 else r1) (v1 + v2)).set (if 0 - v1 < 0 - v2 then r1 else r2)
        ((if 0 - v1 < 0 - v2 then r2 else r1 : Nat) : Int)).set (ps.length - 1) (vL + 1) ∧
      rt.wk = 3 ∧ rt.cost ≤ 160 ∧ rt.need ≤ P.length + 80 ∧ rt.ps.mem.take P.length = P := by
  have hr1v : i32.valid (r1 : Int) = true := i32_valid r1 (by omega) (by omega)
  have hr2v : i32.valid (r2 : Int) = true := i32_valid r2 (by omega) (by omega)
  have ev := eqE_val (T8 P a b r1 r2) ps 4 (P.length+4) 7 (P.length+7) (r1 : Int) (r2 : Int) rfl rfl
    (T8_loc4 P a b r1 r2) (T8_loc7 P a b r1 r2) hr1v hr2v
  rw [if_neg (by omega)] at ev
  have b1 := pexecW_branch_false i32 fu eqE (.sequence (.scope (.sequence (.primitive (.ret (.variable i32 5))) Sk)) Sk) Sk
    (T8 P a b r1 r2) ps ev _ (pexecW_skip i32 fu _ _)
  have c2 := cond2_val ps (T8 P a b r1 r2) (P.length+4) (P.length+7) r1 r2 (T8_loc4 P a b r1 r2) (T8_loc7 P a b r1 r2)
    hn hr1 hr2 v1 v2 hv1 hv2 g1 g2 n1 n2
  by_cases hsw : 0 - v1 < 0 - v2
  · rw [if_pos hsw] at c2
    simp only [if_pos hsw]
    obtain ⟨rs, hrs, pS, vS, retS, cS, nS, wS⟩ := swap_exec (T8 P a b r1 r2) ps (P.length+4) (P.length+7) r1 r2
      (T8_loc4 P a b r1 r2) (T8_loc7 P a b r1 r2) (by omega) (T8_bs_length P a b r1 r2) hr1v hr2v fu
    have b2 := pexecW_branch_true i32 fu cond2U swapBlock Sk (T8 P a b r1 r2) ps 1 c2 (by simp) _ hrs
    -- the state after the swap
    have l4 : Loc (setP (setP (T8 P a b r1 r2) (P.length+4) (r2 : Int)) (P.length+7) (r1 : Int)) 4 (P.length+4) r2 :=
      loc_set_other _ _ _ _ _ _ (loc_set _ _ _ _ _ (T8_loc4 P a b r1 r2)) (by omega)
    have l7 : Loc (setP (setP (T8 P a b r1 r2) (P.length+4) (r2 : Int)) (P.length+7) (r1 : Int)) 7 (P.length+7) r1 :=
      loc_set _ _ _ _ _ (loc_set_other _ _ _ _ _ _ (T8_loc7 P a b r1 r2) (by omega))
    have hs' : i32.valid (v2 + v1) = true := by rw [Int.add_comm]; exact hsum
    obtain ⟨rt, hrt, retW, vecW, wkW, cW, nW, psW⟩ := tail_writes _ ps (P.length+4) (P.length+7) r2 r1 v2 v1 vL
      l4 l7 hn hr2 hr1 (by simp [setP, T8_bs_length]) hL2 hL1 hvL hv2 hv1 g2 g1 gL hs' hLn fu
    have t4 := seqW_some (b := _) b2 retS (by rw [pS, vS]; exact hrt)
    have t3 := seqW_some b1 rfl t4
    refine ⟨_, t3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [retW]
    · simp [vecW, Int.add_comm]
    · simp [wkW, wS]
    · simp [vwp, NExpr.nodes, Container.nodes] at *
      omega
    · simp [vwp, NExpr.nodes, Container.nodes] at *
      omega
    · simp [psW, pS]
      rw [take_appI _ _ _ (by simp [setP, T8_mem_length]), take_setP _ _ _ _ (by omega), take_setP _ _ _ _ (by omega), T8_take]
  · rw [if_neg hsw] at c2
    simp only [if_neg hsw]
    have b2 := pexecW_branch_false i32 fu cond2U swapBlock Sk (T8 P a b r1 r2) ps c2 _ (pexecW_skip i32 fu _ _)
    obtain ⟨rt, hrt, retW, vecW, wkW, cW, nW, psW⟩ := tail_writes (T8 P a b r1 r2) ps (P.length+4) (P.length+7) r1 r2 v1 v2 vL
      (T8_loc4 P a b r1 r2) (T8_loc7 P a b r1 r2) hn hr1 hr2 (T8_bs_length P a b r1 r2) hL1 hL2 hvL hv1 hv2 g1 g2 gL hsum hLn fu
    have t4 := seqW_some (b := _) b2 rfl hrt
    have t3 := seqW_some b1 rfl t4
    refine ⟨_, t3, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [retW]
    · simp [vecW]
    · simp [wkW]
    · simp [vwp, NExpr.nodes, Container.nodes] at *
      omega
    · simp [vwp, NExpr.nodes, Container.nodes] at *
      omega
    · simp [psW]
      rw [take_appI _ _ _ (by simp [T8_mem_length])]
      exact T8_take P a b r1 r2


-- The effect of `uf_unite` on the forest `ps` for the roots `r1` of `a` and `r2` of `b`.
def uniteX (ps : List Int) (r1 r2 : Nat) : Nat := if 0 - ps.getD r1 0 < 0 - ps.getD r2 0 then r2 else r1
def uniteY (ps : List Int) (r1 r2 : Nat) : Nat := if 0 - ps.getD r1 0 < 0 - ps.getD r2 0 then r1 else r2
def uniteVec (ps : List Int) (r1 r2 : Nat) : List Int :=
  if r1 = r2 then ps
  else (ps.set (uniteX ps r1 r2) (ps.getD r1 0 + ps.getD r2 0)).set (uniteY ps r1 r2) (uniteX ps r1 r2 : Int)

theorem getD_of (ps : List Int) (i : Nat) (v : Int) (h : ps[i]? = some v) : ps.getD i 0 = v := by
  simp [List.getD_eq_getElem?_getD, h]

theorem reach_lt (ps : List Int)
    (hnodes : ∀ (i : Nat) (p : Int), i + 1 < ps.length → ps[i]? = some p → 0 ≤ p → p.toNat + 1 < ps.length) :
    ∀ (a r : Nat), Reach ps a r → a + 1 < ps.length → r + 1 < ps.length := by
  intro a r h
  induction h with
  | refl => exact id
  | step a b c hp _ ih =>
    intro ha
    have := hnodes a (b : Int) ha hp (by omega)
    simp at this
    exact ih this

-- The effect of `UnionFind::unite` on the vector `ps`: the link and the decrement of the tree count in the last entry.
def uniteVecC (ps : List Int) (r1 r2 : Nat) : List Int :=
  if r1 = r2 then ps else (uniteVec ps r1 r2).set (ps.length - 1) (ps.getD (ps.length - 1) 0 + 1)

theorem body_exec_unite (P : List Cell) (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank)
    (hn : ps.length < 2147483648) (a b : Nat) (ha : a + 1 < ps.length) (hb : b + 1 < ps.length) (fu : Nat)
    (hfa : rank a + 2 ≤ fu) (hfb : rank b + 2 ≤ fu)
    (hnodes : ∀ (i : Nat) (p : Int), i + 1 < ps.length → ps[i]? = some p → 0 ≤ p → p.toNat + 1 < ps.length)
    (vL : Int) (hvL : ps[ps.length - 1]? = some vL) (hLn : i32.valid (vL + 1) = true)
    (hmin : ∀ x ∈ ps, i32.valid (0 - x) = true)
    (hsum : ∀ (i j : Nat) (x y : Int), i + 1 < ps.length → j + 1 < ps.length → ps[i]? = some x → ps[j]? = some y →
      x < 0 → y < 0 → i32.valid (x + y) = true) :
    ∃ (res : PRW) (r1 r2 : Nat), pexecW i32 fu (preCmd tailU) (S0 P a b) ps = some res ∧
      Reach ps a r1 ∧ Reach ps b r2 ∧ r1 + 1 < ps.length ∧ (∃ v, ps[r1]? = some v ∧ v < 0) ∧
      r2 + 1 < ps.length ∧ (∃ v, ps[r2]? = some v ∧ v < 0) ∧
      res.ret = some (uniteX ps r1 r2 : Int) ∧ res.vec = uniteVecC ps r1 r2 ∧
      res.wk = (if r1 = r2 then 0 else 3) ∧
      res.cost ≤ 16 * rank a + 16 * rank b + 240 ∧ res.need ≤ P.length + 100 ∧ res.ps.mem.take P.length = P := by
  have key := prefix_exec tailU P ps rank hF hn a b (by omega) (by omega) fu hfa hfb (by
    intro r1 r2 reach1 reach2 hr1 hroot1 hr2 hroot2
    have hl1 : r1 + 1 < ps.length := reach_lt ps hnodes a r1 reach1 ha
    have hl2 : r2 + 1 < ps.length := reach_lt ps hnodes b r2 reach2 hb
    by_cases heq : r1 = r2
    · subst heq
      obtain ⟨rt, h, _⟩ := tail_same P a b r1 ps (by omega) fu
      exact ⟨rt, h⟩
    · obtain ⟨v1, hv1, hn1⟩ := hroot1
      obtain ⟨v2, hv2, hn2⟩ := hroot2
      have m1 := List.mem_of_getElem? hv1
      have m2 := List.mem_of_getElem? hv2
      obtain ⟨rt, h, _⟩ := tail_diff P a b r1 r2 ps hn hr1 hr2 (by omega) (by omega) v1 v2 vL hv1 hv2 hvL
        (hF.valid v1 m1) (hF.valid v2 m2) (hF.valid vL (List.mem_of_getElem? hvL)) hLn
        (hmin v1 m1) (hmin v2 m2) heq (hsum r1 r2 v1 v2 hl1 hl2 hv1 hv2 hn1 hn2) fu
      exact ⟨rt, h⟩)
  obtain ⟨r1, r2, rt, res, reach1, reach2, hr1, hroot1, hr2, hroot2, hrt, hres, pS, vS, retS, cS, nS, wS⟩ := key
  have hl1 : r1 + 1 < ps.length := reach_lt ps hnodes a r1 reach1 ha
  have hl2 : r2 + 1 < ps.length := reach_lt ps hnodes b r2 reach2 hb
  refine ⟨res, r1, r2, hres, reach1, reach2, hl1, hroot1, hl2, hroot2, ?_⟩
  by_cases heq : r1 = r2
  · subst heq
    obtain ⟨rt', h', retT, vecT, wkT, cT, nT, psT⟩ := tail_same P a b r1 ps (by omega) fu
    rw [hrt] at h'
    cases h'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [retS, retT]; simp [uniteX]
    · rw [vS, vecT]; simp [uniteVecC]
    · rw [wS, wkT]; simp
    · omega
    · omega
    · rw [pS, psT]; exact T8_take P a b r1 r1
  · obtain ⟨v1, hv1, hn1⟩ := hroot1
    obtain ⟨v2, hv2, hn2⟩ := hroot2
    have m1 := List.mem_of_getElem? hv1
    have m2 := List.mem_of_getElem? hv2
    obtain ⟨rt', h', retT, vecT, wkT, cT, nT, tkT⟩ := tail_diff P a b r1 r2 ps hn hr1 hr2 (by omega) (by omega) v1 v2 vL
      hv1 hv2 hvL (hF.valid v1 m1) (hF.valid v2 m2) (hF.valid vL (List.mem_of_getElem? hvL)) hLn
      (hmin v1 m1) (hmin v2 m2) heq (hsum r1 r2 v1 v2 hl1 hl2 hv1 hv2 hn1 hn2) fu
    rw [hrt] at h'
    cases h'
    have g1 := getD_of ps r1 v1 hv1
    have g2 := getD_of ps r2 v2 hv2
    have gL := getD_of ps (ps.length - 1) vL hvL
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [retS, retT]; simp only [uniteX, g1, g2]
    · rw [vS, vecT]; simp only [uniteVecC, uniteVec, uniteX, uniteY, g1, g2, gL, if_neg heq]
    · rw [wS, wkT]; simp [heq]
    · omega
    · omega
    · rw [pS]; exact tkT


-- The caller owns a writable root vector of `int` bound at its vector slot `vslot`.
structure VOKWI (caller : NState) (vslot vb V vsc : Nat) (vbuf : Buffer Value) : Prop where
  valid : caller.frame.state.wellFormed = true
  slot : caller.vectorSlot vslot = some vb
  binding : caller.frame.bindings[vb]? = some ⟨V,.integer i32,true,.root vsc⟩
  vtag : caller.frame.state.forest.lookup V = some ⟨.integer i32,none,some vsc,[]⟩
  vfound : caller.frame.state.storage.lookup V = some vbuf
  lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length
  flag : caller.frame.rootWritable[V]? = some true
  strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope
  base : caller.scalars.baseMemory ≤ caller.scalars.memory.length

theorem prepare_uu (caller : NState) {vslot vb V vsc : Nat} {vbuf : Buffer Value}
    (ok : VOKWI caller vslot vb V vsc vbuf) (e1 e2 : NExpr) (v1 v2 : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (hty1 : e1.resultType = i32) (hty2 : e2.resultType = i32)
    (value1 : e1.denote (envOf caller) = some v1) (value2 : e2.denote (envOf caller) = some v2)
    (hv1 : i32.valid v1 = true) (hv2 : i32.valid v2 = true) :
    ∃ t, Good (caller.charge 1 1) t (e1.nodes+e2.nodes) (max e1.nodes e2.nodes) ∧
      ∃ Sinit, prepare caller Proofs.UnionFindInstance.UnionFind_unite.parameters
          [.vectorReference vslot,.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.vector 0,.scalar 0,.scalar 1] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨i32,v1⟩,⟨i32,v2⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,true,.root vsc⟩]⟩ ∧
        Sinit.scalars.work = t.scalars.work+4 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc i32 true true vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (fun _ => rfl)
  have rvec : resolve caller (.vector i32 true) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc i32 true) := by
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
  have bound : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).bindRoot V (.integer i32) vsc true =
      some (⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,true,.root vsc⟩]⟩,0) := by
    have vobject : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).object V (.integer i32) =
        some (vbuf,⟨.integer i32,none,some vsc,[]⟩) :=
      object_runs _ V _ vbuf _ ok.valid ok.vfound ok.vtag rfl
    have vrooted : caller.frame.state.forest.rootOwner V = some V := CppVectorOwnership.root_runs _ V _ ok.vtag rfl
    have vmax : (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame).maximum V = some true :=
      maximum_runs _ V V true ok.lengths vrooted ok.flag
    simp only [Frame.bindRoot,vobject,vmax,Bind.bind,Option.bind]
    simp [Frame.addBinding]
  have hp : Proofs.UnionFindInstance.UnionFind_unite.parameters =
      [.vector i32 true,.scalar i32 false true,.scalar i32 false true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec,res1,res2]
  simp [fs,fr,fb,hmem,hbind,hbase,bound,bindAll,bindOne,CppState.bindArgument,hv1,hv2,callerP,
    NState.observe,CppState.State.observe]
  left
  have g := good.2.2.2.2.1
  simp [NState.charge,NState.observe,CppState.State.observe] at g
  omega


theorem uniteX_lt (ps : List Int) (r1 r2 : Nat) (h1 : r1 < ps.length) (h2 : r2 < ps.length) :
    uniteX ps r1 r2 < ps.length := by
  unfold uniteX; split <;> assumption

set_option maxHeartbeats 4000000 in
theorem uf_unite_correct (caller : NState) {vslot vb V vsc : Nat} {vbuf : Buffer Value}
    (ok : VOKWI caller vslot vb V vsc vbuf) (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank)
    (hitems : vbuf.items = ps.map Value.integer) (hn : ps.length < 2147483648)
    (hbvalid : vbuf.Valid (accepts (.integer i32))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit i32)
    (howner : vbuf.owner = V)
    (e1 e2 : NExpr) (a b : Nat) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = i32) (ht2 : e2.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (a : Int)) (value2 : e2.denote (envOf caller) = some (b : Int))
    (ha : a + 1 < ps.length) (hb : b + 1 < ps.length)
    (hnodes : ∀ (i : Nat) (p : Int), i + 1 < ps.length → ps[i]? = some p → 0 ≤ p → p.toNat + 1 < ps.length)
    (vL : Int) (hvL : ps[ps.length - 1]? = some vL) (hLn : i32.valid (vL + 1) = true)
    (hmin : ∀ x ∈ ps, i32.valid (0 - x) = true)
    (hsum : ∀ (i j : Nat) (x y : Int), i + 1 < ps.length → j + 1 < ps.length → ps[i]? = some x → ps[j]? = some y →
      x < 0 → y < 0 → i32.valid (x + y) = true) :
    ∃ Sinit fuel res, ∃ r1 r2 : Nat, prepare caller Proofs.UnionFindInstance.UnionFind_unite.parameters
        [.vectorReference vslot,.value e1,.value e2] = some Sinit ∧
      Proofs.UnionFindInstance.UnionFind_unite.callFuel fuel caller [.vectorReference vslot,.value e1,.value e2] =
        .finished (res,.scalar (uniteX ps r1 r2 : Int)) ∧
      Reach ps a r1 ∧ Reach ps b r2 ∧ r1 + 1 < ps.length ∧ (∃ v, ps[r1]? = some v ∧ v < 0) ∧
      r2 + 1 < ps.length ∧ (∃ v, ps[r2]? = some v ∧ v < 0) ∧
      ScalarPost3 caller Sinit res (e1.nodes+e2.nodes) (16 * rank a + 16 * rank b + 420) caller.scalars.memory
        (if r1 = r2 then 0 else 3) V (uniteVecC ps r1 r2) := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_uu caller ok e1 e2 (a : Int) (b : Int) hs1 hs2 ht1 ht2 value1 value2
      (i32_valid a (by omega) (by omega)) (i32_valid b (by omega) (by omega))
  let vc : VCtx := ⟨i32,true,true,V,vsc,vbuf,ps,hitems,fun _ => rfl,by omega,
    caller.frame.state.liveSpace,caller.frame.state.storage.work,caller.scope+1,
    caller.frame.state.storage.objects.length⟩
  have fwS : FW vc ps vbuf 0 Sinit.frame := by
    rw [sFrame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,hitems,hbvalid,hlimit,howner,by omega⟩
    intro owner k h
    have := ok.strict owner k h
    show k < caller.scope+1
    omega
  obtain ⟨rr,r1,r2,hexec,reach1,reach2,hr1,hroot1,hr2,hroot2,hret,hvec,hwk,hcost,hneed,htake⟩ :=
    body_exec_unite (callerP caller) ps rank hF hn a b ha hb (max (rank a) (rank b) + 2) (by omega) (by omega)
      hnodes vL hvL hLn hmin hsum
  have ea := env_loc (S0 (callerP caller) a b) 0 (callerP caller).length a
    (S0_loc0 _ _ _) (i32_valid a (by omega) (by omega))
  have eb := env_loc (S0 (callerP caller) a b) 1 ((callerP caller).length+1) b
    (S0_loc1 _ _ _) (i32_valid b (by omega) (by omega))
  have hexec' := UfBounds.prepend_bounds ea hn (by omega) (by omega)
    (UfBounds.prepend_bounds eb hn (by omega) (by omega) hexec)
  have hneed' : (UfBounds.bounded (S0 (callerP caller) a b) (UfBounds.bounded (S0 (callerP caller) a b) rr)).need ≤ (callerP caller).length+112 := by
    simp only [UfBounds.bounded,S0,List.length_append,List.length_cons,List.length_nil]
    omega
  have hcost' : (UfBounds.bounded (S0 (callerP caller) a b) (UfBounds.bounded (S0 (callerP caller) a b) rr)).cost ≤ 16 * rank a + 16 * rank b + 400 := by
    dsimp [UfBounds.bounded]; omega
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have gw1 := good.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hresv : i32.valid (uniteX ps r1 r2 : Int) = true :=
    i32_valid _ (by omega) (by have := uniteX_lt ps r1 r2 (by omega) (by omega); omega)
  have hpost := call_vecw vc true (fun _ => ⟨rfl,rfl⟩) caller Proofs.UnionFindInstance.UnionFind_unite
    [.vectorReference vslot,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨i32,(a : Int)⟩ : Cell),⟨i32,(b : Int)⟩])
    [(⟨(callerP caller).length,true⟩ : CppState.Binding),⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [UfRootCall.take_P caller]) ok.base (by decide)
    (max (rank a) (rank b) + 2) (UfBounds.bounded (S0 (callerP caller) a b) (UfBounds.bounded (S0 (callerP caller) a b) rr))
    (by rw [body_eqU]; exact hexec') _ hret i32 rfl hresv hneed' (by simp) (e1.nodes+e2.nodes)
    (16 * rank a + 16 * rank b + 420) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  dsimp only [UfBounds.bounded,UfBounds.charged] at post
  refine ⟨Sinit,fuel,res,r1,r2,hprep,hrun,reach1,reach2,hr1,hroot1,hr2,hroot2,?_⟩
  have hle : caller.scalars.memory.length ≤ (callerP caller).length := by omega
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    calc rr.ps.mem.take caller.scalars.memory.length
        = (rr.ps.mem.take (callerP caller).length).take caller.scalars.memory.length := by
          rw [List.take_take, Nat.min_eq_left hle]
      _ = (callerP caller).take caller.scalars.memory.length := by rw [htake]
      _ = caller.scalars.memory := by simp only [callerP]; exact List.take_left' rfl
  rw [hs', hvec, hwk] at post
  exact post


-- Linking the root `Y` below the root `X` (and storing the new size at `X`) keeps the forest condition: the nodes
-- of the tree of `Y` get a larger rank than every node of the tree of `X`.
theorem link_forest (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank) (X Y : Nat) (sz : Int)
    (hXl : X < ps.length) (hYl : Y < ps.length) (hX : ∃ v, ps[X]? = some v ∧ v < 0)
    (hY : ∃ v, ps[Y]? = some v ∧ v < 0) (hne : X ≠ Y) (hsz : sz < 0) (hszv : i32.valid sz = true)
    (hn : ps.length < 2147483648) :
    ∃ rank' : Nat → Nat, Forest ((ps.set X sz).set Y (X : Int)) rank' := by
  classical
  have hXv : i32.valid (X : Int) = true := i32_valid X (by omega) (by omega)
  refine ⟨fun i => if Reach ps i Y then rank i + rank X + 1 else rank i, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_or_eq_of_mem_set hx with h | h
    · rcases List.mem_or_eq_of_mem_set h with h' | h'
      · exact hF.valid x h'
      · rw [h']; exact hszv
    · rw [h]; exact hXv
  · intro i p hi h0
    by_cases hiY : i = Y
    · subst hiY
      rw [List.getElem?_set_self (by simp; omega)] at hi
      have := Option.some.inj hi; subst this
      simp; omega
    · rw [List.getElem?_set_ne (Ne.symm hiY)] at hi
      by_cases hiX : i = X
      · subst hiX
        rw [List.getElem?_set_self hXl] at hi
        have := Option.some.inj hi; subst this
        omega
      · rw [List.getElem?_set_ne (Ne.symm hiX)] at hi
        have := hF.inside i p hi h0
        simpa using this
  · intro i p hi h0
    by_cases hiY : i = Y
    · subst hiY
      rw [List.getElem?_set_self (by simp; omega)] at hi
      have := Option.some.inj hi; subst this
      have hXY : ¬ Reach ps X i := by
        intro h
        obtain ⟨w, hw, hneg⟩ := hX
        exact hne (root_reach ps X ⟨w, hw, hneg⟩ i h).symm
      simp only [Int.toNat_natCast, if_pos (Reach.refl i), if_neg hXY]
      omega
    · rw [List.getElem?_set_ne (Ne.symm hiY)] at hi
      by_cases hiX : i = X
      · subst hiX
        rw [List.getElem?_set_self hXl] at hi
        have := Option.some.inj hi; subst this
        omega
      · rw [List.getElem?_set_ne (Ne.symm hiX)] at hi
        have hd := hF.decrease i p hi h0
        have hpar : ps[i]? = some ((p.toNat : Nat) : Int) := by rw [Int.toNat_of_nonneg h0]; exact hi
        by_cases hr : Reach ps i Y
        · have hp : Reach ps p.toNat Y := by
            cases hr with
            | refl => exact absurd rfl hiY
            | step _ b' _ hp' hr' =>
              have e : ps[i]? = some (b' : Int) := hp'
              rw [hpar] at e
              have := Option.some.inj e
              have : p.toNat = b' := by omega
              rw [this]; exact hr'
          rw [if_pos hr, if_pos hp]; omega
        · have hp : ¬ Reach ps p.toNat Y := by
            intro h
            exact hr (Reach.step i p.toNat Y hpar h)
          rw [if_neg hr, if_neg hp]; exact hd


-- The forest after `uf_unite` is again a forest (for some rank function).
theorem uniteVec_forest (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank) (r1 r2 : Nat)
    (hr1 : r1 < ps.length) (hr2 : r2 < ps.length) (hroot1 : ∃ v, ps[r1]? = some v ∧ v < 0)
    (hroot2 : ∃ v, ps[r2]? = some v ∧ v < 0) (hn : ps.length < 2147483648)
    (hsum : ∀ x y : Int, ps[r1]? = some x → ps[r2]? = some y → x < 0 → y < 0 → i32.valid (x + y) = true) :
    ∃ rank' : Nat → Nat, Forest (uniteVec ps r1 r2) rank' := by
  by_cases heq : r1 = r2
  · exact ⟨rank, by simpa [uniteVec, heq] using hF⟩
  · obtain ⟨v1, hv1, n1⟩ := hroot1
    obtain ⟨v2, hv2, n2⟩ := hroot2
    have m1 := List.mem_of_getElem? hv1
    have m2 := List.mem_of_getElem? hv2
    have g1 := getD_of ps r1 v1 hv1
    have g2 := getD_of ps r2 v2 hv2
    have hs := hsum v1 v2 hv1 hv2 n1 n2
    unfold uniteVec uniteX uniteY
    rw [if_neg heq, g1, g2]
    by_cases hlt : 0 - v1 < 0 - v2
    · rw [if_pos hlt, if_pos hlt]
      exact link_forest ps rank hF r2 r1 (v1 + v2) hr2 hr1 ⟨v2, hv2, n2⟩ ⟨v1, hv1, n1⟩ (Ne.symm heq)
        (by omega) hs hn
    · rw [if_neg hlt, if_neg hlt]
      exact link_forest ps rank hF r1 r2 (v1 + v2) hr1 hr2 ⟨v1, hv1, n1⟩ ⟨v2, hv2, n2⟩ heq
        (by omega) hs hn


-- Changing the value of a root to another negative value keeps the forest condition (same rank).
theorem forest_set_root (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank) (i : Nat) (w : Int) (hw : w < 0)
    (hwv : i32.valid w = true) : Forest (ps.set i w) rank := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_or_eq_of_mem_set hx with h | h
    · exact hF.valid x h
    · rw [h]; exact hwv
  · intro j p hj h0
    by_cases hji : j = i
    · subst hji
      by_cases hl : j < ps.length
      · rw [List.getElem?_set_self hl] at hj
        have := Option.some.inj hj; subst this; omega
      · have hnone : (ps.set j w)[j]? = none := by rw [List.getElem?_eq_none]; simp; omega
        rw [hnone] at hj; simp at hj
    · rw [List.getElem?_set_ne (Ne.symm hji)] at hj
      have := hF.inside j p hj h0
      simpa using this
  · intro j p hj h0
    by_cases hji : j = i
    · subst hji
      by_cases hl : j < ps.length
      · rw [List.getElem?_set_self hl] at hj
        have := Option.some.inj hj; subst this; omega
      · have hnone : (ps.set j w)[j]? = none := by rw [List.getElem?_eq_none]; simp; omega
        rw [hnone] at hj; simp at hj
    · rw [List.getElem?_set_ne (Ne.symm hji)] at hj
      exact hF.decrease j p hj h0

-- The forest after `UnionFind::unite` is again a forest (for some rank function), provided the tree count stays negative.
theorem uniteVecC_forest (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank) (r1 r2 : Nat)
    (hr1 : r1 < ps.length) (hr2 : r2 < ps.length) (hroot1 : ∃ v, ps[r1]? = some v ∧ v < 0)
    (hroot2 : ∃ v, ps[r2]? = some v ∧ v < 0) (hn : ps.length < 2147483648)
    (hsum : ∀ x y : Int, ps[r1]? = some x → ps[r2]? = some y → x < 0 → y < 0 → i32.valid (x + y) = true)
    (vL : Int) (hvL : ps[ps.length - 1]? = some vL) (hLneg : vL + 1 < 0) (hLn : i32.valid (vL + 1) = true)
    (hL1 : r1 ≠ ps.length - 1) (hL2 : r2 ≠ ps.length - 1) :
    ∃ rank' : Nat → Nat, Forest (uniteVecC ps r1 r2) rank' := by
  by_cases heq : r1 = r2
  · exact ⟨rank, by simpa [uniteVecC, heq] using hF⟩
  · obtain ⟨rank', hF'⟩ := uniteVec_forest ps rank hF r1 r2 hr1 hr2 hroot1 hroot2 hn hsum
    have gL : ps.getD (ps.length - 1) 0 = vL := getD_of ps _ vL hvL
    unfold uniteVecC
    rw [if_neg heq, gL]
    exact ⟨rank', forest_set_root _ rank' hF' (ps.length - 1) (vL + 1) hLneg hLn⟩

end Proofs.UfUniteCall
