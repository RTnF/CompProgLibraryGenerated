import Proofs.UfBounds
import Proofs.Generated.UnionFind

namespace Proofs.UfRootCall
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

abbrev rdA : NExpr := .read i32 (.local 0) (.cast u64 (.variable i32 1))
abbrev condU : NExpr := .binary bT .ge rdA (.literal i32 0)
abbrev assignU : NStmt := .assign 1 i32 rdA
abbrev loopBodyU : Command := .sequence (.scope (.sequence (.primitive assignU) (.primitive .skip))) (.primitive .skip)
abbrev loopCU : Command := .whileLoop condU loopBodyU
abbrev bodyCmdU : Command := .sequence loopCU (.sequence (.primitive (.ret (.variable i32 1))) (.primitive .skip))

theorem body_eqU : Proofs.UnionFindInstance.UnionFind_find_root.body = bodyCmdU := rfl

theorem vwp_rdA : vwp rdA = (5,5) := by decide
theorem vwp_varI : vwp (NExpr.variable i32 1) = (1,1) := by decide
theorem vwp_condU : vwp condU = (7,7) := by decide

-- The parent links of the forest `ps` and a rank that strictly decreases along them.
def Parent (ps : List Int) (i j : Nat) : Prop := ps[i]? = some (j : Int)

structure Forest (ps : List Int) (rank : Nat → Nat) : Prop where
  valid : ∀ x ∈ ps, i32.valid x = true
  inside : ∀ (i : Nat) (p : Int), ps[i]? = some p → 0 ≤ p → p < ps.length
  decrease : ∀ (i : Nat) (p : Int), ps[i]? = some p → 0 ≤ p → rank p.toNat < rank i

theorem cond_valU (ps : List Int) (P : List Cell) (a : Nat) (x : Int) (hn : ps.length < 2147483648)
    (ha : a < ps.length) (hx : ps[a]? = some x) (hxv : i32.valid x = true) :
    vdenL i32 ps (penv1 (stI P a)) condU = some (if 0 ≤ x then 1 else 0) := by
  have hb : condU.scalarOnly = false := rfl
  have hrd : rdA.scalarOnly = false := rfl
  have vcur : vdenL i32 ps (penv1 (stI P a)) rdA = some x := by
    rw [vdenL_read _ _ _ _ _ hrd, if_pos ⟨rfl, rfl⟩, idxcur ps P a (by omega), Option.bind_some]
    simp [elemAtL, hx, hxv]
  have hl : vdenL i32 ps (penv1 (stI P a)) (NExpr.literal i32 0) = some 0 := by
    rw [vdenL_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 0 = true from rfl)]
  rw [vdenL_binary _ _ _ _ _ _ _ hb, vcur, hl, Option.bind_some, Option.bind_some]
  have : binaryValue .ge x 0 = if 0 ≤ x then 1 else 0 := by
    show (if x ≥ 0 then 1 else 0) = _
    by_cases h : 0 ≤ x <;> simp [h]
  rw [this]
  simp only [bT]; unfold Ty.convert
  by_cases h : 0 ≤ x <;> simp [h]

theorem rdA_valU (ps : List Int) (P : List Cell) (a : Nat) (x : Int) (hn : ps.length < 2147483648)
    (ha : a < ps.length) (hx : ps[a]? = some x) (hxv : i32.valid x = true) :
    vdenL i32 ps (penv1 (stI P a)) rdA = some x := by
  have hrd : rdA.scalarOnly = false := rfl
  rw [vdenL_read _ _ _ _ _ hrd, if_pos ⟨rfl, rfl⟩, idxcur ps P a (by omega), Option.bind_some]
  simp [elemAtL, hx, hxv]

theorem iterU (P : List Cell) (ps : List Int) (a : Nat) (x : Int) (hn : ps.length < 2147483648) (ha : a < ps.length)
    (hx : ps[a]? = some x) (hxv : i32.valid x = true) (hx0 : 0 ≤ x) (hxl : x < ps.length) (fu : Nat) :
    ∃ r1, pexecW i32 fu loopBodyU (stI P a) ps = some r1 ∧ r1.ps = stI P x ∧ r1.vec = ps ∧ r1.ret = none ∧
      r1.cost ≤ 8 ∧ r1.need ≤ P.length + 20 ∧ r1.wk = 0 := by
  have hval := rdA_valU ps P a x hn ha hx hxv
  have bI : (stI P a).bs[0]? = some ⟨P.length,true⟩ := by simp [stI]
  have cI : (stI P a).mem[P.length]? = some ⟨i32,a⟩ := by
    have := Proofs.ModIntExec.get_tail P [⟨i32,a⟩] 0
    simpa [stI] using this
  have st := pstmtW_assign_ok i32 (stI P a) ps 0 i32 rdA x hval ⟨P.length,true⟩ ⟨i32,a⟩ bI cI rfl
    (show i32.valid (a : Int) = true from i32_valid _ (by omega) (by omega)) rfl x (conv_signed i32 rfl rfl _ hxv)
  rw [set_i1] at st
  have a1 := (pexecW_prim i32 fu assignU _ _).trans st
  have a2 := seqW_some a1 rfl (pexecW_skip i32 fu (stI P x) ps)
  have a3 := pexecW_scope i32 fu _ _ _ _ a2
  have a4 := Proofs.PexecKit.scope_take (stI P a) (stI P x) (by simp [stI]) (by simp [stI])
  simp only [a4] at a3
  have a5 := seqW_some a3 rfl (pexecW_skip i32 fu (stI P x) ps)
  refine ⟨_, a5, rfl, rfl, rfl, ?_, ?_, rfl⟩
  · simp [vwp_rdA]
  · simp [vwp_rdA, stI, NExpr.nodes, Container.nodes]

-- Following parent links from `a` reaches `r`.
inductive Reach (ps : List Int) : Nat → Nat → Prop where
  | refl (a : Nat) : Reach ps a a
  | step (a b c : Nat) : Parent ps a b → Reach ps b c → Reach ps a c

theorem loop_runU (P : List Cell) (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank)
    (hn : ps.length < 2147483648) :
    ∀ (m a : Nat), a < ps.length → rank a ≤ m → ∀ fu, m + 2 ≤ fu →
      ∃ (res : PRW) (r : Nat), pexecW i32 fu loopCU (stI P a) ps = some res ∧ res.ps = stI P r ∧ res.vec = ps ∧
        res.ret = none ∧ Reach ps a r ∧ r < ps.length ∧ (∃ v, ps[r]? = some v ∧ v < 0) ∧
        res.cost ≤ 16 * m + 8 ∧ res.need ≤ P.length + 20 ∧ res.wk = 0 := by
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
    have hc := cond_valU ps P a x hn ha hx hxv
    rw [if_neg (by omega)] at hc
    rw [pexecW_while, hc]
    simp only [Bind.bind, Option.bind, ite_true, vwp_condU]
    refine ⟨_, a, rfl, rfl, rfl, rfl, Reach.refl a, ha, ⟨x, hx, hneg⟩, ?_, ?_, rfl⟩
    · simp
    · simp [stI]
  | succ m ih =>
    intro a ha hr fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    obtain ⟨x, hx⟩ : ∃ x, ps[a]? = some x := ⟨ps[a], by simp [ha]⟩
    have hxv := hF.valid x (List.mem_of_getElem? hx)
    have hc := cond_valU ps P a x hn ha hx hxv
    by_cases hx0 : 0 ≤ x
    · rw [if_pos hx0] at hc
      have hxl := hF.inside a x hx hx0
      have hdec := hF.decrease a x hx hx0
      obtain ⟨r1, h1, p1, v1, ret1, c1, n1, w1⟩ := iterU P ps a x hn ha hx hxv hx0 hxl (fu'+1)
      obtain ⟨r2, r, h2, p2, v2, ret2, hreach, hrl, hroot, c2, n2, w2⟩ :=
        ih x.toNat (by omega) (by omega) fu' (by omega)
      have hxn : ((x.toNat : Nat) : Int) = x := Int.toNat_of_nonneg hx0
      have p1' : r1.ps = stI P ((x.toNat : Nat) : Int) := by rw [p1, hxn]
      rw [pexecW_while, hc]
      simp only [Bind.bind, Option.bind, h1, ret1, p1', v1, h2, vwp_condU]
      refine ⟨⟨r2.ps, r2.vec, r2.ret, 7+1+r1.cost+r2.cost, max ((stI P a).mem.length +
        (stI P a).bs.length + 7 + 2) (max r1.need r2.need), r1.wk+r2.wk⟩, r, by simp, p2, v2, ret2,
        Reach.step a x.toNat r (by simp [Parent, hxn, hx]) hreach, hrl, hroot, ?_, ?_, ?_⟩
      · simp; omega
      · simp [stI_size, n1, n2]
      · simp [w1, w2]
    · rw [if_neg hx0] at hc
      rw [pexecW_while, hc]
      simp only [Bind.bind, Option.bind, ite_true, vwp_condU]
      refine ⟨_, a, rfl, rfl, rfl, rfl, Reach.refl a, ha, ⟨x, hx, by omega⟩, ?_, ?_, rfl⟩
      · simp
      · simp [stI]

theorem body_execU (P : List Cell) (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank)
    (hn : ps.length < 2147483648) (a : Nat) (ha : a < ps.length) (fu : Nat) (hfu : rank a + 2 ≤ fu) :
    ∃ (res : PRW) (r : Nat), pexecW i32 fu bodyCmdU (stI P a) ps = some res ∧ res.ret = some (r : Int) ∧
      res.ps = stI P r ∧ res.vec = ps ∧ Reach ps a r ∧ r < ps.length ∧ (∃ v, ps[r]? = some v ∧ v < 0) ∧
      res.cost ≤ 16 * rank a + 18 ∧ res.need ≤ P.length + 20 ∧ res.wk = 0 := by
  obtain ⟨rL, r, hL, pL, vL, retL, hreach, hrl, hroot, cL, nL, wL⟩ :=
    loop_runU P ps rank hF hn (rank a) a ha (le_refl _) fu hfu
  have hret : vdenL i32 rL.vec (penv1 (stI P r)) (NExpr.variable i32 1) = some (r : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl, den_variable]
    exact env_i1 P r (i32_valid r (by omega) (by omega))
  have g1 := pstmtW_ret_ok i32 (stI P r) rL.vec (NExpr.variable i32 1) (r : Int) hret
  have g2 := (pexecW_prim i32 fu (.ret (.variable i32 1)) _ _).trans g1
  have g3 := seqW_ret (b := .primitive .skip) g2 rfl
  rw [← pL] at g3
  have h4 := seqW_some hL retL g3
  have hsz : rL.ps.mem.length + rL.ps.bs.length = P.length + 2 := by rw [pL]; simp [stI]
  refine ⟨_, r, h4, rfl, ?_, ?_, hreach, hrl, hroot, ?_, ?_, ?_⟩
  · simp [pL]
  · simp [vL]
  · simp [vwp_varI]
    omega
  · simp [vwp_varI]
    omega
  · simp [wL]


abbrev negE : NExpr := .binary i32 .sub (.literal i32 0) rdA
abbrev bodyCmdS : Command := .sequence loopCU (.sequence (.primitive (.ret negE)) (.primitive .skip))

theorem body_eqS : Proofs.UnionFindInstance.UnionFind_size.body = UfBounds.bounds 1 bodyCmdS := rfl

theorem vwp_negE : vwp negE = (7,7) := by decide

theorem neg_valS (ps : List Int) (P : List Cell) (r : Nat) (x : Int) (hn : ps.length < 2147483648)
    (hr : r < ps.length) (hx : ps[r]? = some x) (hxv : i32.valid x = true) (hneg : i32.valid (0 - x) = true) :
    vdenL i32 ps (penv1 (stI P r)) negE = some (0 - x) := by
  have hb : negE.scalarOnly = false := rfl
  have hl : vdenL i32 ps (penv1 (stI P r)) (NExpr.literal i32 0) = some 0 := by
    rw [vdenL_scalar _ _ _ _ rfl, den_literal, if_pos (show i32.valid 0 = true from rfl)]
  rw [vdenL_binary _ _ _ _ _ _ _ hb, hl, rdA_valU ps P r x hn hr hx hxv, Option.bind_some, Option.bind_some]
  have : binaryValue .sub 0 x = 0 - x := rfl
  rw [this]
  exact conv_signed i32 rfl rfl _ hneg

theorem body_execS (P : List Cell) (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank)
    (hn : ps.length < 2147483648) (a : Nat) (ha : a < ps.length) (fu : Nat) (hfu : rank a + 2 ≤ fu)
    (hmin : ∀ x ∈ ps, i32.valid (0 - x) = true) :
    ∃ (res : PRW) (r : Nat) (v : Int), pexecW i32 fu bodyCmdS (stI P a) ps = some res ∧ res.ret = some (0 - v) ∧
      res.ps = stI P r ∧ res.vec = ps ∧ Reach ps a r ∧ r < ps.length ∧ ps[r]? = some v ∧ v < 0 ∧
      res.cost ≤ 16 * rank a + 24 ∧ res.need ≤ P.length + 20 ∧ res.wk = 0 := by
  obtain ⟨rL, r, hL, pL, vL, retL, hreach, hrl, ⟨v, hv, hvneg⟩, cL, nL, wL⟩ :=
    loop_runU P ps rank hF hn (rank a) a ha (le_refl _) fu hfu
  have hvv := hF.valid v (List.mem_of_getElem? hv)
  have hret : vdenL i32 rL.vec (penv1 (stI P r)) negE = some (0 - v) := by
    rw [vL]; exact neg_valS ps P r v hn hrl hv hvv (hmin v (List.mem_of_getElem? hv))
  have g1 := pstmtW_ret_ok i32 (stI P r) rL.vec negE (0 - v) hret
  have g2 := (pexecW_prim i32 fu (.ret negE) _ _).trans g1
  have g3 := seqW_ret (b := .primitive .skip) g2 rfl
  rw [← pL] at g3
  have h4 := seqW_some hL retL g3
  have hsz : rL.ps.mem.length + rL.ps.bs.length = P.length + 2 := by rw [pL]; simp [stI]
  refine ⟨_, r, v, h4, rfl, ?_, ?_, hreach, hrl, hv, hvneg, ?_, ?_, ?_⟩
  · simp [pL]
  · simp [vL]
  · simp [vwp_negE]
    omega
  · simp [vwp_negE]
    omega
  · simp [wL]

-- The caller owns a root vector of `int` bound at its vector slot `vslot`.
structure VOKI (caller : NState) (vslot vb V vsc : Nat) (m : Bool) (vbuf : Buffer Value) : Prop where
  valid : caller.frame.state.wellFormed = true
  slot : caller.vectorSlot vslot = some vb
  binding : caller.frame.bindings[vb]? = some ⟨V,.integer i32,false,.root vsc⟩
  vtag : caller.frame.state.forest.lookup V = some ⟨.integer i32,none,some vsc,[]⟩
  vfound : caller.frame.state.storage.lookup V = some vbuf
  lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length
  flag : caller.frame.rootWritable[V]? = some m
  strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope
  base : caller.scalars.baseMemory ≤ caller.scalars.memory.length

theorem prepare_ur (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : VOKI caller vslot vb V vsc m vbuf) (e : NExpr) (v : Int) (hs : e.scalarOnly = true)
    (hty : e.resultType = i32) (value : e.denote (envOf caller) = some v) (hv : i32.valid v = true) :
    ∃ t, Good (caller.charge 1 1) t e.nodes e.nodes ∧
      ∃ Sinit, prepare caller Proofs.UnionFindInstance.UnionFind_find_root.parameters [.vectorReference vslot,.value e] = some Sinit ∧
        Sinit.slots = [.vector 0,.scalar 0] ∧ Sinit.scalars.memory = callerP caller ++ [⟨i32,v⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,false,.root vsc⟩]⟩ ∧
        Sinit.scalars.work = t.scalars.work+3 ∧ t.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc i32 false m vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (by simp)
  have rvec : resolve caller (.vector i32 false) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc i32 false) := by
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
  have hp : Proofs.UnionFindInstance.UnionFind_find_root.parameters = [.vector i32 false,.scalar i32 false true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec,res]
  simp [fs,fr,fb,hmem,hbind,hbase,bound,bindAll,bindOne,CppState.bindArgument,hv,callerP,
    NState.observe,CppState.State.observe]
  left
  have g := good.2.2.2.2.1
  simp [NState.charge,NState.observe,CppState.State.observe] at g
  omega

theorem take_P (caller : NState) (L : List Cell) :
    (callerP caller ++ L).take caller.scalars.memory.length = caller.scalars.memory := by
  have : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  have hl : caller.scalars.memory.length ≤ (callerP caller).length := by simp [callerP]
  rw [List.take_append_of_le_length hl]; exact this

set_option maxHeartbeats 4000000 in
theorem uf_root_correct (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : VOKI caller vslot vb V vsc m vbuf) (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank)
    (hitems : vbuf.items = ps.map Value.integer) (hn : ps.length < 2147483648)
    (hbvalid : vbuf.Valid (accepts (.integer i32))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit i32)
    (howner : vbuf.owner = V)
    (e : NExpr) (a : Nat) (hs : e.scalarOnly = true) (ht : e.resultType = i32)
    (value : e.denote (envOf caller) = some (a : Int)) (ha : a < ps.length) :
    ∃ Sinit fuel res, ∃ r : Nat, prepare caller Proofs.UnionFindInstance.UnionFind_find_root.parameters
        [.vectorReference vslot,.value e] = some Sinit ∧
      Proofs.UnionFindInstance.UnionFind_find_root.callFuel fuel caller [.vectorReference vslot,.value e] =
        .finished (res,.scalar (r : Int)) ∧
      Reach ps a r ∧ r < ps.length ∧ (∃ v, ps[r]? = some v ∧ v < 0) ∧
      ScalarPost3 caller Sinit res e.nodes (16 * rank a + 60) caller.scalars.memory 0 V ps := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_ur caller ok e (a : Int) hs ht value (i32_valid a (by omega) (by omega))
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
  obtain ⟨rr,r,hexec,hret,hrps,hrvec,hreach,hrl,hroot,hcost,hneed,hwk⟩ :=
    body_execU (callerP caller) ps rank hF hn a ha (rank a + 2) (le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(a : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := take_P caller _
  have gw1 := good.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hres : i32.valid (r : Int) = true := i32_valid r (by omega) (by omega)
  have hpost := call_vecw vc false (fun h => absurd h (by decide)) caller Proofs.UnionFindInstance.UnionFind_find_root
    [.vectorReference vslot,.value e] Sinit
    (callerP caller ++ [(⟨i32,(a : Int)⟩ : Cell)]) [(⟨(callerP caller).length,true⟩ : CppState.Binding)]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok.base (by decide) (rank a + 2) rr
    (by rw [body_eqU]; exact hexec) (r : Int) hret i32 rfl hres (by omega) (by simp) e.nodes
    (16 * rank a + 60) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,r,hprep,hrun,hreach,hrl,hroot,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [stI]
    exact take_P caller _
  rw [hs', hrvec, hwk] at post
  exact post


theorem uf_size_correct (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : VOKI caller vslot vb V vsc m vbuf) (ps : List Int) (rank : Nat → Nat) (hF : Forest ps rank)
    (hitems : vbuf.items = ps.map Value.integer) (hn : ps.length < 2147483648)
    (hbvalid : vbuf.Valid (accepts (.integer i32))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit i32)
    (howner : vbuf.owner = V)
    (e : NExpr) (a : Nat) (hs : e.scalarOnly = true) (ht : e.resultType = i32)
    (value : e.denote (envOf caller) = some (a : Int)) (ha : a + 1 < ps.length)
    (hmin : ∀ x ∈ ps, i32.valid (0 - x) = true) :
    ∃ Sinit fuel res, ∃ r : Nat, ∃ v : Int, prepare caller Proofs.UnionFindInstance.UnionFind_size.parameters
        [.vectorReference vslot,.value e] = some Sinit ∧
      Proofs.UnionFindInstance.UnionFind_size.callFuel fuel caller [.vectorReference vslot,.value e] =
        .finished (res,.scalar (0 - v)) ∧
      Reach ps a r ∧ r < ps.length ∧ ps[r]? = some v ∧ v < 0 ∧
      ScalarPost3 caller Sinit res e.nodes (16 * rank a + 100) caller.scalars.memory 0 V ps := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_ur caller ok e (a : Int) hs ht value (i32_valid a (by omega) (by omega))
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
  obtain ⟨rr,r,v,hexec,hret,hrps,hrvec,hreach,hrl,hroot,hvneg,hcost,hneed,hwk⟩ :=
    body_execS (callerP caller) ps rank hF hn a (by omega) (rank a + 2) (le_refl _) hmin
  have hexec' := UfBounds.prepend_bounds (j := 1) (a := (a : Int))
    (env_i1 (callerP caller) a (i32_valid a (by omega) (by omega))) hn (by omega) (by omega) hexec
  have hneed' : (UfBounds.bounded (stI (callerP caller) a) rr).need ≤ (callerP caller).length+112 := by
    simp only [UfBounds.bounded,stI,List.length_append,List.length_cons,List.length_nil]
    omega
  have hcost' : (UfBounds.bounded (stI (callerP caller) a) rr).cost ≤ 16 * rank a + 80 := by
    dsimp [UfBounds.bounded]; omega
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(a : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := take_P caller _
  have gw1 := good.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hres : i32.valid (0 - v) = true := hmin v (List.mem_of_getElem? hroot)
  have hpost := call_vecw vc false (fun h => absurd h (by decide)) caller Proofs.UnionFindInstance.UnionFind_size
    [.vectorReference vslot,.value e] Sinit
    (callerP caller ++ [(⟨i32,(a : Int)⟩ : Cell)]) [(⟨(callerP caller).length,true⟩ : CppState.Binding)]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok.base (by decide) (rank a + 2) (UfBounds.bounded (stI (callerP caller) a) rr)
    (by rw [body_eqS]; exact hexec') (0 - v) hret i32 rfl hres hneed' (by simp) e.nodes
    (16 * rank a + 100) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  dsimp only [UfBounds.bounded,UfBounds.charged] at post
  refine ⟨Sinit,fuel,res,r,v,hprep,hrun,hreach,hrl,hroot,hvneg,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [stI]
    exact take_P caller _
  rw [hs', hrvec, hwk] at post
  exact post

end Proofs.UfRootCall
