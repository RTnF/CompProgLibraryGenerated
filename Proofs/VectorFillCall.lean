import Proofs.VectorSumCall
import Proofs.VecKitW
import Proofs.Generated.VectorFill

namespace Proofs.VectorFillCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.VecStraight Proofs.VecCall Proofs.VecKit
open Proofs.CppNestedFacts Proofs.IntSim Proofs.ScalarCall Proofs.VecWrite Proofs.VecWriteCall Proofs.VecKitW
open Proofs.QuotientSearch
open Proofs.VectorSumCall (stS env_s env_i i32_valid conv_signed stS_size set_s set_i inc_val vwp_cond vwp_inc vwp_lit2)
open Proofs.CppState (Cell)

-- A dummy context carrying only the element type and contents: `vden` of it is `vdenL`.
def dummyCtx (ty : Ty) (vec : List Int) (small : vec.length < 18446744073709551616) : VCtx :=
  ⟨ty,true,true,0,0,⟨0,vec.map Value.integer,0,0,0⟩,vec,rfl,fun _ => rfl,small,0,0,0,0⟩

theorem vdenL_scalar (ty : Ty) (vec : List Int) (env : Nat → Ty → Option Int) (e : NExpr) (h : e.scalarOnly = true) :
    vdenL ty vec env e = e.denote env := by
  unfold vdenL; simp [h]

theorem cond_valL (ty : Ty) (vec : List Int) (hty : ty = s64) (P : List Cell) (s i : Int)
    (hn : vec.length < 2147483648) (h0 : 0 ≤ i) (h1 : i ≤ vec.length) :
    vdenL ty vec (penv1 (stS P s i)) Proofs.VectorSumCall.condE = some (if i < (vec.length : Int) then 1 else 0) := by
  have small : vec.length < 18446744073709551616 := by omega
  have := Proofs.VectorSumCall.cond_val (dummyCtx ty vec small) hty P s i hn h0 h1
  rw [vden_eq] at this
  exact this

abbrev writeS : NStmt := .write (.local 0) s64 (.cast u64 (.variable i32 2)) (.variable s64 1)
abbrev loopBodyF : Command := .sequence (.scope (.sequence (.primitive writeS) (.primitive .skip)))
  (.sequence (.primitive Proofs.VectorSumCall.assignI) (.primitive .skip))
abbrev loopCF : Command := .whileLoop Proofs.VectorSumCall.condE loopBodyF
abbrev bodyCmdF : Command := .sequence (.scope (.sequence (.primitive Proofs.VectorSumCall.declI)
  (.sequence loopCF (.primitive .skip)))) (.primitive .skip)

theorem body_eq : Proofs.VectorFillInstance.vector_fill_std_vector_long_long.body = bodyCmdF := rfl

def fillv (vec : List Int) (val : Int) (i : Nat) : List Int := List.replicate i val ++ vec.drop i

theorem fillv_length (vec : List Int) (val : Int) (i : Nat) (hi : i ≤ vec.length) : (fillv vec val i).length = vec.length := by
  simp [fillv]; omega

theorem fillv_set (vec : List Int) (val : Int) (i : Nat) (hi : i < vec.length) :
    (fillv vec val i).set i val = fillv vec val (i+1) := by
  have hd : vec.drop i = vec[i] :: vec.drop (i+1) := List.drop_eq_getElem_cons hi
  have h1 : (List.replicate i val ++ vec.drop i).set i val = List.replicate i val ++ (vec.drop i).set 0 val := by
    have := List.set_append_right (s := List.replicate i val) (t := vec.drop i) i val (by simp)
    simpa using this
  unfold fillv
  rw [h1, hd, List.set_cons_zero]
  simp [List.replicate_succ']

theorem vwp_idx : vwp (NExpr.cast u64 (.variable i32 2)) = (2,2) := by decide
theorem vwp_val : vwp (NExpr.variable s64 1) = (1,1) := by decide

theorem iterF (P : List Cell) (val : Int) (i : Nat) (vec : List Int) (hn : vec.length < 2147483648)
    (hi : i < vec.length) (hv : s64.valid val = true) (fu : Nat) :
    ∃ r1, pexecW s64 fu loopBodyF (stS P val i) (fillv vec val i) = some r1 ∧ r1.ps = stS P val (i+1) ∧
      r1.vec = fillv vec val (i+1) ∧ r1.ret = none ∧ r1.cost ≤ 12 ∧ r1.need ≤ P.length + 16 ∧ r1.wk = 1 := by
  have e1 := env_s P val i hv
  have e2 := env_i P val i (i32_valid i (by omega) (by omega))
  have hlen := fillv_length vec val i (by omega)
  have hx : vdenL s64 (fillv vec val i) (penv1 (stS P val i)) (NExpr.variable s64 1) = some val := by
    rw [vdenL_scalar _ _ _ _ rfl, den_variable]; exact e1
  have hp : vdenL s64 (fillv vec val i) (penv1 (stS P val i)) (NExpr.cast u64 (.variable i32 2)) = some (i : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl, den_cast]
    show ((penv1 (stS P val i)) 2 i32).bind u64.convert = _
    rw [e2, Option.bind_some, convert_u64]
    simp
    exact Int.emod_eq_of_lt (by omega) (by omega)
  have w := pstmtW_write_ok s64 (stS P val i) (fillv vec val i) (NExpr.cast u64 (.variable i32 2)) (NExpr.variable s64 1)
    val i hx hp (by omega) hv
  rw [fillv_set vec val i hi] at w
  have a1 := (pexecW_prim s64 fu writeS _ _).trans w
  have a2 := seqW_some a1 rfl (pexecW_skip s64 fu (stS P val i) (fillv vec val (i+1)))
  have a3 := pexecW_scope s64 fu _ _ _ _ a2
  have a4 := Proofs.PexecKit.scope_take (stS P val i) (stS P val i) rfl rfl
  simp only [a4] at a3
  have hinc : vdenL s64 (fillv vec val (i+1)) (penv1 (stS P val i)) Proofs.VectorSumCall.incE = some ((i : Int)+1) := by
    have small : (fillv vec val (i+1)).length < 18446744073709551616 := by
      have : (fillv vec val (i+1)).length ≤ vec.length := by simp [fillv]; omega
      omega
    have := inc_val (dummyCtx s64 (fillv vec val (i+1)) small) P val i (by omega)
    rw [vden_eq] at this
    exact this
  have bI : (stS P val i).bs[1]? = some ⟨P.length+1,true⟩ := by simp [stS]
  have cI : (stS P val i).mem[P.length+1]? = some ⟨i32,i⟩ := by
    have := Proofs.ModIntExec.get_tail P [⟨s64,val⟩,⟨i32,i⟩] 1
    simpa [stS] using this
  have stI := pstmtW_assign_ok s64 (stS P val i) (fillv vec val (i+1)) 1 i32 Proofs.VectorSumCall.incE ((i : Int)+1) hinc
    ⟨P.length+1,true⟩ ⟨i32,i⟩ bI cI rfl (show i32.valid (i : Int) = true from i32_valid _ (by omega) (by omega)) rfl
    ((i : Int)+1) (conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega)))
  rw [set_i] at stI
  have b1 := (pexecW_prim s64 fu Proofs.VectorSumCall.assignI _ _).trans stI
  have b2 := seqW_some b1 rfl (pexecW_skip s64 fu (stS P val (i+1)) (fillv vec val (i+1)))
  have c1 := seqW_some a3 rfl b2
  refine ⟨_, c1, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp [vwp_idx, vwp_val, vwp_inc]
  · simp [vwp_idx, vwp_val, vwp_inc, stS, NExpr.nodes]
  · simp

theorem loop_runF (P : List Cell) (val : Int) (vec : List Int) (hn : vec.length < 2147483648)
    (hv : s64.valid val = true) :
    ∀ (m i : Nat), i + m = vec.length → ∀ fu, m + 1 ≤ fu →
      ∃ r, pexecW s64 fu loopCF (stS P val i) (fillv vec val i) = some r ∧
        r.ps = stS P val vec.length ∧ r.vec = fillv vec val vec.length ∧ r.ret = none ∧
        r.cost ≤ 19*m+7 ∧ r.need ≤ P.length + 16 ∧ r.wk = m := by
  intro m
  induction m with
  | zero =>
    intro i hi fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    have hc := cond_valL s64 (fillv vec val i) rfl P val i (by rw [fillv_length vec val i (by omega)]; exact hn)
      (by omega) (by rw [fillv_length vec val i (by omega)]; omega)
    rw [fillv_length vec val i (by omega)] at hc
    have hz : ¬ ((i : Int) < (vec.length : Int)) := by omega
    rw [if_neg hz] at hc
    rw [pexecW_while, hc]
    have : i = vec.length := by omega
    subst this
    simp only [Bind.bind, Option.bind, ite_true, vwp_cond]
    refine ⟨_, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
    · simp
    · simp [stS]
  | succ m ih =>
    intro i hi fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1, by omega⟩
    have hlt : i < vec.length := by omega
    have hlen := fillv_length vec val i (by omega)
    have hc := cond_valL s64 (fillv vec val i) rfl P val i (by rw [hlen]; exact hn) (by omega) (by rw [hlen]; omega)
    rw [hlen] at hc
    have ht : (i : Int) < (vec.length : Int) := by omega
    rw [if_pos ht] at hc
    obtain ⟨r1, h1', p1, v1, ret1, c1, n1, w1⟩ := iterF P val i vec hn hlt hv (fu'+1)
    have p1' : r1.ps = stS P val ((i+1 : Nat) : Int) := by rw [p1]; simp
    obtain ⟨r2, h2, p2, v2, ret2, c2, n2, w2⟩ := ih (i+1) (by omega) fu' (by omega)
    rw [pexecW_while, hc]
    simp only [Bind.bind, Option.bind, h1', ret1, p1', v1, h2, vwp_cond]
    refine ⟨⟨r2.ps, r2.vec, r2.ret, 6+1+r1.cost+r2.cost, max ((stS P val i).mem.length +
      (stS P val i).bs.length + 6 + 2) (max r1.need r2.need), r1.wk+r2.wk⟩, by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact p2
    · exact v2
    · exact ret2
    · simp; omega
    · simp [stS_size, n1, n2]; omega
    · simp [w1, w2]; omega

theorem body_execF (P : List Cell) (val : Int) (vec : List Int) (hn : vec.length < 2147483648)
    (hv : s64.valid val = true) (fu : Nat) (hfu : vec.length + 1 ≤ fu) :
    ∃ r, pexecW s64 fu bodyCmdF ⟨P ++ [⟨s64,val⟩],[⟨P.length,true⟩]⟩ vec = some r ∧
      r.ps = ⟨P ++ [⟨s64,val⟩],[⟨P.length,true⟩]⟩ ∧ r.vec = fillv vec val vec.length ∧ r.ret = none ∧
      r.cost ≤ 19*vec.length + 20 ∧ r.need ≤ P.length + 16 ∧ r.wk = vec.length := by
  have hv2 : vdenL s64 vec (penv1 (⟨P ++ [(⟨s64,val⟩ : Cell)],[⟨P.length,true⟩]⟩ : PS)) (.literal i32 0) = some 0 := by
    have h0 : i32.valid 0 = true := rfl
    rw [vdenL_scalar _ _ _ _ rfl, den_literal, if_pos h0]
  have d2 := pstmtW_declare_ok s64 (⟨P ++ [(⟨s64,val⟩ : Cell)],[⟨P.length,true⟩]⟩ : PS) vec i32 true (.literal i32 0) 0 hv2 0
    (conv_signed i32 rfl rfl _ rfl)
  have st0 : (⟨(P ++ [(⟨s64,val⟩ : Cell)]) ++ [(⟨i32,0⟩ : Cell)],[⟨P.length,true⟩] ++ [⟨(P ++ [(⟨s64,val⟩ : Cell)]).length,true⟩]⟩ : PS) =
      stS P val ((0 : Nat) : Int) := by
    simp [stS]
  rw [st0] at d2
  have v0 : vec = fillv vec val 0 := by simp [fillv]
  obtain ⟨rL, hL, pL, vL, retL, cL, nL, wL⟩ := loop_runF P val vec hn hv vec.length 0 (by omega) fu hfu
  rw [← v0] at hL
  have f2 := seqW_some hL retL (pexecW_skip s64 fu rL.ps rL.vec)
  have d2' := (pexecW_prim s64 fu Proofs.VectorSumCall.declI _ _).trans d2
  have f3 := seqW_some d2' rfl f2
  have f4 := pexecW_scope s64 fu _ _ _ _ f3
  have take_eq : (⟨(stS P val vec.length).mem.take (P ++ [(⟨s64,val⟩ : Cell)]).length,
      (stS P val vec.length).bs.take [(⟨P.length,true⟩ : CppState.Binding)].length⟩ : PS) =
      (⟨P ++ [(⟨s64,val⟩ : Cell)],[⟨P.length,true⟩]⟩ : PS) := by
    simp [stS, List.take_append, List.take_of_length_le]
  rw [pL] at f4
  simp only [take_eq] at f4
  have h5 := seqW_some f4 rfl (pexecW_skip s64 fu (⟨P ++ [(⟨s64,val⟩ : Cell)],[⟨P.length,true⟩]⟩ : PS) rL.vec)
  refine ⟨_, h5, rfl, ?_, rfl, ?_, ?_, ?_⟩
  · simp [vL]
  · simp [vwp_lit2]
    omega
  · simp [vwp_lit2, stS]
    omega
  · simp [wL]

-- The caller owns a writable root vector of `long long` bound at its vector slot `vslot`.
structure VOKW (caller : NState) (vslot vb V vsc : Nat) (vbuf : Buffer Value) : Prop where
  valid : caller.frame.state.wellFormed = true
  slot : caller.vectorSlot vslot = some vb
  binding : caller.frame.bindings[vb]? = some ⟨V,.integer s64,true,.root vsc⟩
  vtag : caller.frame.state.forest.lookup V = some ⟨.integer s64,none,some vsc,[]⟩
  vfound : caller.frame.state.storage.lookup V = some vbuf
  lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length
  flag : caller.frame.rootWritable[V]? = some true
  strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope
  base : caller.scalars.baseMemory ≤ caller.scalars.memory.length

theorem prepare_vf (caller : NState) {vslot vb V vsc : Nat} {vbuf : Buffer Value}
    (ok : VOKW caller vslot vb V vsc vbuf) (e : NExpr) (v : Int) (hs : e.scalarOnly = true)
    (hty : e.resultType = s64) (value : e.denote (envOf caller) = some v) (hv : s64.valid v = true) :
    ∃ t, Good (caller.charge 1 1) t e.nodes e.nodes ∧
      ∃ Sinit, prepare caller Proofs.VectorFillInstance.vector_fill_std_vector_long_long.parameters [.vectorReference vslot,.value e] = some Sinit ∧
        Sinit.slots = [.vector 0,.scalar 0] ∧ Sinit.scalars.memory = callerP caller ++ [⟨s64,v⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer s64,true,.root vsc⟩]⟩ ∧
        Sinit.scalars.work = t.scalars.work+3 ∧ t.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc s64 true true vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (fun _ => rfl)
  have rvec : resolve caller (.vector s64 true) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc s64 true) := by
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
  have hp : Proofs.VectorFillInstance.vector_fill_std_vector_long_long.parameters = [.vector s64 true,.scalar s64 false true] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec,res]
  simp [fs,fr,fb,hmem,hbind,hbase,bound,bindAll,bindOne,CppState.bindArgument,hv,callerP,
    NState.observe,CppState.State.observe]
  refine ⟨Nat.le_max_left _ _,?_⟩
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
theorem vector_fill_correct (caller : NState) {vslot vb V vsc : Nat} {vbuf : Buffer Value}
    (ok : VOKW caller vslot vb V vsc vbuf) (vec : List Int) (hitems : vbuf.items = vec.map Value.integer)
    (hbvalid : vbuf.Valid (accepts (.integer s64))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit s64)
    (howner : vbuf.owner = V) (hn : vec.length < 2147483648)
    (e : NExpr) (v : Int) (hs : e.scalarOnly = true) (hty : e.resultType = s64)
    (value : e.denote (envOf caller) = some v) (hv : s64.valid v = true) :
    ∃ Sinit fuel res, prepare caller Proofs.VectorFillInstance.vector_fill_std_vector_long_long.parameters
        [.vectorReference vslot,.value e] = some Sinit ∧
      Proofs.VectorFillInstance.vector_fill_std_vector_long_long.callFuel fuel caller [.vectorReference vslot,.value e] =
        .finished (res,Ret.unit) ∧
      ScalarPost3 caller Sinit res e.nodes (19*vec.length+30) caller.scalars.memory vec.length V
        (List.replicate vec.length v) := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_vf caller ok e v hs hty value hv
  let vc : VCtx := ⟨s64,true,true,V,vsc,vbuf,vec,hitems,fun _ => rfl,by omega,caller.frame.state.liveSpace,
    caller.frame.state.storage.work,caller.scope+1,caller.frame.state.storage.objects.length⟩
  have hty' : vc.ty = s64 := rfl
  have fwS : FW vc vec vbuf 0 Sinit.frame := by
    rw [sFrame]
    refine ⟨ok.valid,ok.lengths,rfl,rfl,?_,rfl,rfl,ok.vtag,ok.vfound,ok.flag,hitems,hbvalid,hlimit,howner,by omega⟩
    intro owner k h
    have := ok.strict owner k h
    show k < caller.scope+1
    omega
  obtain ⟨r,hexec,hrps,hrvec,hret,hcost,hneed,hwk⟩ := body_execF (callerP caller) v vec hn hv (vec.length+1) (Nat.le_refl _)
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨s64,v⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory :=
    take_P caller _
  have gw := good.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw
  have hpost := call_vecw_unit vc true (fun _ => ⟨rfl,rfl⟩) caller Proofs.VectorFillInstance.vector_fill_std_vector_long_long [.vectorReference vslot,.value e] Sinit
    (callerP caller ++ [(⟨s64,v⟩ : Cell)]) [(⟨(callerP caller).length,true⟩ : CppState.Binding)]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlen]; omega) (by rw [takeM]) ok.base (by decide) (vec.length+1) r
    (by rw [body_eq]; exact hexec) hret rfl (by omega) (by simp) e.nodes (19*vec.length+30) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]; exact takeM
  rw [hs'] at post
  have hvec : fillv vec v vec.length = List.replicate vec.length v := by simp [fillv]
  rw [hrvec, hvec, hwk] at post
  exact post

end Proofs.VectorFillCall
