import Proofs.UfUniteCall

namespace Proofs.UfCounterCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.VecStraight Proofs.VecCall Proofs.VecKit
open Proofs.CppNestedFacts Proofs.IntSim Proofs.ScalarCall Proofs.VecWrite Proofs.VecWriteCall Proofs.VecKitW
open Proofs.QuotientSearch Proofs.VectorFillCall Proofs.PrefixSumsCall
open Proofs.UfRootCall Proofs.UfSameCall Proofs.UfUniteCall
open Proofs.VectorSumCall (conv_signed i32_valid)
open Proofs.CppState (Cell)
open Proofs.PowModStep (Sk)

abbrev negOne : NExpr := .unary i32 .neg (.literal i32 1)

theorem den_unaryU (env : Nat → Ty → Option Int) (ty : Ty) (op : Unary) (e : NExpr) :
    (NExpr.unary ty op e).denote env = (e.denote env).bind fun v => ty.convert (unaryValue op v) := by
  simp [NExpr.denote]

theorem negOne_val (env : Nat → Ty → Option Int) : negOne.denote env = some (-1) := by
  rw [den_unaryU, den_literal, if_pos (show i32.valid 1 = true from rfl), Option.bind_some]
  exact conv_signed i32 rfl rfl _ rfl

/-! ### `UnionFind::num_groups`: `int last = ps.size() - 1; return -1 - ps[last];` -/

abbrev retNG : NExpr := .binary i32 .sub negOne rdA
abbrev bodyNG : Command := .sequence declLast (.sequence (.primitive (.ret retNG)) Sk)

theorem body_eqNG : Proofs.UnionFindInstance.UnionFind_num_groups.body = bodyNG := rfl

theorem retNG_val (ps : List Int) (P : List Cell) (r : Nat) (x : Int) (hn : ps.length < 2147483648)
    (hr : r < ps.length) (hx : ps[r]? = some x) (hxv : i32.valid x = true) :
    vdenL i32 ps (penv1 (stI P r)) retNG = some (-1 - x) := by
  have hb : retNG.scalarOnly = false := rfl
  have hl : vdenL i32 ps (penv1 (stI P r)) negOne = some (-1) := by
    rw [vdenL_scalar _ _ _ _ rfl, negOne_val]
  rw [vdenL_binary _ _ _ _ _ _ _ hb, hl, rdA_valU ps P r x hn hr hx hxv, Option.bind_some, Option.bind_some]
  have : binaryValue .sub (-1) x = -1 - x := rfl
  rw [this]
  refine conv_signed i32 rfl rfl _ ?_
  have := hxv
  simp [Ty.valid] at this ⊢
  omega


theorem Loc_stI (P : List Cell) (a : Int) : Loc (stI P a) 0 P.length a := by
  refine ⟨by simp [stI], ?_⟩
  simp [stI]

set_option maxHeartbeats 4000000 in
theorem body_exec_ng (P : List Cell) (ps : List Int) (hn : ps.length < 2147483648) (hl : 1 ≤ ps.length) (vL : Int)
    (hvL : ps[ps.length - 1]? = some vL) (gL : i32.valid vL = true) (fu : Nat) :
    ∃ res : PRW, pexecW i32 fu bodyNG ⟨P,[]⟩ ps = some res ∧ res.ret = some (-1 - vL) ∧ res.vec = ps ∧ res.wk = 0 ∧
      res.cost ≤ 60 ∧ res.need ≤ P.length + 40 ∧ res.ps.mem.take P.length = P := by
  have lv := lastE_val ps ⟨P,[]⟩ hn hl
  have d := pstmtW_declare_ok i32 (⟨P,[]⟩ : PS) ps i32 true lastE ((ps.length - 1 : Nat) : Int) lv
    ((ps.length - 1 : Nat) : Int) (conv_signed i32 rfl rfl _ (i32_valid _ (by omega) (by omega)))
  have st0 : (⟨P ++ [(⟨i32,((ps.length - 1 : Nat) : Int)⟩ : Cell)],[] ++ [⟨P.length,true⟩]⟩ : PS) =
      stI P ((ps.length - 1 : Nat) : Int) := by simp [stI]
  simp only [List.length_nil, List.append_nil, Nat.zero_add] at d
  have d' : pstmtW i32 (.declare i32 true lastE) ⟨P,[]⟩ ps = some ⟨stI P ((ps.length - 1 : Nat) : Int),ps,none,
      (vwp lastE).1+1,P.length+0+(vwp lastE).2+4,0⟩ := by
    rw [← st0]; simpa using d
  have hret := retNG_val ps P (ps.length - 1) vL hn (by omega) hvL gL
  have g1 := pstmtW_ret_ok i32 (stI P ((ps.length - 1 : Nat) : Int)) ps retNG (-1 - vL) hret
  have g2 := (pexecW_prim i32 fu (.ret retNG) _ _).trans g1
  have g3 := seqW_ret (b := Sk) g2 rfl
  have d3 := (pexecW_prim i32 fu (.declare i32 true lastE) _ _).trans d'
  have h4 := seqW_some d3 rfl g3
  refine ⟨_, h4, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp
  · simp [vwp, NExpr.nodes, Container.nodes, stI]
  · simp [vwp, NExpr.nodes, Container.nodes, stI]
  · simp [stI]

theorem prepare_ng (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : VOKI caller vslot vb V vsc m vbuf) :
    ∃ Sinit, prepare caller Proofs.UnionFindInstance.UnionFind_num_groups.parameters [.vectorReference vslot] = some Sinit ∧
      Sinit.slots = [.vector 0] ∧ Sinit.scalars.memory = callerP caller ∧ Sinit.scalars.bindings = [] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,false,.root vsc⟩]⟩ ∧
      Sinit.scalars.work = caller.scalars.work+3 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨resolved,_,_⟩ := resolve_vroot caller.frame vb V vsc i32 false m vbuf ok.binding ok.valid ok.vtag ok.vfound
    ok.lengths ok.flag (by simp)
  have rvec : resolve caller (.vector i32 false) (.vectorReference vslot) =
      some (caller.charge 1 1,.vector V vsc i32 false) := by
    simp [resolve,ok.slot,ok.binding,resolved]
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
  have hp : Proofs.UnionFindInstance.UnionFind_num_groups.parameters = [.vector i32 false] := rfl
  rw [hp]
  simp [prepare,ok.valid,resolveAll,rvec]
  simp [bound,bindAll,bindOne,CppState.bindArgument,callerP,NState.observe,CppState.State.observe,NState.charge]

set_option maxHeartbeats 4000000 in
theorem uf_num_groups_correct (caller : NState) {vslot vb V vsc : Nat} {m : Bool} {vbuf : Buffer Value}
    (ok : VOKI caller vslot vb V vsc m vbuf) (ps : List Int)
    (hitems : vbuf.items = ps.map Value.integer) (hn : ps.length < 2147483648)
    (hbvalid : vbuf.Valid (accepts (.integer i32))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit i32)
    (howner : vbuf.owner = V) (hl : 1 ≤ ps.length) (vL : Int) (hvL : ps[ps.length - 1]? = some vL)
    (gL : i32.valid vL = true) :
    ∃ Sinit fuel res, prepare caller Proofs.UnionFindInstance.UnionFind_num_groups.parameters
        [.vectorReference vslot] = some Sinit ∧
      Proofs.UnionFindInstance.UnionFind_num_groups.callFuel fuel caller [.vectorReference vslot] =
        .finished (res,.scalar (-1 - vL)) ∧
      ScalarPost3 caller Sinit res 0 100 caller.scalars.memory 0 V ps := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prepare_ng caller ok
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
  obtain ⟨rr,hexec,hret,hrvec,hwk,hcost,hneed,htake⟩ := body_exec_ng (callerP caller) ps hn hl vL hvL gL 2
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have hres : i32.valid (-1 - vL) = true := by
    have := gL
    simp [Ty.valid] at this ⊢
    omega
  have hpost := call_vecw vc false (fun h => absurd h (by decide)) caller Proofs.UnionFindInstance.UnionFind_num_groups
    [.vectorReference vslot] Sinit (callerP caller) [] hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope
    (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl (by omega) (by simp [hlenP]) (by simp [callerP])
    ok.base (by decide) 2 rr (by rw [body_eqNG]; exact hexec) (-1 - vL) hret i32 rfl hres (by omega)
    (by simp [hlenP]) 0 100 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    have hle : caller.scalars.memory.length ≤ (callerP caller).length := by omega
    calc rr.ps.mem.take caller.scalars.memory.length
        = (rr.ps.mem.take (callerP caller).length).take caller.scalars.memory.length := by
          rw [List.take_take, Nat.min_eq_left hle]
      _ = (callerP caller).take caller.scalars.memory.length := by rw [htake]
      _ = caller.scalars.memory := by simp only [callerP]; exact List.take_left' rfl
  rw [hs', hrvec, hwk] at post
  exact post


/-! ### `UnionFind::UnionFind(int n)`: the body `ps[n] = -1 - n;` after `ps(n + 1, -1)` -/

abbrev wrNew : NStmt := .write (.local 0) i32 (.cast u64 (.variable i32 1)) (.binary i32 .sub negOne (.variable i32 1))
abbrev bodyNew : Command := .sequence (.primitive wrNew) Sk

theorem body_eqNew : Proofs.UnionFindInstance.UnionFind_new1.body = UfBounds.checked (UfBounds.lower 1) bodyNew := rfl

set_option maxHeartbeats 4000000 in
theorem body_exec_new (P : List Cell) (ps : List Int) (n : Nat) (hn : ps.length < 2147483648) (hnl : n < ps.length)
    (fu : Nat) :
    ∃ res : PRW, pexecW i32 fu bodyNew (stI P n) ps = some res ∧ res.ret = none ∧ res.ps = stI P n ∧
      res.vec = ps.set n (-1 - (n : Int)) ∧ res.wk = 1 ∧ res.cost ≤ 60 ∧ res.need ≤ P.length + 40 := by
  have L := Loc_stI P (n : Int)
  have hp : vdenL i32 ps (penv1 (stI P n)) (NExpr.cast u64 (.variable i32 1)) = some (n : Int) := by
    rw [vdenL_scalar _ _ _ _ rfl]; exact idxK (stI P n) 0 P.length n L (by omega)
  have hx : vdenL i32 ps (penv1 (stI P n)) (NExpr.binary i32 .sub negOne (.variable i32 1)) = some (-1 - (n : Int)) := by
    rw [vdenL_scalar _ _ _ _ rfl, den_binary, negOne_val, den_variable,
      env_loc (stI P n) 0 P.length (n : Int) L (i32_valid n (by omega) (by omega)), Option.bind_some, Option.bind_some]
    have : binaryValue .sub (-1) (n : Int) = -1 - (n : Int) := rfl
    rw [this]
    refine conv_signed i32 rfl rfl _ ?_
    simp [Ty.valid]
    omega
  have hv : i32.valid (-1 - (n : Int)) = true := by simp [Ty.valid]; omega
  have w := pstmtW_write_ok i32 (stI P n) ps (NExpr.cast u64 (.variable i32 1))
    (NExpr.binary i32 .sub negOne (.variable i32 1)) (-1 - (n : Int)) n hx hp hnl hv
  have w1 := (pexecW_prim i32 fu wrNew _ _).trans w
  have w2 := seqW_some w1 rfl (pexecW_skip i32 fu (stI P n) (ps.set n (-1 - (n : Int))))
  refine ⟨_, w2, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simp
  · simp [vwp, NExpr.nodes, Container.nodes]
  · simp [vwp, NExpr.nodes, Container.nodes, stI]

theorem prepare_new (caller : NState) {vslot vb V vsc : Nat} {vbuf : Buffer Value}
    (ok : UfFindCall.VOKWF caller vslot vb V vsc vbuf) (e : NExpr) (v : Int) (hs : e.scalarOnly = true)
    (hty : e.resultType = i32) (value : e.denote (envOf caller) = some v) (hv : i32.valid v = true) :
    ∃ t, Good (caller.charge 1 1) t e.nodes e.nodes ∧
      ∃ Sinit, prepare caller Proofs.UnionFindInstance.UnionFind_new1.parameters [.vectorReference vslot,.value e] = some Sinit ∧
        Sinit.slots = [.vector 0,.scalar 0] ∧ Sinit.scalars.memory = callerP caller ++ [⟨i32,v⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[⟨V,.integer i32,true,.root vsc⟩]⟩ ∧
        Sinit.scalars.work = t.scalars.work+3 ∧ t.scalars.peak ≤ Sinit.scalars.peak ∧
        caller.scalars.peak ≤ Sinit.scalars.peak :=
  UfFindCall.prepare_fd caller ok e v hs hty value hv

set_option maxHeartbeats 4000000 in
theorem uf_new_correct (caller : NState) {vslot vb V vsc : Nat} {vbuf : Buffer Value}
    (ok : UfFindCall.VOKWF caller vslot vb V vsc vbuf) (ps : List Int)
    (hitems : vbuf.items = ps.map Value.integer) (hn : ps.length < 2147483648)
    (hbvalid : vbuf.Valid (accepts (.integer i32))) (hlimit : vbuf.limit = CppVectorBindings.sizeLimit i32)
    (howner : vbuf.owner = V)
    (e : NExpr) (a : Nat) (hs : e.scalarOnly = true) (ht : e.resultType = i32)
    (value : e.denote (envOf caller) = some (a : Int)) (ha : a < ps.length) :
    ∃ Sinit fuel res, prepare caller Proofs.UnionFindInstance.UnionFind_new1.parameters
        [.vectorReference vslot,.value e] = some Sinit ∧
      Proofs.UnionFindInstance.UnionFind_new1.callFuel fuel caller [.vectorReference vslot,.value e] =
        .finished (res,Ret.unit) ∧
      ScalarPost3 caller Sinit res e.nodes 120 caller.scalars.memory 1 V (ps.set a (-1 - (a : Int))) := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_new caller ok e (a : Int) hs ht value (i32_valid a (by omega) (by omega))
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
  obtain ⟨rr,hexec,hret,hrps,hrvec,hwk,hcost,hneed⟩ := body_exec_new (callerP caller) ps a hn ha 1
  have hexec' := UfBounds.prepend (UfBounds.lower_value _ _ 1 a
    (env_i1 (callerP caller) a (i32_valid a (by omega) (by omega))) (by omega)) hexec
  have hneed' : (UfBounds.charged (stI (callerP caller) a) (UfBounds.lower 1) rr).need ≤ (callerP caller).length+112 := by
    simp only [UfBounds.charged,stI,List.length_append,List.length_cons,List.length_nil]
    have wp : vwp (UfBounds.lower 1) = (3,3) := rfl
    rw [wp]; dsimp; omega
  have hcost' : (UfBounds.charged (stI (callerP caller) a) (UfBounds.lower 1) rr).cost ≤ 80 := by
    dsimp [UfBounds.charged]
    have wp : vwp (UfBounds.lower 1) = (3,3) := rfl
    rw [wp]; dsimp; omega
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(a : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := UfRootCall.take_P caller _
  have gw1 := good.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hpost := call_vecw_unit vc true (fun _ => ⟨rfl,rfl⟩) caller Proofs.UnionFindInstance.UnionFind_new1
    [.vectorReference vslot,.value e] Sinit
    (callerP caller ++ [(⟨i32,(a : Int)⟩ : Cell)]) [(⟨(callerP caller).length,true⟩ : CppState.Binding)]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok.base (by decide) 1 (UfBounds.charged (stI (callerP caller) a) (UfBounds.lower 1) rr)
    (by rw [body_eqNew]; exact hexec') hret rfl hneed' (by simp) e.nodes 120 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  dsimp only [UfBounds.bounded,UfBounds.charged] at post
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [stI]
    exact UfRootCall.take_P caller _
  rw [hs', hrvec, hwk] at post
  exact post

end Proofs.UfCounterCall
