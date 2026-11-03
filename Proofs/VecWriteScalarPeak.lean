import Proofs.VecWriteFrame
import Proofs.CppCallUnique

namespace Proofs.VecWriteScalarPeak
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.VecStraight
open Proofs.VecCall Proofs.VecWrite
open Proofs.CppState (Cell)

open Proofs.VecWriteCall

set_option maxHeartbeats 4000000 in
-- Keep scalar peak independent of the historical outer peak.
theorem call_vecw_scalar_peak (vc : VCtx) (w : Bool) (hw : w = true → vc.wV = true ∧ vc.flag = true) (caller : NState) (prog : NProgram) (args : List NArgument) (Sinit : NState)
    (M : List Cell) (bs : List CppState.Binding)
    (hprep : prepare caller prog.parameters args = some Sinit)
    (sSlots : Sinit.slots = sl1 bs.length) (sMem : Sinit.scalars.memory = M) (sBind : Sinit.scalars.bindings = bs)
    (sBase : Sinit.scalars.baseMemory = caller.scalars.baseMemory) (sScope : Sinit.scope = caller.scope+1)
    (sState : Sinit.frame.state = caller.frame.state) (sRw : Sinit.frame.rootWritable = caller.frame.rootWritable)
    {vec0 : List Int} {buf0 : Buffer Value} (fwS : FW vc vec0 buf0 0 Sinit.frame) (hL0 : vc.L0 = caller.frame.state.liveSpace)
    (hT0 : vc.T0 = caller.frame.state.storage.work) (hN : vc.N = caller.frame.state.storage.objects.length)
    (hsc : vc.sc = caller.scope+1)
    (sPeak : caller.scalars.peak ≤ Sinit.scalars.peak)
    (hMlen : caller.scalars.memory.length ≤ M.length)
    (hMtypes : (M.take caller.scalars.memory.length).map Cell.type = caller.scalars.memory.map Cell.type)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (hbody : WrV w prog.body = true) (fu : Nat) (r : PRW) (hexec : pexecW vc.ty fu prog.body ⟨M,bs⟩ vec0 = some r) (v : Int)
    (hret : r.ret = some v) (ty : Ty) (hres : prog.result = ResultKind.scalar ty) (hv : ty.valid v = true)
    (hneed : r.need ≤ (callerP caller).length+112) (hlive0 : M.length+bs.length ≤ (callerP caller).length+100)
    (kn extra : Nat) (hwork : Sinit.scalars.work+r.cost+1 ≤ caller.scalars.work+kn+extra) :
    ∃ fuel res, prog.callFuel fuel caller args = .finished (res,.scalar v) ∧
      res.scalars.peak ≤ max Sinit.scalars.peak ((callerP caller).length+12-caller.scalars.baseMemory+100) := by
  obtain ⟨SPB,hSPB⟩ : ∃ SPB, SPB = max Sinit.scalars.peak
    ((callerP caller).length+12-caller.scalars.baseMemory+100) := ⟨_,rfl⟩
  obtain ⟨TPB,hTPB⟩ : ∃ TPB, TPB = max Sinit.peak (max caller.frame.state.storage.peak (caller.frame.state.liveSpace+1)) := ⟨_,rfl⟩
  have hB : caller.scalars.baseMemory ≤ (callerP caller).length := by
    have : caller.scalars.memory.length ≤ (callerP caller).length := by simp [callerP]
    omega
  have qs : QS Sinit [] caller.scalars.baseMemory (caller.scope+1) M bs (sl1 bs.length) :=
    ⟨sSlots,by rw [sMem]; simp,sBind,sBase,sScope⟩
  have cq : Cq SPB TPB Sinit.scalars.work Sinit := by
    refine ⟨Nat.le_refl _,?_,?_,?_⟩
    · show Sinit.scalars.peak ≤ SPB; rw [hSPB]; omega
    · show Sinit.frame.state.storage.peak ≤ TPB; rw [hTPB,sState]; omega
    · show Sinit.peak ≤ SPB + TPB; rw [hSPB]; omega
  have run := soundW vc w hw prog.body hbody fu ⟨M,bs⟩ vec0 r hexec (SPB := SPB) (TPB := TPB) (W := Sinit.scalars.work) (wk := 0)
    (buf := buf0) Sinit qs fwS cq
    (by show caller.scalars.baseMemory ≤ M.length; omega)
    (by show M.length+bs.length ≤ SPB+caller.scalars.baseMemory; rw [hSPB]; omega)
    (by rw [hSPB]; omega) (by omega) (by rw [hTPB,hL0]; omega)
  obtain ⟨fuel,step,hrun,ret,brk,qsD,⟨bufD,faD⟩,cqD⟩ := run
  have ext := pexecW_ext vc w prog.body hbody fu ⟨M,bs⟩ vec0 r hexec
  have memD : step.state.scalars.memory = r.ps.mem := qsD.memory
  have takeEq : step.state.scalars.memory.take caller.scalars.memory.length =
      r.ps.mem.take caller.scalars.memory.length := by rw [memD]
  have rLen : caller.scalars.memory.length ≤ r.ps.mem.length := Nat.le_trans hMlen ext.2.2.1
  have cond : caller.scalars.memory.length ≤ step.state.scalars.memory.length ∧
      (step.state.scalars.memory.take caller.scalars.memory.length).map Cell.type =
        caller.scalars.memory.map Cell.type := by
    refine ⟨by rw [memD]; exact rLen,?_⟩
    rw [takeEq]
    have h1 : (r.ps.mem.take M.length).map Cell.type = M.map Cell.type := ext.2.2.2
    have h2 : (r.ps.mem.take caller.scalars.memory.length) =
        (r.ps.mem.take M.length).take caller.scalars.memory.length := by
      rw [List.take_take]; simp [Nat.min_eq_left hMlen]
    rw [h2,List.map_take,h1,← List.map_take,hMtypes]
  have scopeD : step.state.scope = caller.scope+1 := qsD.scope
  have fresh : ∀ owner, step.state.frame.state.forest.context owner ≠ some step.state.scope := by
    intro owner h
    have := faD.strict owner _ h
    omega
  have fin := finish_scalar caller step.state ty v hv cond faD.valid fresh
  refine ⟨fuel,finS caller step.state,?_,?_⟩
  · unfold NProgram.callFuel
    simp only [hprep,Proofs.CppLoop.liftChecked,Proofs.CppLoop.Outcome.bind]
    have ret' : step.returned = some (.scalar v) := by rw [ret,hret]; rfl
    simp only [Bind.bind,Proofs.CppLoop.Outcome.bind,hrun,brk,hres,ret',fin]
    simp
  · have spR : step.state.scalars.peak ≤ SPB := cqD.scalarPeak
    have takeLen : (step.state.scalars.memory.take caller.scalars.memory.length).length = caller.scalars.memory.length := by
      simp only [List.length_take,Nat.min_eq_left cond.1]
    have scalarPeak : (finS caller step.state).scalars.peak =
        max (max caller.scalars.peak step.state.scalars.peak)
          ((step.state.scalars.memory.take caller.scalars.memory.length).length-caller.scalars.baseMemory+
            caller.scalars.bindings.length+0) := rfl
    rw [scalarPeak,takeLen]
    have oldBound : caller.scalars.peak ≤ SPB := Nat.le_trans sPeak (by rw [hSPB]; exact Nat.le_max_left _ _)
    have liveBound : caller.scalars.memory.length-caller.scalars.baseMemory+caller.scalars.bindings.length+0 ≤ SPB := by
      rw [hSPB]
      have length : (callerP caller).length = caller.scalars.memory.length+
          (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
      omega
    rw [← hSPB]
    exact Nat.max_le.mpr ⟨Nat.max_le.mpr ⟨oldBound,spR⟩,liveBound⟩


set_option maxHeartbeats 4000000 in
theorem call_vecw_scalar_peak_actual (vc : VCtx) (w : Bool) (hw : w = true → vc.wV = true ∧ vc.flag = true) (caller : NState) (prog : NProgram) (args : List NArgument) (Sinit : NState)
    (M : List Cell) (bs : List CppState.Binding)
    (hprep : prepare caller prog.parameters args = some Sinit)
    (sSlots : Sinit.slots = sl1 bs.length) (sMem : Sinit.scalars.memory = M) (sBind : Sinit.scalars.bindings = bs)
    (sBase : Sinit.scalars.baseMemory = caller.scalars.baseMemory) (sScope : Sinit.scope = caller.scope+1)
    (sState : Sinit.frame.state = caller.frame.state) (sRw : Sinit.frame.rootWritable = caller.frame.rootWritable)
    {vec0 : List Int} {buf0 : Buffer Value} (fwS : FW vc vec0 buf0 0 Sinit.frame) (hL0 : vc.L0 = caller.frame.state.liveSpace)
    (hT0 : vc.T0 = caller.frame.state.storage.work) (hN : vc.N = caller.frame.state.storage.objects.length)
    (hsc : vc.sc = caller.scope+1)
    (sPeak : caller.scalars.peak ≤ Sinit.scalars.peak)
    (hMlen : caller.scalars.memory.length ≤ M.length)
    (hMtypes : (M.take caller.scalars.memory.length).map Cell.type = caller.scalars.memory.map Cell.type)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (hbody : WrV w prog.body = true) (fu : Nat) (r : PRW) (hexec : pexecW vc.ty fu prog.body ⟨M,bs⟩ vec0 = some r) (v : Int)
    (hret : r.ret = some v) (ty : Ty) (hres : prog.result = ResultKind.scalar ty) (hv : ty.valid v = true)
    (hneed : r.need ≤ (callerP caller).length+112) (hlive0 : M.length+bs.length ≤ (callerP caller).length+100)
    (kn extra : Nat) (hwork : Sinit.scalars.work+r.cost+1 ≤ caller.scalars.work+kn+extra)
    (actualFuel : Nat) (out : NState) (result : Ret)
    (actual : prog.callFuel actualFuel caller args = .finished (out,result)) :
    out.scalars.peak ≤ max Sinit.scalars.peak ((callerP caller).length+12-caller.scalars.baseMemory+100) := by
  obtain ⟨fuel,computed,ran,peak⟩ := call_vecw_scalar_peak vc w hw caller prog args Sinit M bs hprep
    sSlots sMem sBind sBase sScope sState sRw fwS hL0 hT0 hN hsc sPeak hMlen hMtypes base hbody
    fu r hexec v hret ty hres hv hneed hlive0 kn extra hwork
  have same := Proofs.CppCallUnique.call_unique prog fuel actualFuel caller args (computed,.scalar v) (out,result) ran actual
  have outEq := congrArg Prod.fst same
  change computed = out at outEq
  rw [← outEq]
  exact peak

end Proofs.VecWriteScalarPeak
