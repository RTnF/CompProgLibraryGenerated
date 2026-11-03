import Proofs.VecWrite
import Proofs.VecCall

namespace Proofs.VecWriteCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.VecStraight
open Proofs.VecCall Proofs.VecWrite
open Proofs.CppState (Cell)

structure ScalarPost3 (caller Sinit res : NState) (kn extra : Nat) (mem : List Cell) (wk V : Nat) (items : List Int) : Prop where
  valid : res.frame.state.wellFormed = true
  objects : res.frame.state.storage.objects.length = caller.frame.state.storage.objects.length
  live : res.frame.state.liveSpace = caller.frame.state.liveSpace
  storageWork : res.frame.state.storage.work ≤ caller.frame.state.storage.work + wk
  rwLength : res.frame.rootWritable.length = caller.frame.state.storage.objects.length
  slots : res.slots = caller.slots
  scope : res.scope = caller.scope
  bindings : res.frame.bindings = caller.frame.bindings
  scalarMemory : res.scalars.memory = mem
  storagePeak : res.frame.state.storage.peak ≤ max caller.frame.state.storage.peak (caller.frame.state.liveSpace+1)
  scalarWork : res.scalars.work ≤ caller.scalars.work+kn+extra
  scalarPeak : res.scalars.peak ≤ max (max Sinit.scalars.peak Sinit.peak)
    ((callerP caller).length+12-caller.scalars.baseMemory+100)
  outerPeak : res.peak ≤ max caller.peak (max (max Sinit.scalars.peak Sinit.peak)
      ((callerP caller).length+12-caller.scalars.baseMemory+100) +
    max caller.frame.state.storage.peak (caller.frame.state.liveSpace+1))
  vector : ∃ buf', res.frame.state.storage.lookup V = some buf' ∧ buf'.items = items.map Value.integer

theorem scalar_post3 (caller Sinit R : NState) (kn extra W : Nat) {mem : List Cell} {SPB TPB : Nat}
    (hSPB : SPB = max (max Sinit.scalars.peak Sinit.peak) ((callerP caller).length+12-caller.scalars.baseMemory+100))
    (hTPB : TPB = max caller.frame.state.storage.peak (caller.frame.state.liveSpace+1))
    (htake : R.scalars.memory.take caller.scalars.memory.length = mem) (hmemLen : mem.length = caller.scalars.memory.length)
    (hbase : R.scalars.baseMemory = caller.scalars.baseMemory)
    (hbm : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (spC : caller.scalars.peak ≤ Sinit.scalars.peak)
    (vc : VCtx) (hL0 : vc.L0 = caller.frame.state.liveSpace) (hT0 : vc.T0 = caller.frame.state.storage.work)
    (hN : vc.N = caller.frame.state.storage.objects.length) {vec : List Int} {buf : Buffer Value} {wk : Nat} (fa : FW vc vec buf wk R.frame)
    (cq : Cq SPB TPB W R) (hw : R.scalars.work+1 ≤ caller.scalars.work+kn+extra) :
    ScalarPost3 caller Sinit (finS caller R) kn extra mem wk vc.R vec := by
  have same := noopRetired_same R.frame
  have faLive : R.frame.state.liveSpace = caller.frame.state.liveSpace := fa.live.trans hL0
  have faWork : R.frame.state.storage.work = caller.frame.state.storage.work + wk := by have := fa.work; omega
  have faCount : R.frame.state.storage.objects.length = caller.frame.state.storage.objects.length := fa.count.trans hN
  have lenP : (callerP caller).length = caller.scalars.memory.length+
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeLen : (R.scalars.memory.take caller.scalars.memory.length).length = caller.scalars.memory.length := by
    rw [htake]; exact hmemLen
  have spR : R.scalars.peak ≤ SPB := cq.scalarPeak
  have stR : R.frame.state.storage.peak ≤ TPB := cq.storagePeak
  have opR : R.peak ≤ SPB+TPB := cq.outerPeak
  have resSp : (finS caller R).scalars.peak =
      max (max caller.scalars.peak R.scalars.peak)
        ((R.scalars.memory.take caller.scalars.memory.length).length-caller.scalars.baseMemory+
          caller.scalars.bindings.length+0) := rfl
  have spRes : (finS caller R).scalars.peak ≤ SPB := by
    rw [resSp,takeLen]
    have h2 : caller.scalars.peak ≤ SPB := by rw [hSPB]; omega
    have h4 : caller.scalars.memory.length-caller.scalars.baseMemory+caller.scalars.bindings.length+0 ≤ SPB := by
      rw [hSPB]; omega
    omega
  have stRes : (finS caller R).frame.state.storage.peak ≤ TPB := by
    show max R.frame.state.storage.peak (R.frame.state.liveSpace-R.frame.state.storage.baseSpace) ≤ TPB
    rw [hTPB] at stR ⊢
    have := faLive
    omega
  have resPeak : (finS caller R).peak = max (max caller.peak R.peak)
      ((finS caller R).scalars.peak + (finS caller R).frame.state.storage.peak) := rfl
  have wf := (wellFormed_parts _ fa.valid).1
  refine ⟨?_,?_,?_,?_,?_,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_⟩
  · show (noopRetired R.frame).state.wellFormed = true
    rw [same.wellFormed]; exact fa.valid
  · show (noopRetired R.frame).state.storage.objects.length = _
    rw [same.2.1]; exact faCount
  · show (noopRetired R.frame).state.liveSpace = _
    rw [same.liveSpace]; exact faLive
  · show R.frame.state.storage.work ≤ _
    exact Nat.le_of_eq faWork
  · show R.frame.rootWritable.length = _
    have := fa.lengths
    have := faCount
    omega
  · show R.scalars.memory.take caller.scalars.memory.length = mem
    exact htake
  · rw [hTPB] at stRes; exact stRes
  · show R.scalars.work+1 ≤ _
    exact hw
  · rw [hSPB] at spRes; exact spRes
  · rw [resPeak]
    have key : max (max caller.peak R.peak) ((finS caller R).scalars.peak + (finS caller R).frame.state.storage.peak)
        ≤ max caller.peak (SPB+TPB) := peak_final3 SPB TPB _ _ _ _ _ _ _ opR spR spR stR spRes stRes
    rw [hSPB,hTPB] at key
    exact key
  · refine ⟨buf, ?_, fa.items⟩
    show (noopRetired R.frame).state.storage.lookup vc.R = _
    rw [same.lookup]; exact fa.vfound



set_option maxHeartbeats 4000000 in
-- A call whose body is in the straight-line fragment with one read-only vector parameter (location slot 0).
theorem call_vecw (vc : VCtx) (w : Bool) (hw : w = true → vc.wV = true ∧ vc.flag = true) (caller : NState) (prog : NProgram) (args : List NArgument) (Sinit : NState)
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
      ScalarPost3 caller Sinit res kn extra (r.ps.mem.take caller.scalars.memory.length) r.wk vc.R r.vec := by
  obtain ⟨SPB,hSPB⟩ : ∃ SPB, SPB = max (max Sinit.scalars.peak Sinit.peak)
    ((callerP caller).length+12-caller.scalars.baseMemory+100) := ⟨_,rfl⟩
  obtain ⟨TPB,hTPB⟩ : ∃ TPB, TPB = max caller.frame.state.storage.peak (caller.frame.state.liveSpace+1) := ⟨_,rfl⟩
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
  · have hmemLen : (r.ps.mem.take caller.scalars.memory.length).length = caller.scalars.memory.length := by
      simp; omega
    exact scalar_post3 caller Sinit step.state kn extra (Sinit.scalars.work+r.cost) hSPB hTPB takeEq.symm.symm hmemLen
      qsD.base base sPeak vc hL0 hT0 hN (faD.wk_eq (by omega)) cqD (by
      have := cqD.work
      show step.state.scalars.work+1 ≤ _
      omega)


theorem finish_unit (caller R : NState)
    (cond : caller.scalars.memory.length ≤ R.scalars.memory.length ∧
      (R.scalars.memory.take caller.scalars.memory.length).map Cell.type = caller.scalars.memory.map Cell.type)
    (valid : R.frame.state.wellFormed = true) (fresh : ∀ owner, R.frame.state.forest.context owner ≠ some R.scope) :
    finish caller R .unit none = some (finS caller R,Ret.unit) := by
  have retired := retireScope_fresh R.frame R.scope valid fresh
  unfold finish
  rw [if_pos cond]
  simp only [retired,Bind.bind,Option.bind]
  rfl

set_option maxHeartbeats 4000000 in
-- A call whose body is in the straight-line fragment with one read-only vector parameter (location slot 0).
theorem call_vecw_unit (vc : VCtx) (w : Bool) (hw : w = true → vc.wV = true ∧ vc.flag = true) (caller : NState) (prog : NProgram) (args : List NArgument) (Sinit : NState)
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
    (hbody : WrV w prog.body = true) (fu : Nat) (r : PRW) (hexec : pexecW vc.ty fu prog.body ⟨M,bs⟩ vec0 = some r) 
    (hret : r.ret = none) (hres : prog.result = ResultKind.unit)
    (hneed : r.need ≤ (callerP caller).length+112) (hlive0 : M.length+bs.length ≤ (callerP caller).length+100)
    (kn extra : Nat) (hwork : Sinit.scalars.work+r.cost+1 ≤ caller.scalars.work+kn+extra) :
    ∃ fuel res, prog.callFuel fuel caller args = .finished (res,Ret.unit) ∧
      ScalarPost3 caller Sinit res kn extra (r.ps.mem.take caller.scalars.memory.length) r.wk vc.R r.vec := by
  obtain ⟨SPB,hSPB⟩ : ∃ SPB, SPB = max (max Sinit.scalars.peak Sinit.peak)
    ((callerP caller).length+12-caller.scalars.baseMemory+100) := ⟨_,rfl⟩
  obtain ⟨TPB,hTPB⟩ : ∃ TPB, TPB = max caller.frame.state.storage.peak (caller.frame.state.liveSpace+1) := ⟨_,rfl⟩
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
  have fin := finish_unit caller step.state cond faD.valid fresh
  refine ⟨fuel,finS caller step.state,?_,?_⟩
  · unfold NProgram.callFuel
    simp only [hprep,Proofs.CppLoop.liftChecked,Proofs.CppLoop.Outcome.bind]
    have ret' : step.returned = none := by rw [ret,hret]; rfl
    simp only [Bind.bind,Proofs.CppLoop.Outcome.bind,hrun,brk,hres,ret',fin]
    simp
  · have hmemLen : (r.ps.mem.take caller.scalars.memory.length).length = caller.scalars.memory.length := by
      simp; omega
    exact scalar_post3 caller Sinit step.state kn extra (Sinit.scalars.work+r.cost) hSPB hTPB takeEq.symm.symm hmemLen
      qsD.base base sPeak vc hL0 hT0 hN (faD.wk_eq (by omega)) cqD (by
      have := cqD.work
      show step.state.scalars.work+1 ≤ _
      omega)


theorem ScalarPost3.relax {caller Sinit res : NState} {kn extra kn' extra' : Nat} {mem : List Cell} {wk wk' V : Nat}
    {items : List Int} (h : ScalarPost3 caller Sinit res kn extra mem wk V items) (hk : kn ≤ kn') (he : extra ≤ extra')
    (hw : wk ≤ wk') : ScalarPost3 caller Sinit res kn' extra' mem wk' V items :=
  ⟨h.valid,h.objects,h.live,by have := h.storageWork; omega,h.rwLength,h.slots,h.scope,h.bindings,h.scalarMemory,
    h.storagePeak,by have := h.scalarWork; omega,h.scalarPeak,h.outerPeak,h.vector⟩

end Proofs.VecWriteCall
