import Proofs.MultiVec
import Proofs.VecWriteCall

namespace Proofs.MultiVecCall
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.Mod61Body Proofs.VecExpr Proofs.VecStraight
open Proofs.VecCall Proofs.VecWrite Proofs.VecWriteCall Proofs.MultiVec
open Proofs.CppState (Cell)

structure ScalarPostM (mv : MV) (caller Sinit res : NState) (kn extra : Nat) (mem : List Cell) (wk : Nat) (vv : Nat → List Int) : Prop where
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
  vector : ∀ k, k < mv.nv → ∃ buf', res.frame.state.storage.lookup (mv.R k) = some buf' ∧ buf'.items = (vv k).map Value.integer

theorem scalar_postM (caller Sinit R : NState) (kn extra W : Nat) {mem : List Cell} {SPB TPB : Nat}
    (hSPB : SPB = max (max Sinit.scalars.peak Sinit.peak) ((callerP caller).length+12-caller.scalars.baseMemory+100))
    (hTPB : TPB = max caller.frame.state.storage.peak (caller.frame.state.liveSpace+1))
    (htake : R.scalars.memory.take caller.scalars.memory.length = mem) (hmemLen : mem.length = caller.scalars.memory.length)
    (hbase : R.scalars.baseMemory = caller.scalars.baseMemory)
    (hbm : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (spC : caller.scalars.peak ≤ Sinit.scalars.peak)
    (mv : MV) (hL0 : mv.L0 = caller.frame.state.liveSpace) (hT0 : mv.T0 = caller.frame.state.storage.work)
    (hN : mv.N = caller.frame.state.storage.objects.length) {vv : Nat → List Int} {bb : Nat → Buffer Value} {wk : Nat} (fa : FWM mv vv bb wk R.frame)
    (cq : Cq SPB TPB W R) (hw : R.scalars.work+1 ≤ caller.scalars.work+kn+extra) :
    ScalarPostM mv caller Sinit (finS caller R) kn extra mem wk vv := by
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
  · intro k hk
    refine ⟨bb k, ?_, fa.items k hk⟩
    show (noopRetired R.frame).state.storage.lookup (mv.R k) = _
    rw [same.lookup]; exact fa.vfound k hk



set_option maxHeartbeats 4000000 in
-- A call whose body is in the straight-line fragment with `mv.nv` flat vector parameters (location slots `0 .. nv-1`).
theorem call_vecm (mv : MV) (w : Nat → Bool) (hw : ∀ k, w k = true → mv.wV k = true ∧ mv.flag k = true) (caller : NState) (prog : NProgram) (args : List NArgument) (Sinit : NState)
    (M : List Cell) (bs : List CppState.Binding)
    (hprep : prepare caller prog.parameters args = some Sinit)
    (sSlots : Sinit.slots = slN mv.nv bs.length) (sMem : Sinit.scalars.memory = M) (sBind : Sinit.scalars.bindings = bs)
    (sBase : Sinit.scalars.baseMemory = caller.scalars.baseMemory) (sScope : Sinit.scope = caller.scope+1)
    (sState : Sinit.frame.state = caller.frame.state) (sRw : Sinit.frame.rootWritable = caller.frame.rootWritable)
    {vv0 : Nat → List Int} {bb0 : Nat → Buffer Value} (fwS : FWM mv vv0 bb0 0 Sinit.frame) (hL0 : mv.L0 = caller.frame.state.liveSpace)
    (hT0 : mv.T0 = caller.frame.state.storage.work) (hN : mv.N = caller.frame.state.storage.objects.length)
    (hsc : mv.sc = caller.scope+1)
    (sPeak : caller.scalars.peak ≤ Sinit.scalars.peak)
    (hMlen : caller.scalars.memory.length ≤ M.length)
    (hMtypes : (M.take caller.scalars.memory.length).map Cell.type = caller.scalars.memory.map Cell.type)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (hbody : WrM w prog.body = true) (fu : Nat) (r : PRM) (hexec : pexecM mv fu prog.body ⟨M,bs⟩ vv0 = some r) (v : Int)
    (hret : r.ret = some v) (ty : Ty) (hres : prog.result = ResultKind.scalar ty) (hv : ty.valid v = true)
    (hneed : r.need ≤ (callerP caller).length+112) (hlive0 : M.length+bs.length ≤ (callerP caller).length+100)
    (kn extra : Nat) (hwork : Sinit.scalars.work+r.cost+1 ≤ caller.scalars.work+kn+extra) :
    ∃ fuel res, prog.callFuel fuel caller args = .finished (res,.scalar v) ∧
      ScalarPostM mv caller Sinit res kn extra (r.ps.mem.take caller.scalars.memory.length) r.wk r.vv := by
  obtain ⟨SPB,hSPB⟩ : ∃ SPB, SPB = max (max Sinit.scalars.peak Sinit.peak)
    ((callerP caller).length+12-caller.scalars.baseMemory+100) := ⟨_,rfl⟩
  obtain ⟨TPB,hTPB⟩ : ∃ TPB, TPB = max caller.frame.state.storage.peak (caller.frame.state.liveSpace+1) := ⟨_,rfl⟩
  have hB : caller.scalars.baseMemory ≤ (callerP caller).length := by
    have : caller.scalars.memory.length ≤ (callerP caller).length := by simp [callerP]
    omega
  have qs : QS Sinit [] caller.scalars.baseMemory (caller.scope+1) M bs (slN mv.nv bs.length) :=
    ⟨sSlots,by rw [sMem]; simp,sBind,sBase,sScope⟩
  have cq : Cq SPB TPB Sinit.scalars.work Sinit := by
    refine ⟨Nat.le_refl _,?_,?_,?_⟩
    · show Sinit.scalars.peak ≤ SPB; rw [hSPB]; omega
    · show Sinit.frame.state.storage.peak ≤ TPB; rw [hTPB,sState]; omega
    · show Sinit.peak ≤ SPB + TPB; rw [hSPB]; omega
  have run := soundM mv w hw prog.body hbody fu ⟨M,bs⟩ vv0 r hexec (SPB := SPB) (TPB := TPB) (W := Sinit.scalars.work) (wk := 0)
    (bb := bb0) Sinit qs fwS cq
    (by show caller.scalars.baseMemory ≤ M.length; omega)
    (by show M.length+bs.length ≤ SPB+caller.scalars.baseMemory; rw [hSPB]; omega)
    (by rw [hSPB]; omega) (by omega) (by rw [hTPB,hL0]; omega)
  obtain ⟨fuel,step,hrun,ret,brk,qsD,⟨bbD,faD⟩,cqD⟩ := run
  have ext := pexecM_ext mv w prog.body hbody fu ⟨M,bs⟩ vv0 r hexec
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
    exact scalar_postM caller Sinit step.state kn extra (Sinit.scalars.work+r.cost) hSPB hTPB takeEq.symm.symm hmemLen
      qsD.base base sPeak mv hL0 hT0 hN (faD.wk_eq (by omega)) cqD (by
      have := cqD.work
      show step.state.scalars.work+1 ≤ _
      omega)


set_option maxHeartbeats 4000000 in
-- A call whose body is in the straight-line fragment with `mv.nv` flat vector parameters (location slots `0 .. nv-1`).
theorem call_vecm_unit (mv : MV) (w : Nat → Bool) (hw : ∀ k, w k = true → mv.wV k = true ∧ mv.flag k = true) (caller : NState) (prog : NProgram) (args : List NArgument) (Sinit : NState)
    (M : List Cell) (bs : List CppState.Binding)
    (hprep : prepare caller prog.parameters args = some Sinit)
    (sSlots : Sinit.slots = slN mv.nv bs.length) (sMem : Sinit.scalars.memory = M) (sBind : Sinit.scalars.bindings = bs)
    (sBase : Sinit.scalars.baseMemory = caller.scalars.baseMemory) (sScope : Sinit.scope = caller.scope+1)
    (sState : Sinit.frame.state = caller.frame.state) (sRw : Sinit.frame.rootWritable = caller.frame.rootWritable)
    {vv0 : Nat → List Int} {bb0 : Nat → Buffer Value} (fwS : FWM mv vv0 bb0 0 Sinit.frame) (hL0 : mv.L0 = caller.frame.state.liveSpace)
    (hT0 : mv.T0 = caller.frame.state.storage.work) (hN : mv.N = caller.frame.state.storage.objects.length)
    (hsc : mv.sc = caller.scope+1)
    (sPeak : caller.scalars.peak ≤ Sinit.scalars.peak)
    (hMlen : caller.scalars.memory.length ≤ M.length)
    (hMtypes : (M.take caller.scalars.memory.length).map Cell.type = caller.scalars.memory.map Cell.type)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (hbody : WrM w prog.body = true) (fu : Nat) (r : PRM) (hexec : pexecM mv fu prog.body ⟨M,bs⟩ vv0 = some r) 
    (hret : r.ret = none) (hres : prog.result = ResultKind.unit)
    (hneed : r.need ≤ (callerP caller).length+112) (hlive0 : M.length+bs.length ≤ (callerP caller).length+100)
    (kn extra : Nat) (hwork : Sinit.scalars.work+r.cost+1 ≤ caller.scalars.work+kn+extra) :
    ∃ fuel res, prog.callFuel fuel caller args = .finished (res,Ret.unit) ∧
      ScalarPostM mv caller Sinit res kn extra (r.ps.mem.take caller.scalars.memory.length) r.wk r.vv := by
  obtain ⟨SPB,hSPB⟩ : ∃ SPB, SPB = max (max Sinit.scalars.peak Sinit.peak)
    ((callerP caller).length+12-caller.scalars.baseMemory+100) := ⟨_,rfl⟩
  obtain ⟨TPB,hTPB⟩ : ∃ TPB, TPB = max caller.frame.state.storage.peak (caller.frame.state.liveSpace+1) := ⟨_,rfl⟩
  have hB : caller.scalars.baseMemory ≤ (callerP caller).length := by
    have : caller.scalars.memory.length ≤ (callerP caller).length := by simp [callerP]
    omega
  have qs : QS Sinit [] caller.scalars.baseMemory (caller.scope+1) M bs (slN mv.nv bs.length) :=
    ⟨sSlots,by rw [sMem]; simp,sBind,sBase,sScope⟩
  have cq : Cq SPB TPB Sinit.scalars.work Sinit := by
    refine ⟨Nat.le_refl _,?_,?_,?_⟩
    · show Sinit.scalars.peak ≤ SPB; rw [hSPB]; omega
    · show Sinit.frame.state.storage.peak ≤ TPB; rw [hTPB,sState]; omega
    · show Sinit.peak ≤ SPB + TPB; rw [hSPB]; omega
  have run := soundM mv w hw prog.body hbody fu ⟨M,bs⟩ vv0 r hexec (SPB := SPB) (TPB := TPB) (W := Sinit.scalars.work) (wk := 0)
    (bb := bb0) Sinit qs fwS cq
    (by show caller.scalars.baseMemory ≤ M.length; omega)
    (by show M.length+bs.length ≤ SPB+caller.scalars.baseMemory; rw [hSPB]; omega)
    (by rw [hSPB]; omega) (by omega) (by rw [hTPB,hL0]; omega)
  obtain ⟨fuel,step,hrun,ret,brk,qsD,⟨bbD,faD⟩,cqD⟩ := run
  have ext := pexecM_ext mv w prog.body hbody fu ⟨M,bs⟩ vv0 r hexec
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
    exact scalar_postM caller Sinit step.state kn extra (Sinit.scalars.work+r.cost) hSPB hTPB takeEq.symm.symm hmemLen
      qsD.base base sPeak mv hL0 hT0 hN (faD.wk_eq (by omega)) cqD (by
      have := cqD.work
      show step.state.scalars.work+1 ≤ _
      omega)


theorem ScalarPostM.relax {mv : MV} {caller Sinit res : NState} {kn extra kn' extra' : Nat} {mem : List Cell} {wk wk' : Nat} {vv : Nat → List Int}
     (h : ScalarPostM mv caller Sinit res kn extra mem wk vv) (hk : kn ≤ kn') (he : extra ≤ extra')
    (hw : wk ≤ wk') : ScalarPostM mv caller Sinit res kn' extra' mem wk' vv :=
  ⟨h.valid,h.objects,h.live,by have := h.storageWork; omega,h.rwLength,h.slots,h.scope,h.bindings,h.scalarMemory,
    h.storagePeak,by have := h.scalarWork; omega,h.scalarPeak,h.outerPeak,h.vector⟩


end Proofs.MultiVecCall
