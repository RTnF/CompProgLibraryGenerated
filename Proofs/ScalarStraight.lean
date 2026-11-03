import Proofs.StraightLine
import Proofs.ScalarCall

namespace Proofs.ScalarStraight
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.Mod61Body
open Proofs.CppState (Cell)

set_option maxHeartbeats 4000000 in
-- A call whose body is in the straight-line scalar fragment: the result and the leftover state come from
-- the pure executor `pexec`.
theorem call_scalar (caller : NState) (prog : NProgram) (args : List NArgument) (Sinit : NState)
    (M : List Cell) (bs : List CppState.Binding)
    (hprep : prepare caller prog.parameters args = some Sinit)
    (sSlots : Sinit.slots = ssl bs.length) (sMem : Sinit.scalars.memory = M) (sBind : Sinit.scalars.bindings = bs)
    (sBase : Sinit.scalars.baseMemory = caller.scalars.baseMemory) (sScope : Sinit.scope = caller.scope+1)
    (sFrame : Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩)
    (sPeak : caller.scalars.peak ≤ Sinit.scalars.peak)
    (hMlen : caller.scalars.memory.length ≤ M.length)
    (hMtypes : (M.take caller.scalars.memory.length).map Cell.type = caller.scalars.memory.map Cell.type)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (hbody : Scalar prog.body = true) (fu : Nat) (r : PR) (hexec : pexec fu prog.body ⟨M,bs⟩ = some r) (v : Int)
    (hret : r.ret = some v) (ty : Ty) (hres : prog.result = ResultKind.scalar ty) (hv : ty.valid v = true)
    (hneed : r.need ≤ (callerP caller).length+112) (hlive0 : M.length+bs.length ≤ (callerP caller).length+100)
    (kn extra : Nat) (hwork : Sinit.scalars.work+r.cost+1 ≤ caller.scalars.work+kn+extra) :
    ∃ fuel res, prog.callFuel fuel caller args = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res kn extra (r.ps.mem.take caller.scalars.memory.length) := by
  have sState : Sinit.frame.state = caller.frame.state := by rw [sFrame]
  have sRw : Sinit.frame.rootWritable = caller.frame.rootWritable := by rw [sFrame]
  have sFb : Sinit.frame.bindings = [] := by rw [sFrame]
  obtain ⟨SPB,hSPB⟩ : ∃ SPB, SPB = max (max Sinit.scalars.peak Sinit.peak)
    ((callerP caller).length+12-caller.scalars.baseMemory+100) := ⟨_,rfl⟩
  obtain ⟨TPB,hTPB⟩ : ∃ TPB, TPB = max caller.frame.state.storage.peak caller.frame.state.liveSpace := ⟨_,rfl⟩
  have hB : caller.scalars.baseMemory ≤ (callerP caller).length := by
    have : caller.scalars.memory.length ≤ (callerP caller).length := by simp [callerP]
    omega
  have qs : QS Sinit [] caller.scalars.baseMemory (caller.scope+1) M bs (ssl bs.length) :=
    ⟨sSlots,by rw [sMem]; simp,sBind,sBase,sScope⟩
  have fa : FA Sinit.frame caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope+1)
      caller.frame.state.storage.objects.length := by
    refine ⟨by rw [sState]; exact valid,by rw [sState,sRw]; exact lengths,by rw [sState],by rw [sState],?_,sFb,by rw [sState]⟩
    intro owner c h
    rw [sState] at h
    have := strict owner c h
    omega
  have cq : Cq SPB TPB Sinit.scalars.work Sinit := by
    refine ⟨Nat.le_refl _,?_,?_,?_⟩
    · show Sinit.scalars.peak ≤ SPB; rw [hSPB]; omega
    · show Sinit.frame.state.storage.peak ≤ TPB; rw [hTPB,sState]; omega
    · show Sinit.peak ≤ SPB + TPB; rw [hSPB]; omega
  have run := sound prog.body hbody fu ⟨M,bs⟩ r hexec (L0 := caller.frame.state.liveSpace)
    (T0 := caller.frame.state.storage.work) (N := caller.frame.state.storage.objects.length)
    (scq := caller.scope+1) (SPB := SPB) (TPB := TPB) (W := Sinit.scalars.work) Sinit qs fa cq
    (by show caller.scalars.baseMemory ≤ M.length; omega)
    (by show M.length+bs.length ≤ SPB+caller.scalars.baseMemory; rw [hSPB]; omega)
    (by rw [hSPB]; omega) (Nat.le_refl _) (by rw [hTPB]; omega)
  obtain ⟨fuel,step,hrun,ret,brk,qsD,faD,cqD⟩ := run
  have ext := pexec_ext prog.body hbody fu ⟨M,bs⟩ r hexec
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
    exact scalar_post2 caller Sinit step.state kn extra (Sinit.scalars.work+r.cost) hSPB hTPB takeEq.symm.symm hmemLen
      qsD.base base sPeak faD cqD (by
      have := cqD.work
      show step.state.scalars.work+1 ≤ _
      omega)

end Proofs.ScalarStraight
