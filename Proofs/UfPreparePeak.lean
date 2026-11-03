import Proofs.UfConstructionPeak

namespace Proofs.UfPreparePeak
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.DoublingNested Proofs.DoublingCall
open Proofs.DynamicExpr Proofs.DynamicContents Proofs.MultiVecDynamic Proofs.CppRootModel
open Proofs.UfConstructionStage

-- Argument values are copied after caller locals have been reserved. No
-- successful prepare/run is assumed, and existing caller aliases stay outside.
theorem prepare_sized_peak (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (baseline : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (en : NExpr) (n : Int) (scalar : en.scalarOnly = true) (type : en.resultType = i32)
    (value : en.denote (envOf caller) = some n) (nvalid : i32.valid n = true) :
    ∃ init, prepare caller Proofs.UnionFindConstructionInstance.UnionFind_construct1.parameters [.value en] = some init ∧
      snapshot init = ⟨callerP caller++[⟨i32,n⟩],[⟨(callerP caller).length,true⟩],[.scalar 0]⟩ ∧
      init.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧ init.scope = caller.scope+1 ∧
      init.scalars.baseMemory = caller.scalars.baseMemory ∧
      liveS init = liveS caller+caller.frame.bindings.length+2 ∧
      init.scalars.peak ≤ max caller.scalars.peak (liveS caller+caller.frame.bindings.length+en.nodes+2) ∧
      init.peak ≤ max caller.peak (max caller.scalars.peak
        (liveS caller+caller.frame.bindings.length+en.nodes+2)+caller.frame.state.storage.peak) := by
  obtain ⟨q,ran,good⟩ := scalar_eval en caller n scalar value
  obtain ⟨frame,slots,scope,memory,bindings,base⟩ := good.1
  have fs : q.frame.state = caller.frame.state := by rw [frame]
  have fr : q.frame.rootWritable = caller.frame.rootWritable := by rw [frame]
  have fb : q.frame.bindings = caller.frame.bindings := by rw [frame]
  have resolved : resolve caller (.scalar i32 false true) (.value en) = some (q,.scalar i32 true n) := by
    simp [resolve,type,ran]
  have hp : Proofs.UnionFindConstructionInstance.UnionFind_construct1.parameters = [.scalar i32 false true] := rfl
  rw [hp]
  simp [prepare,valid,resolveAll,resolved,bindAll,bindOne,CppState.bindArgument,nvalid,
    snapshot,NState.release,NState.observe,CppState.State.observe,fs,fr,fb,memory,bindings,base,callerP,liveS]
  have scalarPeak := good.2.2.2.2.2.1
  have outerPeak := good.2.2.2.2.2.2.2
  unfold liveS at scalarPeak
  rw [fs] at outerPeak
  all_goals omega

theorem prepare_default_peak (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (baseline : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ init, prepare caller Proofs.UnionFindConstructionInstance.UnionFind_construct0.parameters [] = some init ∧
      snapshot init = ⟨callerP caller,[],[]⟩ ∧
      init.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧ init.scope = caller.scope+1 ∧
      init.scalars.baseMemory = caller.scalars.baseMemory ∧
      liveS init = liveS caller+caller.frame.bindings.length ∧
      init.scalars.peak = caller.scalars.peak ∧
      init.peak = max caller.peak (caller.scalars.peak+caller.frame.state.storage.peak) := by
  have hp : Proofs.UnionFindConstructionInstance.UnionFind_construct0.parameters = [] := rfl
  rw [hp]
  simp [prepare,valid,resolveAll,bindAll,snapshot,NState.release,NState.observe,callerP,liveS]
  omega


end Proofs.UfPreparePeak
