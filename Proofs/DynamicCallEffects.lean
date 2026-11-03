import Proofs.DynamicPhysicalEffects

namespace Proofs.DynamicCallEffects
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.MultiVecDynamic
open Proofs.DynamicExpr Proofs.DynamicRealizes Proofs.DynamicControlBridge Proofs.DynamicFinish
open Proofs.DynamicForestEffects Proofs.DynamicPhysicalEffects

-- The physical body certificate retains authority and the callee scope.
-- One caller NoScope fact then supplies the finish ownership condition.
theorem sound (params : List Parameter) (st : DynamicStmt.State) (caller : NState)
    (real : Realizes params st.locals st.contents caller) (program : NProgram) (arguments : List NArgument)
    (rs : List Resolved) (args : DynamicArguments.resolveAll params st program.parameters arguments = some rs)
    (absent : NoScope caller.frame.state.forest (caller.scope+1))
    (body : ∀ initial, CppNestedCall.prepare caller program.parameters arguments = some initial →
      Realizes (DynamicFamilyInit.describe caller.frame.rootWritable 0 rs) (snapshot initial) st.contents initial →
      Runs (DynamicFamilyInit.describe caller.frame.rootWritable 0 rs) program.body ⟨snapshot initial,st.contents⟩ initial
        (fun p a => p.breaking = false ∧ Change initial a.state ∧ ∃ value,
          resultValue program.result p.returned = some value)) :
    ∃ (fuel : Nat) (final : DynamicStmt.State) (next : NState) (value : Ret),
      program.callFuel fuel caller arguments = .finished (next,value) ∧ Realizes params final.locals final.contents next := by
  obtain ⟨prepared0,prepared,_,state,flags,scope,_⟩ := DynamicPrepareExists.prepare params st caller real program.parameters arguments rs args
  apply DynamicCallAuto.sound params st caller real program arguments rs args
  intro initial ran initialReal
  have same : prepared0 = initial := Option.some.inj (prepared.symm.trans ran)
  subst prepared0
  have preparation : Authority caller.frame initial.frame := Authority.same (congrArg Proofs.CppNestedVectorStore.State.forest state) flags
  apply (body initial ran initialReal).mono
  intro p a ⟨notBreaking,effect,value,accepted⟩
  have total := preparation.trans effect.1
  refine ⟨notBreaking,value,accepted,total.1,?_⟩
  change NoScope a.state.frame.state.forest a.state.scope
  rw [effect.2,scope]
  exact total.absent _ absent

end Proofs.DynamicCallEffects
