import Proofs.DynamicControlPreserve

namespace Proofs.DynamicCallAuto
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.MultiVecDynamic
open Proofs.DynamicExpr Proofs.DynamicRealizes Proofs.DynamicControlBridge Proofs.DynamicFinish Proofs.DynamicPreserve
open Proofs.CppLoop (Outcome liftChecked)

-- Shape and scalar prefix checks follow from the successful pure body.
-- Physical allocation authority and ownership remain body invariants.
theorem sound (params : List Parameter) (st : DynamicStmt.State) (caller : NState)
    (real : Realizes params st.locals st.contents caller) (program : NProgram) (arguments : List NArgument)
    (rs : List Resolved) (args : DynamicArguments.resolveAll params st program.parameters arguments = some rs)
    (body : ∀ initial, CppNestedCall.prepare caller program.parameters arguments = some initial →
      Realizes (DynamicFamilyInit.describe caller.frame.rootWritable 0 rs) (snapshot initial) st.contents initial →
      Runs (DynamicFamilyInit.describe caller.frame.rootWritable 0 rs) program.body ⟨snapshot initial,st.contents⟩ initial
        (fun p a => p.breaking = false ∧ ∃ value,
          resultValue program.result p.returned = some value ∧
          (∃ extra, a.state.frame.rootWritable = caller.frame.rootWritable ++ extra) ∧
          (∀ owner, a.state.frame.state.forest.context owner ≠ some a.state.scope))) :
    ∃ (fuel : Nat) (final : DynamicStmt.State) (next : NState) (value : Ret),
      program.callFuel fuel caller arguments = .finished (next,value) ∧ Realizes params final.locals final.contents next := by
  obtain ⟨initial,prepared,initialReal,_,_,_,memory⟩ := DynamicPrepareExists.prepare params st caller real program.parameters arguments rs args
  obtain ⟨fuel,p,a,pRun,ran,matched,notBreaking,value,accepted,flags,fresh⟩ := (body initial prepared initialReal).aligned
  have preserved := DynamicControlPreserve.run _ fuel program.body ⟨snapshot initial,st.contents⟩ p pRun
  have initialPrefix : TypesPrefix st.locals (snapshot initial) := by
    apply TypesPrefix.memory
    obtain ⟨extra,memory⟩ := memory
    refine ⟨extra,?_⟩
    have sm := congrArg Locals.memory real.locals
    change caller.scalars.memory = st.locals.memory at sm
    change initial.scalars.memory = st.locals.memory ++ extra
    rw [memory,sm]
  obtain ⟨final,pureFinish⟩ := finish_exists st p.state (initialPrefix.trans preserved.2) program.result p.returned value accepted
  obtain ⟨done,finalReal,_⟩ := DynamicFinish.sound params _ st p.state final caller a.state real matched.state program.result p.returned value pureFinish preserved.1 flags fresh
  have breaking : a.breaking = false := matched.breaking.trans notBreaking
  refine ⟨fuel,final,restored caller a.state,value,?_,finalReal⟩
  simp [NProgram.callFuel,prepared,ran,breaking,matched.returned,done,liftChecked,bind,Outcome.bind]

end Proofs.DynamicCallAuto
