import Proofs.DynamicFinish

namespace Proofs.DynamicCall
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.DynamicExpr Proofs.DynamicRealizes
open Proofs.MultiVecDynamic Proofs.DynamicControlBridge Proofs.DynamicFinish
open Proofs.CppLoop (Outcome liftChecked)

-- A verified body supplies its scalar prefix, heap signature, authority and
-- scope-exit invariants. The caller need not assume prepare or finish success.
theorem sound (params : List Parameter) (st : DynamicStmt.State) (caller : NState)
    (real : Realizes params st.locals st.contents caller) (program : NProgram) (arguments : List NArgument)
    (rs : List Resolved) (args : DynamicArguments.resolveAll params st program.parameters arguments = some rs)
    (body : ∀ initial, CppNestedCall.prepare caller program.parameters arguments = some initial →
      Realizes (DynamicFamilyInit.describe caller.frame.rootWritable 0 rs) (snapshot initial) st.contents initial →
      Runs (DynamicFamilyInit.describe caller.frame.rootWritable 0 rs) program.body ⟨snapshot initial,st.contents⟩ initial
        (fun p a => p.breaking = false ∧ ∃ final value,
          DynamicFinish.finish st p.state program.result p.returned = some (final,value) ∧
          SameShape st.contents p.state.contents ∧
          (∃ extra, a.state.frame.rootWritable = caller.frame.rootWritable ++ extra) ∧
          (∀ owner, a.state.frame.state.forest.context owner ≠ some a.state.scope))) :
    ∃ (fuel : Nat) (final : DynamicStmt.State) (next : NState) (value : Ret), program.callFuel fuel caller arguments = .finished (next,value) ∧
      Realizes params final.locals final.contents next := by
  obtain ⟨initial,prepared,initialReal,_⟩ := DynamicPrepareExists.prepare params st caller real program.parameters arguments rs args
  obtain ⟨fuel,p,a,_,ran,matched,notBreaking,final,value,finished,shape,flags,fresh⟩ := (body initial prepared initialReal).aligned
  obtain ⟨done,finalReal,_⟩ := DynamicFinish.sound params _ st p.state final caller a.state real matched.state program.result p.returned value finished shape flags fresh
  have breaking : a.breaking = false := matched.breaking.trans notBreaking
  refine ⟨fuel,final,restored caller a.state,value,?_,finalReal⟩
  simp [NProgram.callFuel,prepared,ran,breaking,matched.returned,done,liftChecked,bind,pure,Outcome.bind]

end Proofs.DynamicCall
