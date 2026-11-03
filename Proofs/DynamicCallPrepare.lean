import Proofs.DynamicResolve

namespace Proofs.DynamicCallPrepare
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppRowsFrame Proofs.CppRootModel
open Proofs.MultiVecDynamic Proofs.DynamicExpr Proofs.DynamicRealizes Proofs.DynamicFamilyInit

-- The caller supplies a pure argument-resolution success and the actual
-- prepare success. No post-resolution Family or view proofs are required.
theorem sound (params : List Parameter) (st : DynamicStmt.State) (caller callee : NState)
    (real : Realizes params st.locals st.contents caller)
    (parameters : List Proofs.CppVectorBindings.Parameter) (arguments : List NArgument) (rs : List Resolved)
    (pure : DynamicArguments.resolveAll params st parameters arguments = some rs)
    (prepared : prepare caller parameters arguments = some callee) :
    ∃ (h : Heap) (m : Resources) (last : NState), DynamicContents.eraseHeap h = st.contents ∧
      CppNestedCall.resolveAll caller parameters arguments = some (last,rs) ∧
      Family params h last.frame m ∧
      Family (describe caller.frame.rootWritable 0 rs) h callee.frame m ∧
      Realizes (describe caller.frame.rootWritable 0 rs) (snapshot callee) st.contents callee ∧
      callee.frame.state = caller.frame.state ∧ callee.frame.rootWritable = caller.frame.rootWritable ∧
      callee.scope = caller.scope+1 := by
  obtain ⟨h,m,family,erased⟩ := real.heap
  obtain ⟨last,resolved,good,ext,lastFamily,compatible,_⟩ :=
    DynamicResolve.all_sound params st h m caller family real parameters arguments rs pure
  obtain ⟨calleeFamily,calleeReal,state,flags,scope⟩ :=
    DynamicPrepare.prepared_family caller last callee parameters arguments rs family.valid resolved lastFamily compatible prepared
  have sameFlags : last.frame.rootWritable = caller.frame.rootWritable := good.2.1
  have finalFamily : Family (describe caller.frame.rootWritable 0 rs) h callee.frame m := by rw [← sameFlags]; exact calleeFamily
  have finalReal : Realizes (describe caller.frame.rootWritable 0 rs) (snapshot callee) st.contents callee :=
    ⟨rfl,h,m,finalFamily,erased⟩
  exact ⟨h,m,last,erased,resolved,lastFamily,finalFamily,finalReal,state.trans good.1,flags.trans sameFlags,scope⟩

end Proofs.DynamicCallPrepare
