import Proofs.DynamicFamilyInit

namespace Proofs.DynamicPrepare
open Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppNestedCall
open Proofs.CppRowsFrame Proofs.CppRootModel Proofs.MultiVecDynamic Proofs.DynamicExpr Proofs.DynamicRealizes
open Proofs.DynamicFamilyInit

def initial (caller last : NState) (parameters : List Proofs.CppVectorBindings.Parameter) : NState :=
  let released := last.release caller
  let scalars : Proofs.CppState.State := {released.scalars with
    memory := released.scalars.memory ++ List.replicate
      (released.scalars.bindings.length+released.frame.bindings.length) ⟨⟨1,false,true⟩,0⟩,
    bindings := [],work := released.scalars.work+1+parameters.length}
  (⟨scalars,{released.frame with bindings := []},[],caller.scope+1,released.peak⟩ : NState).observe

-- This is the actual prepare implementation, including argument-temporary
-- release and the scalar cells reserved to account for the caller's locals.
theorem prepare_eq (caller last : NState) (parameters : List Proofs.CppVectorBindings.Parameter)
    (arguments : List NArgument) (rs : List Resolved) (valid : caller.frame.state.wellFormed = true)
    (resolved : resolveAll caller parameters arguments = some (last,rs)) :
    prepare caller parameters arguments = bindAll (initial caller last parameters) rs := by
  simp only [prepare,valid,ite_true,resolved,Bind.bind,Option.bind]
  rfl

theorem initial_family {params : List Parameter} {h : Heap} {m : Resources}
    (caller last : NState) (parameters : List Proofs.CppVectorBindings.Parameter)
    (family : Family params h last.frame m) : Family [] h (initial caller last parameters).frame m := by
  refine ⟨family.valid,family.models,family.lengths,by simp,by simp,by simp,by simp,?_⟩
  exact ⟨family.measured.live,family.measured.work,family.measured.peak,family.measured.count,family.measured.base⟩

theorem prepared_family {params : List Parameter} {h : Heap} {m : Resources}
    (caller last callee : NState) (parameters : List Proofs.CppVectorBindings.Parameter)
    (arguments : List NArgument) (rs : List Resolved)
    (valid : caller.frame.state.wellFormed = true)
    (resolved : resolveAll caller parameters arguments = some (last,rs))
    (family : Family params h last.frame m) (compatible : ∀ r ∈ rs, Compatible h r)
    (run : prepare caller parameters arguments = some callee) :
    Family (describe last.frame.rootWritable 0 rs) h callee.frame m ∧
      Realizes (describe last.frame.rootWritable 0 rs) (snapshot callee) (DynamicContents.eraseHeap h) callee ∧
      callee.frame.state = last.frame.state ∧ callee.frame.rootWritable = last.frame.rootWritable ∧
      callee.scope = caller.scope+1 := by
  rw [prepare_eq caller last parameters arguments rs valid resolved] at run
  obtain ⟨after,state,flags,scope⟩ := bind_all (initial_family caller last parameters family) rs compatible run
  have final : Family (describe last.frame.rootWritable 0 rs) h callee.frame m := by simpa [initial] using after
  exact ⟨final,⟨rfl,h,m,final,rfl⟩,state,flags,scope⟩

end Proofs.DynamicPrepare
