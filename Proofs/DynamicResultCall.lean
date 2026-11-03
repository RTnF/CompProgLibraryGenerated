import Proofs.DynamicOwnedFinish

namespace Proofs.DynamicResultCall
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.DynamicOwnedState Proofs.DynamicExpr
open Proofs.MultiVecDynamic
open Proofs.CppLoop (Outcome liftChecked)

def initialState (outer : State) (caller initial : NState) (rs : List Resolved) : State :=
  ⟨⟨snapshot initial,outer.core.contents⟩,DynamicFamilyInit.describe caller.frame.rootWritable 0 rs,
    initial.frame.state.storage.objects.length,initial.frame.bindings.length,initial.scope⟩

-- The body sees the freshly prepared parameter layout, including reordered
-- aliases. Its finish certificate restores the caller's original registry.
theorem sound (outer : State) (caller : NState) (real : Realizes outer caller)
    (program : NProgram) (arguments : List NArgument) (rs : List Resolved)
    (args : DynamicArguments.resolveAll outer.params outer.core program.parameters arguments = some rs)
    (body : ∀ initial, CppNestedCall.prepare caller program.parameters arguments = some initial →
      Realizes (initialState outer caller initial rs) initial →
      DynamicResultRuns.Runs program.body (initialState outer caller initial rs) initial
        (fun p a => p.breaking = false ∧ ∃ final value,
          DynamicOwnedFinish.finish outer p.state program.result p.returned = some (final,value) ∧
          ∃ extra, a.state.frame.rootWritable = caller.frame.rootWritable ++ extra)) :
    ∃ (fuel : Nat) (final : State) (next : NState) (value : Ret),
      program.callFuel fuel caller arguments = .finished (next,value) ∧ Realizes final next := by
  obtain ⟨initial,prepared,initialReal,_,_,_,_⟩ :=
    DynamicPrepareExists.prepare outer.params outer.core caller real.data program.parameters arguments rs args
  have strong : Realizes (initialState outer caller initial rs) initial := ⟨initialReal,rfl,rfl,rfl⟩
  obtain ⟨_,fuel,a,ran,p,matched,notBreaking,final,value,pureFinish,flags⟩ := body initial prepared strong
  obtain ⟨frame,next,_,done,after,_⟩ := DynamicOwnedFinish.sound outer p.state final caller a.state real matched.state program.result p.returned value pureFinish flags
  have breaking : a.breaking = false := matched.breaking.trans notBreaking
  have actualFinish : CppNestedCall.finish caller a.state program.result a.returned = some (next,value) := by
    rw [matched.returned]; exact done
  refine ⟨fuel,final,next,value,?_,after⟩
  simp [NProgram.callFuel,prepared,ran,breaking,actualFinish,liftChecked,bind,Outcome.bind]

end Proofs.DynamicResultCall
