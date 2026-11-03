import Proofs.DynamicConstructFill

namespace Proofs.DynamicOwnedLayout
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedProgram Proofs.CppNestedConstruct Proofs.CppNestedStmt Proofs.CppNestedSim
open Proofs.DynamicExpr Proofs.DynamicConstructCore Proofs.DynamicResultValid

theorem bind_root (f frame : Frame) (owner : Nat) (element : Element) (scope : Nat) (wr : Bool) (index : Nat)
    (run : f.bindRoot owner element scope wr = some (frame,index)) :
    frame.state = f.state ∧ frame.rootWritable = f.rootWritable ∧
      frame.bindings.length = f.bindings.length+1 ∧ index = f.bindings.length := by
  unfold Frame.bindRoot at run
  obtain ⟨pair,_,rest⟩ := bind_some _ _ _ run
  obtain ⟨buffer,tag⟩ := pair
  obtain ⟨maximum,_,rest⟩ := bind_some _ _ _ rest
  split at rest
  · have same := Prod.mk.inj (Option.some.inj rest)
    obtain ⟨rfl,rfl⟩ := same
    exact ⟨rfl,rfl,by simp [Frame.addBinding],rfl⟩
  · contradiction

theorem empty (s : NState) (ty : Ty) (wr : Bool) (out : NStep)
    (actual : (NStmt.declareVector ty wr).run s = some out) :
    out.state.frame.bindings.length = s.frame.bindings.length+1 ∧
      out.state.frame.state.storage.objects.length = s.frame.state.storage.objects.length+1 ∧
      snapshot out.state = appended (snapshot s) s.frame.bindings.length := by
  unfold NStmt.run at actual
  obtain ⟨next,allocated,rest⟩ := bind_some _ _ _ actual
  obtain ⟨pair,bound,same⟩ := bind_some _ _ _ rest
  obtain ⟨frame,index⟩ := pair
  have equal := Option.some.inj same
  subst out
  obtain ⟨state,_,bindings,slot⟩ := bind_root _ frame s.frame.state.storage.objects.length (.integer ty) s.scope wr index bound
  refine ⟨bindings,?_,?_⟩
  · change frame.state.storage.objects.length = _
    rw [state]
    exact declareVector_objects_length s.frame.state ty s.scope next allocated
  · change appended (snapshot s) index = _
    rw [slot]

end Proofs.DynamicOwnedLayout
