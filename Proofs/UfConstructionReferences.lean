import Proofs.CppFrameExtension
import Proofs.UfConstructionPreserve

namespace Proofs.UfConstructionReferences
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedVectorStore Proofs.CppVectorOwnership Proofs.CppRootModel
open Proofs.UfConstructionExport Proofs.UfConstructionPreserve Proofs.CppConstructorFinish
open Proofs.CppFrameExtension
open Proofs.DoublingNested (i32)

theorem extension_of_added (f g : Frame) (binding : Binding)
    (valid : f.state.wellFormed = true) (newValid : g.state.wellFormed = true)
    (lengths : f.rootWritable.length = f.state.forest.objects.length)
    (kept : ∀ owner, owner < f.state.storage.objects.length →
      g.state.storage.lookup owner = f.state.storage.lookup owner ∧ g.state.forest.lookup owner = f.state.forest.lookup owner)
    (flags : g.rootWritable = f.rootWritable++[true])
    (bindings : g.bindings = f.bindings++[binding])
    (grown : g.state.forest.objects.length = f.state.forest.objects.length+1) : Extends f g := by
  have lens := (wellFormed_parts f.state valid).1
  refine ⟨valid,newValid,lengths,?_,?_,?_,?_,?_⟩
  · simp [flags,grown,lengths]
  · intro owner inside
    exact (kept owner (by omega)).2
  · intro owner inside
    exact (kept owner inside).1
  · intro owner inside
    rw [flags,List.getElem?_append_left inside]
  · intro slot inside
    rw [bindings,List.getElem?_append_left inside]

-- The usual scope upper bound entails the constructor's old-scope condition.
theorem oldScopes_of_bound (caller : NState)
    (bound : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope) :
    OldScopes caller := by
  intro owner inside same
  have impossible := bound owner (caller.scope+1) same
  omega

theorem construct_sized (caller : NState) (heap : Heap)
    (valid : caller.frame.state.wellFormed = true) (models : HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (scopes : OldScopes caller)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (type : en.resultType = i32) (value : en.denote (Proofs.CppNestedEval.envOf caller) = some (n : Int)) :
    ∃ out, Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 caller [.value en]
        (vectorField true) (.integer i32) (fields true) = .finished (out,reference caller 2) ∧
      Initialized caller out (List.replicate n (-1)) n n ∧ Extends caller.frame out.frame ∧
      (∀ ref v, caller.frame.read ref = some v → out.frame.read ref = some v) := by
  obtain ⟨out,ran,initialized,kept,newBuffer,flags,bindings,grown⟩ :=
    Proofs.UfConstructionPreserve.construct_sized caller heap valid models lengths scopes en n small scalar type value
  have extension := extension_of_added caller.frame out.frame _ valid initialized.1.valid lengths kept flags bindings grown
  exact ⟨out,ran,initialized,extension,fun ref v read => read_kept _ _ extension ref v read⟩

theorem construct_default (caller : NState) (heap : Heap)
    (valid : caller.frame.state.wellFormed = true) (models : HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (scopes : OldScopes caller) :
    ∃ out, Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 caller []
        (vectorField false) (.integer i32) (fields false) = .finished (out,reference caller 2) ∧
      Initialized caller out [] 0 0 ∧ Extends caller.frame out.frame ∧
      (∀ ref v, caller.frame.read ref = some v → out.frame.read ref = some v) := by
  obtain ⟨out,ran,initialized,kept,newBuffer,flags,bindings,grown⟩ :=
    Proofs.UfConstructionPreserve.construct_default caller heap valid models lengths scopes
  have extension := extension_of_added caller.frame out.frame _ valid initialized.1.valid lengths kept flags bindings grown
  exact ⟨out,ran,initialized,extension,fun ref v read => read_kept _ _ extension ref v read⟩

end Proofs.UfConstructionReferences
