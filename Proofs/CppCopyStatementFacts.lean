import Proofs.CppCopyStatement
import Proofs.CppFrameCopy

namespace Proofs.CppCopyStatementFacts
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppVector
open Proofs.CppFrameCopy Proofs.CppCopyStatement Proofs.CppFrameExtension

-- The expression's temporary aliases are released before binding the new root.
def result (caller next : NState) (source : Buffer Value) (ty : Ty) (writable : Bool) : NState :=
  let released := next.release caller
  ({released with
    frame := copiedFrame released.frame source ty released.scope writable
    slots := released.slots++[.vector released.frame.bindings.length]} : NState).charge 1 0

theorem completes (caller next : NState) (container : Container) (index : Nat)
    (binding : Binding) (source : Buffer Value) (ty : Ty) (writable : Bool)
    (evaluated : container.eval caller = some (next,index))
    (resolved : next.frame.resolve index (.integer ty) = some (binding,source))
    (lengths : next.frame.rootWritable.length = next.frame.state.forest.objects.length)
    (supported : Proofs.CppVectorBindings.supported ty) :
    run caller container ty writable = some ⟨result caller next source ty writable,none,false⟩ ∧
    Extends (next.release caller).frame (result caller next source ty writable).frame := by
  obtain ⟨tag,object⟩ := resolve_object next.frame index ty binding source resolved
  have releasedObject : (next.release caller).frame.object binding.owner (.integer ty) = some (source,tag) := object
  have releasedLengths : (next.release caller).frame.rootWritable.length =
      (next.release caller).frame.state.forest.objects.length := lengths
  have copied := copy_owner_runs (next.release caller).frame binding.owner ty (next.release caller).scope
    writable source tag releasedLengths supported releasedObject
  refine ⟨?_,?_⟩
  · exact run_of_steps caller next container ty writable index (next.release caller).frame.bindings.length
      binding source _ evaluated resolved copied
  · exact copy_owner_extends (next.release caller).frame binding.owner ty (next.release caller).scope
      writable source tag releasedLengths supported releasedObject

-- Cost after evaluating the source. Source expression work/temporaries are
-- retained in `next`, so they are not mistaken for the direct copyClass cost.
theorem result_cost (caller next : NState) (source : Buffer Value) (ty : Ty) (writable : Bool)
    (valid : next.frame.state.wellFormed = true) :
    (result caller next source ty writable).work = next.work+source.items.length+2 ∧
    (result caller next source ty writable).frame.state.liveSpace = next.frame.state.liveSpace+source.items.length+1 ∧
    (result caller next source ty writable).frame.state.storage.peak =
      max next.frame.state.storage.peak
        (next.frame.state.liveSpace+source.items.length+2-next.frame.state.storage.baseSpace) := by
  obtain ⟨work,live,peak⟩ := Proofs.CppNestedCopy.clone_cost next.frame.state source ty next.scope
    (wellFormed_parts next.frame.state valid).1
  refine ⟨?_,live,peak⟩
  simp [result,NState.work,NState.charge,NState.observe,NState.release,Proofs.CppState.State.observe,
    copiedFrame,Proofs.CppNestedCopy.cloned,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem keeps_read (caller next : NState) (container : Container) (index : Nat)
    (binding : Binding) (source : Buffer Value) (ty : Ty) (writable : Bool)
    (evaluated : container.eval caller = some (next,index))
    (resolved : next.frame.resolve index (.integer ty) = some (binding,source))
    (lengths : next.frame.rootWritable.length = next.frame.state.forest.objects.length)
    (supported : Proofs.CppVectorBindings.supported ty)
    (reference : Reference) (value : Int)
    (read : (next.release caller).frame.read reference = some value) :
    (result caller next source ty writable).frame.read reference = some value :=
  read_kept _ _ (completes caller next container index binding source ty writable
    evaluated resolved lengths supported).2 reference value read

theorem keeps_scalar (caller next : NState) (source : Buffer Value) (element : Ty) (writable : Bool)
    (slot : Nat) (ty : Ty) (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
    (actual : next.scalarCell slot ty = some (binding,cell)) :
    (result caller next source element writable).scalarCell slot ty = some (binding,cell) := by
  unfold NState.scalarCell at actual
  obtain ⟨index,slotFound,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ actual
  obtain ⟨b,found,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  obtain ⟨c,cellFound,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  have slotBound : slot < next.slots.length := by
    by_cases inside : slot < next.slots.length
    · exact inside
    · have missing := List.getElem?_eq_none_iff.mpr (show next.slots.length ≤ slot by omega)
      simp [NState.scalarSlot,missing] at slotFound
  have slotOut : (result caller next source element writable).scalarSlot slot = some index := by
    simpa only [result,NState.charge,NState.observe,NState.release,NState.scalarSlot,
      List.getElem?_append_left slotBound] using slotFound
  have bindingOut : (result caller next source element writable).scalars.bindings[index]? = some b := found
  have cellOut : (result caller next source element writable).scalars.memory[b.address]? = some c := cellFound
  simpa only [NState.scalarCell,slotOut,bindingOut,cellOut,Bind.bind,Option.bind] using rest

end Proofs.CppCopyStatementFacts
