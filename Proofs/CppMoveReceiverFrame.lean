import Proofs.CppMoveReceiverLayout
import Proofs.VecWrite

namespace Proofs.CppMoveReceiverFrame
open Proofs.CppScalar Proofs.CppVector Proofs.CppMoveHeaders Proofs.CppMoveFrame
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.VecExpr Proofs.VecWrite

-- Recover a real allocation or the empty-header buffer from source ownership.
theorem current_entry (s : Heap Int) (ty : Ty) (id : Nat) (header : Proofs.CppMoveHeaders.Header)
    (found : s.header id = some header) (readable : Proofs.CppMoveHeaders.readable s header ty.valid = true)
    (unique : Unique s) (covered : OwnsAll s) :
    ∃ buffer, currentBuffer s id header = some buffer ∧
      (entries s ty)[buffer.owner]? = some (some (box buffer,⟨.integer ty,none,some header.scope,[]⟩)) ∧
      buffer.Valid ty.valid ∧ buffer.limit = header.limit ∧
      buffer.owner = header.allocation.getD (s.allocations.length+id) := by
  cases owns : header.allocation with
  | none =>
    let buffer : Buffer Int := ⟨s.allocations.length+id,[],0,header.limit,0⟩
    refine ⟨buffer,?_,?_,?_,rfl,?_⟩
    · simp [currentBuffer,owns,buffer]
    · exact entries_empty s ty id header found owns
    · simp [buffer,Buffer.Valid]
    · simp [buffer]
  | some owner =>
    cases live : s.allocation owner with
    | none => simp [Proofs.CppMoveHeaders.readable,owns,live] at readable
    | some tracked =>
      have facts : tracked.buffer.owner = owner ∧ tracked.buffer.limit = header.limit ∧ tracked.buffer.Valid ty.valid := by
        simpa [Proofs.CppMoveHeaders.readable,owns,live] using readable
      have headerFound := ownerHeader_unique s owner id header unique found owns
        (ownerHeader_exists s owner tracked covered live)
      refine ⟨tracked.buffer,?_,?_,facts.2.2,facts.2.1,?_⟩
      · simp [currentBuffer,owns,live]
      · rw [facts.1]
        exact entries_allocation s ty owner tracked header live headerFound
      · simpa [owns] using facts.1

-- The callee context records the actual initial resource counters and scope.
def context (initial : NState) (ty : Ty) (header : Proofs.CppMoveHeaders.Header)
    (writable : Bool) (buffer : Buffer Int)
    (small : buffer.items.length < 18446744073709551616) : VCtx :=
  ⟨ty,writable,true,buffer.owner,header.scope,box buffer,buffer.items,rfl,by simp,small,
    initial.frame.state.liveSpace,initial.frame.state.storage.work,initial.scope,
    initial.frame.state.storage.objects.length⟩

-- Build the body proof frame from the source entry and actual prepared frame.
theorem fw_from_entry (s : Context) (initial : NState) (ty : Ty) (id : Nat)
    (header : Proofs.CppMoveHeaders.Header) (writable : Bool) (buffer : Buffer Int)
    (found : s.objects.heap.header id = some header)
    (permission : writable = true → header.writable = true)
    (entry : (entries s.objects.heap ty)[buffer.owner]? =
      some (some (box buffer,⟨.integer ty,none,some header.scope,[]⟩)))
    (bufferValid : buffer.Valid ty.valid)
    (limit : buffer.limit = Proofs.CppVectorBindings.sizeLimit ty)
    (small : buffer.items.length < 18446744073709551616)
    (owner : buffer.owner = header.allocation.getD (s.objects.heap.allocations.length+id))
    (supported : Proofs.CppVectorBindings.supported ty)
    (valid : AllocationsValid s.objects.heap ty)
    (state : initial.frame.state = (project s ty).frame.state)
    (roots : initial.frame.rootWritable = (project s ty).frame.rootWritable)
    (bindings : initial.frame.bindings = [viewBinding s.objects ty ⟨id,writable⟩])
    (scope : initial.scope = s.scope+1)
    (contexts : ∀ owner sc, (project s ty).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    FW (context initial ty header writable buffer small) buffer.items (box buffer) 0 initial.frame := by
  have pair := materialize_entry s.objects ty buffer.owner (box buffer) _ entry
  have inside := (List.getElem?_eq_some_iff.mp entry).1
  have bind : viewBinding s.objects ty ⟨id,writable⟩ =
      ⟨buffer.owner,.integer ty,writable,.root header.scope⟩ := by
    simp only [viewBinding,found]
    rw [← owner,view_writable ⟨id,writable⟩ header permission]
  refine ⟨?_,?_,rfl,by simp [context],?_,rfl,?_,?_,?_,?_,rfl,?_,limit,rfl,small⟩
  · rw [state]
    exact materialize_ready s.objects ty supported valid
  · rw [state,roots]
    simp [project,materialize]
  · intro owner sc located
    rw [state] at located
    have bound := contexts owner sc located
    change sc < initial.scope
    rw [scope]
    omega
  · simpa only [context,bind] using bindings
  · rw [state]
    exact pair.2
  · rw [state]
    exact pair.1
  · rw [roots]
    simpa [context,project,materialize] using (List.getElem?_replicate_of_lt inside :
      (List.replicate (entries s.objects.heap ty).length true)[buffer.owner]? = some true)
  · exact box_valid buffer ty bufferValid

end Proofs.CppMoveReceiverFrame
