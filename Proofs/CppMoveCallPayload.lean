import Proofs.CppMoveCallLayout
import Proofs.CppMoveReceiverFrame

namespace Proofs.CppMoveCallPayload
open Proofs.CppMoveContext Proofs.CppMoveCallLayout Proofs.CppMoveFrame
open Proofs.CppMoveHeaders Proofs.CppMoveReceiverFrame Proofs.CppScalar
open Proofs.CppVector Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedVectorStore

-- Resolve the actual result header, rather than treating a projected binding
-- or an allocation's old payload as the current C++ object value.
theorem call_payload (program : NProgram) (fuel : Nat) (s out : Context) (ty : Ty)
    (arguments : List NArgument) (result : Ret)
    (run : Proofs.CppMoveCallBindings.callFuel program fuel s ty arguments = .finished (out,result))
    (id : Nat) (header : Proofs.CppMoveHeaders.Header)
    (found : s.objects.heap.header id = some header)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap header ty.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (data : Buffer Int) (current : currentBuffer s.objects.heap id header = some data)
    (final : List Int) (buffer : Buffer Value)
    (lookup : (project out ty).frame.state.storage.lookup data.owner = some buffer)
    (items : buffer.items = final.map Value.integer) :
    ∃ next, currentBuffer out.objects.heap id header = some next ∧ next.items = final := by
  obtain ⟨before,beforeCurrent,beforeEntry,beforeValid,beforeLimit,beforeOwner⟩ :=
    current_entry s.objects.heap ty id header found readable unique covered
  have same : before = data := Option.some.inj (beforeCurrent.symm.trans current)
  subst before
  have layout := call_layout program fuel s out ty arguments result run
  have afterFound : out.objects.heap.header id = some header := by
    simpa only [Heap.header,layout.headers] using found
  obtain ⟨next,afterCurrent,entry,valid,limit,owner⟩ := current_entry out.objects.heap ty id header afterFound
    (call_readable program fuel s out ty arguments result run header readable)
    (call_unique program fuel s out ty arguments result run unique)
    (call_ownsAll program fuel s out ty arguments result run covered)
  have sameOwner : next.owner = data.owner := by rw [owner,beforeOwner,layout.allocations]
  have nextLookup : (project out ty).frame.state.storage.lookup data.owner = some (box next) := by
    rw [← sameOwner]
    exact (materialize_entry out.objects ty next.owner (box next) _ entry).1
  have buffers : box next = buffer := Option.some.inj (nextLookup.symm.trans lookup)
  have itemEq : next.items.map Value.integer = final.map Value.integer := by
    change (box next).items = final.map Value.integer
    rw [buffers]
    exact items
  exact ⟨next,afterCurrent,(List.map_inj_right (fun _ _ equal => Value.integer.inj equal)).mp itemEq⟩

end Proofs.CppMoveCallPayload
