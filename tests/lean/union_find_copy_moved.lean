namespace UfCopyMovedExamples
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
open Proofs.CppMoveFrame Proofs.CppMoveReadReceiver Proofs.CppConstructorFinish
open ReadReceiverPermissionExamples

def copied (w : Bool) := Proofs.UfCopyContext.copy input object w
#guard (copied true).map (fun p => (p.1.scalars.memory.map (·.value),
    (p.1.objects.heap.allocation 0).map (fun a => (a.buffer.items,a.buffer.capacity,a.buffer.epoch)),
    (p.1.objects.heap.header 1).map (·.writable))) ==
  some ([1,4,0,1,4],some ([],0,0),some true)
#guard (copied false).map (fun p => p.1.scalars.bindings.map (·.writable)) ==
  some [false,false,false,false,false]

def getter (w : Bool) := copied w |>.bind fun p =>
  match Proofs.UnionFindPublicCompatInstance.Calls.UnionFind_num_groups_0_2_callFuel 8 p.1 p.2 [] with
  | .finished (out,.scalar v) => some (out.scalars.memory.map (·.value),v)
  | _ => none
#guard getter true == some ([1,4,0,1,4],1)
#guard getter false == some ([1,4,0,1,4],1)

-- The old empty view's synthetic owner changes; its values and capacity do not.
#guard (currentBuffer input.objects.heap 0 ⟨none,0,false,limit⟩).map (·.owner) == some 0
#guard (copied false).bind (fun p =>
    (currentBuffer p.1.objects.heap 0 ⟨none,0,false,limit⟩).map (·.owner)) == some 1
#guard (copied false).bind (fun p =>
    (currentBuffer p.1.objects.heap 0 ⟨none,0,false,limit⟩).map
      (fun b => (b.items,b.capacity,b.epoch))) == some ([],0,0)

example (w : Bool) := Proofs.UfCopyContext.copied input object receiver
  ⟨0,[],0,limit,0⟩ rfl (by decide +kernel)
  ReadReceiverMovedGetterExamples.unique ReadReceiverMovedGetterExamples.covered
  ReadReceiverMovedGetterExamples.allocations w

example (w : Bool) := Proofs.UfCopyContextPreserve.old_read_receiver input
  (⟨0,[],0,limit,0⟩ : Proofs.CppVector.Buffer Int) 1 4 w object receiver

theorem headers_live : Proofs.CppMoveSpace.HeadersLive input.objects.heap := by
  intro id h owner found owns
  obtain ⟨_,rfl⟩ := ReadReceiverMovedGetterExamples.header id h found
  cases owns

-- No UF validity or n = vector length is required for the moved-from getter.
example (w : Bool) := Proofs.UfCopyCounterCall.counter input object receiver
  ⟨0,[],0,limit,0⟩ rfl (by decide +kernel)
  ReadReceiverMovedGetterExamples.unique ReadReceiverMovedGetterExamples.covered
  headers_live ReadReceiverMovedGetterExamples.allocations rfl
  (by change 0 ≤ _; omega) ReadReceiverMovedGetterExamples.contexts w

end UfCopyMovedExamples
