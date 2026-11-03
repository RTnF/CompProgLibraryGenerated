import Proofs.CppMoveReceiverLayout
import Proofs.CppMoveReceiverFrame
import Proofs.UfFieldsRoot
import Proofs.UfFieldsSame
import Proofs.UfFieldsCounter

namespace Proofs.UfReceiverLayout
open Proofs.CppMoveContext Proofs.CppMoveReceiverLayout Proofs.CppScalar
open Proofs.CppNestedProgram Proofs.CppMoveCallBindings Proofs.QuotientFrame
open Proofs.CppState (Cell)
open Proofs.StraightLine Proofs.DoublingNested

-- Build the normal callee layout from resolved source arguments.
theorem prepare_qs (s last : Context) (borrow : Borrow)
    (header : Proofs.CppMoveHeaders.Header)
    (found : s.objects.heap.header borrow.header = some header)
    (permission : borrow.writable = true → header.writable = true)
    (address : Nat) (count : Int)
    (counter : s.scalars.memory[address]? = some ⟨i32,count⟩)
    (countValid : i32.valid count = true) (values : List Int)
    (valid : ∀ value ∈ values, i32.valid value = true)
    (parameters : List Proofs.CppVectorBindings.Parameter)
    (arguments : List Proofs.CppNestedCall.NArgument)
    (resolved : resolveArguments s i32 parameters arguments =
      some (last,receiverArguments borrow i32 address true values)) :
    ∃ prepared initial,
      prepareArguments s i32 parameters arguments = some prepared ∧
      compact (project prepared i32) = some initial ∧
      QS initial [] initial.scalars.baseMemory initial.scope
        (receiverPrefix s ++ cells i32 values)
        (⟨address,true⟩ :: valueBindings (receiverPrefix s).length values.length)
        (.vector 0 :: .scalar 0 :: valueSlots 1 values.length) ∧
      initial.scalars.baseMemory = s.scalars.baseMemory ∧
      initial.scope = s.scope+1 ∧
      initial.frame.state = (project s i32).frame.state ∧
      initial.frame.rootWritable = (project s i32).frame.rootWritable ∧
      initial.frame.bindings = [Proofs.CppMoveFrame.viewBinding s.objects i32 ⟨borrow.header,borrow.writable⟩] := by
  obtain ⟨prepared,run,objects,memory,bindings,slots,scope,base⟩ :=
    prepareArguments_receiver s last borrow header found permission i32 address true count
      counter countValid values valid parameters arguments resolved
  have view : prepared.objects.views[s.objects.views.length]? = some ⟨borrow.header,borrow.writable⟩ := by
    simp [objects]
  obtain ⟨initial,compacted,qs,state,oneBinding⟩ := compact_receiver prepared i32 _ values.length _ view slots
  have data := compact_metadata (project prepared i32) initial compacted
  refine ⟨prepared,initial,run,compacted,?_,?_,?_,?_,?_,?_⟩
  · exact ⟨qs.slots,by simpa only [List.nil_append,memory] using qs.memory,
      qs.bindings.trans bindings,rfl,rfl⟩
  · rw [data.2.2.1]
    exact base
  · rw [data.2.2.2.1]
    exact scope
  · rw [state]
    simp only [project,Proofs.CppMoveFrame.materialize,objects]
  · rw [data.2.1]
    simp only [project,Proofs.CppMoveFrame.materialize,objects]
  · simpa only [Proofs.CppMoveFrame.viewBinding,objects] using oneBinding

-- Match the exact scalar states consumed by the existing original-method proofs.
theorem qs_two (initial : NState) (P : List Cell) (address : Nat) (n a : Int)
    (qs : QS initial [] initial.scalars.baseMemory initial.scope
      (P++cells i32 [n,a]) (⟨address,true⟩::valueBindings P.length 2)
      (.vector 0 :: .scalar 0 :: valueSlots 1 2)) :
    QS initial [] initial.scalars.baseMemory initial.scope
      (Proofs.UfFieldsRoot.fields P ⟨address,true⟩ n a).mem
      (Proofs.UfFieldsRoot.fields P ⟨address,true⟩ n a).bs
      (Proofs.VecExpr.sl1 (Proofs.UfFieldsRoot.fields P ⟨address,true⟩ n a).bs.length) := by
  simpa [Proofs.UfFieldsRoot.fields,Proofs.VecShift.pad,Proofs.PrefixSumsCall.stI,
    cells,valueBindings,addresses,valueSlots,Proofs.VecExpr.sl1,Proofs.Mod61Body.ssl,List.range_succ,List.append_assoc,Nat.add_assoc] using qs

theorem qs_three (initial : NState) (P : List Cell) (address : Nat) (n a b : Int)
    (qs : QS initial [] initial.scalars.baseMemory initial.scope
      (P++cells i32 [n,a,b]) (⟨address,true⟩::valueBindings P.length 3)
      (.vector 0 :: .scalar 0 :: valueSlots 1 3)) :
    QS initial [] initial.scalars.baseMemory initial.scope
      (Proofs.UfFieldsSame.fields P ⟨address,true⟩ n a b).mem
      (Proofs.UfFieldsSame.fields P ⟨address,true⟩ n a b).bs
      (Proofs.VecExpr.sl1 (Proofs.UfFieldsSame.fields P ⟨address,true⟩ n a b).bs.length) := by
  simpa [Proofs.UfFieldsSame.fields,cells,valueBindings,addresses,valueSlots,
    Proofs.VecExpr.sl1,Proofs.Mod61Body.ssl,List.range_succ,Nat.add_assoc] using qs

theorem qs_one (initial : NState) (P : List Cell) (address : Nat) (n : Int)
    (qs : QS initial [] initial.scalars.baseMemory initial.scope
      (P++cells i32 [n]) (⟨address,true⟩::valueBindings P.length 1)
      (.vector 0 :: .scalar 0 :: valueSlots 1 1)) :
    QS initial [] initial.scalars.baseMemory initial.scope
      (Proofs.UfFieldsCounter.fields P address n).mem
      (Proofs.UfFieldsCounter.fields P address n).bs
      (Proofs.VecExpr.sl1 (Proofs.UfFieldsCounter.fields P address n).bs.length) := by
  simpa [Proofs.UfFieldsCounter.fields,cells,valueBindings,addresses,valueSlots,
    Proofs.VecExpr.sl1,Proofs.Mod61Body.ssl,List.range_succ,Nat.add_assoc] using qs


open Proofs.CppMoveReceiverFrame Proofs.CppMoveFrame Proofs.VecExpr Proofs.VecWrite
open Proofs.CppVector Proofs.CppMoveHeaders

theorem prefix_length (s : Context) : s.scalars.memory.length ≤ (receiverPrefix s).length := by
  simp [receiverPrefix]

theorem prefix_take (s : Context) :
    (receiverPrefix s).take s.scalars.memory.length = s.scalars.memory := by
  unfold receiverPrefix
  rw [List.append_assoc,List.take_left]

theorem prefix_cell (s : Context) (address : Nat) (cell : Cell)
    (found : s.scalars.memory[address]? = some cell) : (receiverPrefix s)[address]? = some cell := by
  have inside := (List.getElem?_eq_some_iff.mp found).1
  unfold receiverPrefix
  rw [List.append_assoc,List.getElem?_append_left inside]
  exact found

-- A readable receiver and global ownership/allocation conditions construct FW;
-- neither completed FW nor a successful body run is assumed.
theorem prepare_qs_fw (s last : Context) (borrow : Borrow)
    (header : Proofs.CppMoveHeaders.Header)
    (found : s.objects.heap.header borrow.header = some header)
    (permission : borrow.writable = true → header.writable = true)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap header i32.valid = true)
    (unique : Unique s.objects.heap) (covered : OwnsAll s.objects.heap)
    (validAllocations : AllocationsValid s.objects.heap i32)
    (limit : header.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (address : Nat) (count : Int)
    (counter : s.scalars.memory[address]? = some ⟨i32,count⟩)
    (countValid : i32.valid count = true) (values : List Int)
    (valid : ∀ value ∈ values, i32.valid value = true)
    (parameters : List Proofs.CppVectorBindings.Parameter)
    (arguments : List Proofs.CppNestedCall.NArgument)
    (resolved : resolveArguments s i32 parameters arguments =
      some (last,receiverArguments borrow i32 address true values))
    (contexts : ∀ owner sc, (project s i32).frame.state.forest.context owner = some sc → sc ≤ s.scope) :
    ∃ (prepared : Context) (initial : NState) (vc : VCtx) (buffer : Buffer Int),
      prepareArguments s i32 parameters arguments = some prepared ∧
      compact (project prepared i32) = some initial ∧
      QS initial [] initial.scalars.baseMemory initial.scope
        (receiverPrefix s ++ cells i32 values)
        (⟨address,true⟩ :: valueBindings (receiverPrefix s).length values.length)
        (.vector 0 :: .scalar 0 :: valueSlots 1 values.length) ∧
      FW vc buffer.items (box buffer) 0 initial.frame ∧
      vc.ty = i32 ∧ vc.wV = borrow.writable ∧ vc.flag = true ∧ vc.sc = initial.scope ∧
      currentBuffer s.objects.heap borrow.header header = some buffer ∧
      initial.scalars.baseMemory = s.scalars.baseMemory ∧ initial.scope = s.scope+1 := by
  obtain ⟨prepared,initial,run,compacted,qs,base,scope,state,roots,bindings⟩ :=
    prepare_qs s last borrow header found permission address count counter countValid values valid parameters arguments resolved
  obtain ⟨buffer,current,entry,bufferValid,bufferLimit,owner⟩ :=
    current_entry s.objects.heap i32 borrow.header header found readable unique covered
  have small : buffer.items.length < 18446744073709551616 := by
    have lengths := bufferValid.1
    have capacity := bufferValid.2.1
    have limitBound : Proofs.CppVectorBindings.sizeLimit i32 < 18446744073709551616 := by decide +kernel
    rw [bufferLimit,limit] at capacity
    omega
  have fw := fw_from_entry s initial i32 borrow.header header borrow.writable buffer found permission entry
    bufferValid (bufferLimit.trans limit) small owner (by decide +kernel) validAllocations state roots bindings scope contexts
  exact ⟨prepared,initial,Proofs.CppMoveReceiverFrame.context initial i32 header borrow.writable buffer small,
    buffer,run,compacted,qs,fw,rfl,rfl,rfl,rfl,current,base,scope⟩

end Proofs.UfReceiverLayout
