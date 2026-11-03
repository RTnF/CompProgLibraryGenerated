import Proofs.CppFrameCopy
import Proofs.UfReceiverState

namespace Proofs.UfCopyFields
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedVectorStore Proofs.CppFrameCopy Proofs.UfReceiverState
open Proofs.CppMixedInvoke
open Proofs.DoublingNested (i32)

-- All three UF members are mutable regardless of the source expression's
-- constness. Scalar values are copied into fresh cells, never aliased.
def fields (s : NState) (frame : Frame) (count n : Int) : NState :=
  let scalars : Proofs.CppState.State := {s.scalars with
    memory := s.scalars.memory++[⟨i32,count⟩,⟨i32,n⟩],
    bindings := s.scalars.bindings++[⟨s.scalars.memory.length,true⟩,⟨s.scalars.memory.length+1,true⟩],
    work := s.scalars.work+3}
  ({s with
    scalars := scalars.observe 0
    frame := frame
    slots := s.slots++[.vector s.frame.bindings.length,.scalar s.scalars.bindings.length,
      .scalar (s.scalars.bindings.length+1)]} : NState).observe

def copyReceiver (s : NState) (layout : Layout) : Option (NState × Layout) := do
  let vector ← s.vectorSlot layout.vectorSlot
  let (frame,_) ← copyVector s.frame vector i32 s.scope true
  let (_,count) ← s.scalarCell layout.countSlot i32
  let (_,n) ← s.scalarCell layout.nSlot i32
  some (fields s frame count.value n.value,layoutOf s)

theorem fields_count (s : NState) (frame : Frame) (count n : Int) (valid : i32.valid count = true) :
    (fields s frame count n).scalarCell (layoutOf s).countSlot i32 =
      some (⟨s.scalars.memory.length,true⟩,⟨i32,count⟩) := by
  simp [fields,layoutOf,NState.scalarCell,NState.scalarSlot,NState.observe,Proofs.CppState.State.observe,
    List.getElem?_append,valid]

theorem fields_n (s : NState) (frame : Frame) (count n : Int) (valid : i32.valid n = true) :
    (fields s frame count n).scalarCell (layoutOf s).nSlot i32 =
      some (⟨s.scalars.memory.length+1,true⟩,⟨i32,n⟩) := by
  simp [fields,layoutOf,NState.scalarCell,NState.scalarSlot,NState.observe,Proofs.CppState.State.observe,
    List.getElem?_append,valid]

theorem fields_vector (s : NState) (frame : Frame) (count n : Int) :
    (fields s frame count n).vectorSlot (layoutOf s).vectorSlot = some s.frame.bindings.length := by
  simp [fields,layoutOf,NState.vectorSlot,NState.observe]

theorem copy_receiver_runs (s : NState) (layout : Layout) (count n : Int)
    (cb nb : Proofs.CppState.Binding) (binding : Binding)
    (source : Proofs.CppVector.Buffer Value)
    (slot : s.vectorSlot layout.vectorSlot = some layout.vectorBinding)
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (resolved : s.frame.resolve layout.vectorBinding (.integer i32) = some (binding,source))
    (countCell : s.scalarCell layout.countSlot i32 = some (cb,⟨i32,count⟩))
    (nCell : s.scalarCell layout.nSlot i32 = some (nb,⟨i32,n⟩)) :
    copyReceiver s layout = some (fields s (copiedFrame s.frame source i32 s.scope true) count n,layoutOf s) := by
  have copied := copy_vector_runs s.frame layout.vectorBinding i32 s.scope true binding source lengths
    (by decide +kernel) resolved
  simp [copyReceiver,slot,copied,countCell,nCell]

open Proofs.DynamicResultValid

theorem scalar_valid (s : NState) (slot : Nat) (ty : Ty) (binding : Proofs.CppState.Binding)
    (cell : Proofs.CppState.Cell) (actual : s.scalarCell slot ty = some (binding,cell)) :
    ty.valid cell.value = true := by
  unfold NState.scalarCell at actual
  obtain ⟨index,_,rest⟩ := bind_some _ _ _ actual
  obtain ⟨b,_,rest⟩ := bind_some _ _ _ rest
  obtain ⟨c,_,rest⟩ := bind_some _ _ _ rest
  split at rest
  · rename_i good
    have eq := (Prod.mk.inj (Option.some.inj rest)).2
    subst c
    exact good.2
  · simp at rest

theorem fields_old_scalar (s : NState) (frame : Frame) (count n : Int) (slot : Nat) (ty : Ty)
    (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
    (actual : s.scalarCell slot ty = some (binding,cell)) :
    (fields s frame count n).scalarCell slot ty = some (binding,cell) := by
  unfold NState.scalarCell at actual
  obtain ⟨index,slotFound,rest⟩ := bind_some _ _ _ actual
  obtain ⟨b,found,rest⟩ := bind_some _ _ _ rest
  obtain ⟨c,cellFound,rest⟩ := bind_some _ _ _ rest
  have slotBound : slot < s.slots.length := by
    by_contra outside
    have missing := List.getElem?_eq_none_iff.mpr (show s.slots.length ≤ slot by omega)
    simp [NState.scalarSlot,missing] at slotFound
  have bindingBound := (List.getElem?_eq_some_iff.mp found).1
  have addressBound := (List.getElem?_eq_some_iff.mp cellFound).1
  have slotOut : (fields s frame count n).scalarSlot slot = some index := by
    simpa only [fields,NState.observe,NState.scalarSlot,List.getElem?_append_left slotBound] using slotFound
  have bindingOut : (fields s frame count n).scalars.bindings[index]? = some b := by
    simpa only [fields,NState.observe,Proofs.CppState.State.observe,List.getElem?_append_left bindingBound] using found
  have cellOut : (fields s frame count n).scalars.memory[b.address]? = some c := by
    simpa only [fields,NState.observe,Proofs.CppState.State.observe,List.getElem?_append_left addressBound] using cellFound
  simpa only [NState.scalarCell,slotOut,bindingOut,cellOut,Bind.bind,Option.bind] using rest

theorem fields_old_vector (s : NState) (frame : Frame) (count n : Int) (slot index : Nat)
    (actual : s.vectorSlot slot = some index) :
    (fields s frame count n).vectorSlot slot = some index := by
  have slotBound : slot < s.slots.length := by
    by_contra outside
    have missing := List.getElem?_eq_none_iff.mpr (show s.slots.length ≤ slot by omega)
    simp [NState.vectorSlot,missing] at actual
  simpa only [fields,NState.observe,NState.vectorSlot,List.getElem?_append_left slotBound] using actual

end Proofs.UfCopyFields
