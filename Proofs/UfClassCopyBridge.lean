import Proofs.CppClassCopy
import Proofs.UfCopyFields

namespace Proofs.UfClassCopyBridge
open Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppConstructorFinish
open Proofs.CppClassCopy Proofs.UfCopyFields Proofs.UfReceiverState Proofs.CppFrameCopy
open Proofs.DoublingNested (i32)

def profile : Profile := ⟨i32,true,[(i32,true),(i32,true)]⟩

theorem finish_two (s : NState) (frame : Frame) (count n : Int) :
    Proofs.CppClassCopy.finish s frame s.frame.bindings.length [(⟨i32,count⟩,true),(⟨i32,n⟩,true)] =
      fields s frame count n := by
  simp [Proofs.CppClassCopy.finish,fields,scalarBindings,scalarLocations,List.range_succ]

theorem copy_equiv (s : NState) (layout : Layout) :
    copyClass s ⟨layout.vectorSlot,[layout.countSlot,layout.nSlot]⟩ profile =
      (copyReceiver s layout).map (fun result => (result.1,reference s 2)) := by
  cases slot : s.vectorSlot layout.vectorSlot with
  | none => simp [copyClass,copyReceiver,slot]
  | some index =>
    cases copied : copyVector s.frame index i32 s.scope true with
    | none => simp [copyClass,copyReceiver,profile,slot,copied]
    | some pair =>
      obtain ⟨frame,binding⟩ := pair
      obtain ⟨sourceBinding,sourceBuffer,lengths,supported,resolved,frameEq,bindingEq⟩ :=
        copy_vector_inv s.frame frame index binding i32 s.scope true copied
      subst binding
      cases countFound : s.scalarCell layout.countSlot i32 with
      | none => simp [copyClass,copyReceiver,profile,slot,Proofs.CppClassCopy.captureAll,Proofs.CppClassCopy.capture,countFound]
      | some pair =>
        obtain ⟨cb,countCell⟩ := pair
        obtain ⟨_,_,_,_,countType,_⟩ := Proofs.ExtremaCall.scalarCell_facts countFound
        cases countCell with
        | mk ty count =>
          dsimp only at countType
          subst ty
          cases nFound : s.scalarCell layout.nSlot i32 with
          | none => simp [copyClass,copyReceiver,profile,slot,Proofs.CppClassCopy.captureAll,Proofs.CppClassCopy.capture,countFound,nFound]
          | some pair =>
            obtain ⟨nb,nCell⟩ := pair
            obtain ⟨_,_,_,_,nType,_⟩ := Proofs.ExtremaCall.scalarCell_facts nFound
            cases nCell with
            | mk ty n =>
              dsimp only at nType
              subst ty
              simp [copyClass,copyReceiver,profile,slot,copied,Proofs.CppClassCopy.captureAll,Proofs.CppClassCopy.capture,countFound,nFound,finish_two]

end Proofs.UfClassCopyBridge
