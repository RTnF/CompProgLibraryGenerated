import Proofs.CppClassAssignValues
import Proofs.UfClassCopyBridge

namespace Proofs.UfAssignment
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.CppNestedProgram Proofs.CppConstructorFinish
open Proofs.UfReceiverState Proofs.UfFindCall Proofs.CppClassAssign Proofs.CppFrameCopyAssign
open Proofs.DoublingNested (i32)

def object (layout : Layout) : ObjectRef := ⟨layout.vectorSlot,[layout.countSlot,layout.nSlot]⟩

theorem resolve_ok (s : NState) (layout : Layout) (buffer : Buffer Value)
    (ok : VOKWF s layout.vectorSlot layout.vectorBinding layout.owner layout.scope buffer) :
    s.frame.resolve layout.vectorBinding (.integer i32) =
      some (⟨layout.owner,.integer i32,true,.root layout.scope⟩,buffer) := by
  exact (Proofs.CppNestedRows.resolve_vroot s.frame layout.vectorBinding layout.owner layout.scope i32 true true
    buffer ok.binding ok.valid ok.vtag ok.vfound ok.lengths ok.flag (fun _ => rfl)).1

theorem primitive_contents (target source : Proofs.CppVectorCopyAssign.Tracked Value)
    (result : Proofs.CppVectorCopyAssign.Assignment Value)
    (same : target.buffer.owner = source.buffer.owner → target.buffer.items = source.buffer.items)
    (ran : Proofs.CppVectorCopyAssign.copyAssign target source (accepts (.integer i32)) true = some result) :
    result.target.buffer.items = source.buffer.items ∧ result.target.buffer.limit = target.buffer.limit := by
  unfold Proofs.CppVectorCopyAssign.copyAssign at ran
  split at ran
  · split at ran
    · rename_i equal
      cases Option.some.inj ran
      exact ⟨same equal,rfl⟩
    · cases Option.some.inj ran
      refine ⟨Proofs.CppVectorCopyAssign.assigned_items target source,?_⟩
      unfold Proofs.CppVectorCopyAssign.assigned
      split <;> rfl
  · simp at ran

theorem data_success (s : NState) (a b : Nat) (frame : Frame)
    (ran : dataAssign s.frame a b i32 = some frame) :
    ∃ tb sb old source result,
      s.frame.resolve a (.integer i32) = some (tb,old) ∧
      s.frame.resolve b (.integer i32) = some (sb,source) ∧
      Proofs.CppVectorCopyAssign.copyAssign ⟨old,fun _ => 0⟩ ⟨source,fun _ => 0⟩
        (accepts (.integer i32)) true = some result ∧
      frame = (after ⟨s.frame,fun _ _ => 0⟩ tb.owner old result).frame ∧
      frame.state.wellFormed = true := by
  obtain ⟨finish,actual,equal⟩ := Option.map_eq_some_iff.mp ran
  obtain ⟨tb,sb,old,source,result,tr,sr,_,_,primitive,eq,valid⟩ :=
    Proofs.CppFrameCopyAssign.assign_success ⟨s.frame,fun _ _ => 0⟩ finish a b i32 actual
  refine ⟨tb,sb,old,source,result,tr,sr,primitive,?_,?_⟩
  · rw [← equal,eq]
  · rw [← equal]; exact valid

theorem after_ok (s out : NState) (layout : Layout) (old : Buffer Value)
    (result : Proofs.CppVectorCopyAssign.Assignment Value)
    (ok : VOKWF s layout.vectorSlot layout.vectorBinding layout.owner layout.scope old)
    (frame : out.frame = (after ⟨s.frame,fun _ _ => 0⟩ layout.owner old result).frame)
    (valid : out.frame.state.wellFormed = true) (slots : out.slots = s.slots)
    (scope : out.scope = s.scope) (base : out.scalars.baseMemory = s.scalars.baseMemory)
    (memory : out.scalars.memory.length = s.scalars.memory.length) :
    VOKWF out layout.vectorSlot layout.vectorBinding layout.owner layout.scope result.target.buffer := by
  refine ⟨valid,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [NState.vectorSlot,slots] using ok.slot
  · simpa only [frame,after,Frame.updated] using ok.binding
  · simpa only [frame,after,Frame.updated] using ok.vtag
  · rw [frame]
    exact Proofs.CppVectorStore.lookup_set_same s.frame.state.storage layout.owner _
      (Proofs.CppVectorStore.lookup_bound s.frame.state.storage layout.owner old ok.vfound)
  · simpa only [frame,after,Frame.updated] using ok.lengths
  · simpa only [frame,after,Frame.updated] using ok.flag
  · intro owner c found
    rw [scope]
    apply ok.strict owner c
    simpa only [frame,after,Frame.updated] using found
  · rw [base,memory]; exact ok.base

-- A real class assignment yields the same target buffer as its vector stage.
theorem class_target_buffer (s out : NState) (target source : Layout) (old : Buffer Value)
    (ref : ObjectRef) (ok : VOKWF s target.vectorSlot target.vectorBinding target.owner target.scope old)
    (sourceSlotKnown : s.vectorSlot source.vectorSlot = some source.vectorBinding)
    (ran : assignClass s (object target) (object source) Proofs.UfClassCopyBridge.profile = some (out,ref)) :
    ∃ (sb : Binding) (sourceBuffer : Buffer Value) (result : Proofs.CppVectorCopyAssign.Assignment Value),
      s.frame.resolve source.vectorBinding (.integer i32) = some (sb,sourceBuffer) ∧
      VOKWF out target.vectorSlot target.vectorBinding target.owner target.scope result.target.buffer ∧
      result.target.buffer.Valid (accepts (.integer i32)) ∧
      result.target.buffer.owner = target.owner ∧
      result.target.buffer.items = sourceBuffer.items ∧ result.target.buffer.limit = old.limit := by
  obtain ⟨_,a,b,frame,targetSlot,sourceSlot,vectorRun,_,frameEq,slots,scope,_,memory,_⟩ :=
    class_success s out (object target) (object source) ref Proofs.UfClassCopyBridge.profile ran
  have aEq : a = target.vectorBinding := Option.some.inj (targetSlot.symm.trans ok.slot)
  subst a
  have bEq : b = source.vectorBinding := Option.some.inj (sourceSlot.symm.trans sourceSlotKnown)
  subst b
  obtain ⟨tb,sb,actual,sourceBuffer,result,tr,sr,primitive,post,valid⟩ := data_success s target.vectorBinding source.vectorBinding frame vectorRun
  have targetEq := Prod.mk.inj (Option.some.inj (tr.symm.trans (resolve_ok s target old ok)))
  have tbEq := targetEq.1
  have actualEq := targetEq.2
  subst tb
  subst actual
  have props := Proofs.CppVectorCopyAssign.copy_properties _ _ _ _ result primitive
  have owns : old.owner = target.owner := by
    obtain ⟨tag,objectFound⟩ := Proofs.CppFrameCopy.resolve_object s.frame target.vectorBinding i32
      ⟨target.owner,.integer i32,true,.root target.scope⟩ old (resolve_ok s target old ok)
    exact (Proofs.CppFrameCopyAssign.object_valid s.frame target.owner i32 old tag objectFound).2.2.2.2.1
  have base := (class_peak s out (object target) (object source) ref Proofs.UfClassCopyBridge.profile ran).1
  have outFrame := frameEq.trans post
  have sameItems : old.owner = sourceBuffer.owner → old.items = sourceBuffer.items := by
    intro equal
    obtain ⟨sourceTag,sourceObject⟩ := Proofs.CppFrameCopy.resolve_object s.frame source.vectorBinding i32 sb sourceBuffer sr
    have sourceFacts := Proofs.CppFrameCopyAssign.object_valid s.frame sb.owner i32 sourceBuffer sourceTag sourceObject
    have ownerEq : target.owner = sb.owner := owns.symm.trans (equal.trans sourceFacts.2.2.2.2.1)
    have sourceFound : s.frame.state.storage.lookup target.owner = some sourceBuffer := by
      rw [ownerEq]; exact sourceFacts.2.1
    have bufferEq := Option.some.inj (ok.vfound.symm.trans sourceFound)
    rw [bufferEq]
  have contents := primitive_contents ⟨old,fun _ => 0⟩ ⟨sourceBuffer,fun _ => 0⟩ result sameItems primitive
  refine ⟨sb,sourceBuffer,result,sr,?_,props.1,props.2.1.trans owns,contents.1,contents.2⟩
  exact after_ok s out target old result ok outFrame (frameEq ▸ valid) slots scope base memory

theorem assigned_represents (s out : NState) (target source : Layout) (old buf : Buffer Value)
    (ps : List Int) (count : Int) (rank : Nat → Nat)
    (cb nb tb tn : Proofs.CppState.Binding) (tc nc : Proofs.CppState.Cell) (ref : ObjectRef)
    (ok : VOKWF s target.vectorSlot target.vectorBinding target.owner target.scope old)
    (limit : old.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (inv : Inv s source ps count rank buf cb nb)
    (targetCount : s.scalarCell target.countSlot i32 = some (tb,tc))
    (targetN : s.scalarCell target.nSlot i32 = some (tn,nc)) (writable : tb.writable = true)
    (different : tb.address ≠ tn.address) (sourceDifferent : tb.address ≠ nb.address)
    (ran : assignClass s (object target) (object source) Proofs.UfClassCopyBridge.profile = some (out,ref)) :
    Represents out target ps count rank := by
  obtain ⟨sb,sourceBuffer,result,resolved,nextOK,valid,owner,items,newLimit⟩ :=
    class_target_buffer s out target source old ref ok inv.ok.slot ran
  have same := Prod.mk.inj (Option.some.inj (resolved.symm.trans (resolve_ok s source buf inv.ok)))
  have bufferEq := same.2
  subst sourceBuffer
  have cells := Proofs.CppClassAssignValues.class_two_fields s out (object target) (object source) ref
    Proofs.UfClassCopyBridge.profile target.countSlot target.nSlot source.countSlot source.nSlot i32 i32
    tb tn cb nb tc nc ⟨i32,count⟩ ⟨i32,ps.length⟩ rfl rfl rfl targetCount targetN inv.countCell inv.nCell
    different sourceDifferent ran
  exact ⟨result.target.buffer,tb,tn,nextOK,items.trans inv.items,valid,newLimit.trans limit,owner,
    inv.math,cells.1,writable,cells.2,Ne.symm different⟩

-- Readability and permissions suffice for the destination; its old vector and
-- scalar values need not already describe a valid disjoint-set forest.
theorem assignment_terminates (s : NState) (target source : Layout) (old buf : Buffer Value)
    (ps : List Int) (count : Int) (rank : Nat → Nat)
    (cb nb tb tn : Proofs.CppState.Binding) (tc nc : Proofs.CppState.Cell)
    (ok : VOKWF s target.vectorSlot target.vectorBinding target.owner target.scope old)
    (limit : old.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (inv : Inv s source ps count rank buf cb nb)
    (targetCount : s.scalarCell target.countSlot i32 = some (tb,tc))
    (targetN : s.scalarCell target.nSlot i32 = some (tn,nc))
    (writable : tb.writable = true) (nWritable : tn.writable = true) :
    ∃ out, assignClass s (object target) (object source) Proofs.UfClassCopyBridge.profile = some (out,object target) := by
  apply class_terminate s (object target) (object source) Proofs.UfClassCopyBridge.profile
    target.vectorBinding source.vectorBinding
    ⟨target.owner,.integer i32,true,.root target.scope⟩
    ⟨source.owner,.integer i32,true,.root source.scope⟩ old buf
    rfl ok.slot inv.ok.slot (resolve_ok s target old ok) (resolve_ok s source buf inv.ok) rfl
  · have bounded := inv.bufferValid.2.1
    rw [limit,← inv.limit]
    exact Nat.le_trans inv.bufferValid.1 bounded
  · exact ⟨rfl,⟨tb,tc,targetCount,writable⟩,⟨cb,⟨i32,count⟩,inv.countCell⟩,
      rfl,⟨tn,nc,targetN,nWritable⟩,⟨nb,⟨i32,ps.length⟩,inv.nCell⟩,True.intro⟩


theorem class_other_ok (s out : NState) (target source other : Layout) (old buffer : Buffer Value)
    (ref : ObjectRef)
    (ok : VOKWF s target.vectorSlot target.vectorBinding target.owner target.scope old)
    (otherOK : VOKWF s other.vectorSlot other.vectorBinding other.owner other.scope buffer)
    (different : target.owner ≠ other.owner)
    (ran : assignClass s (object target) (object source) Proofs.UfClassCopyBridge.profile = some (out,ref)) :
    VOKWF out other.vectorSlot other.vectorBinding other.owner other.scope buffer := by
  obtain ⟨_,a,b,frame,targetSlot,_,vectorRun,_,frameEq,slots,scope,_,memory,_⟩ :=
    class_success s out (object target) (object source) ref Proofs.UfClassCopyBridge.profile ran
  have aEq : a = target.vectorBinding := Option.some.inj (targetSlot.symm.trans ok.slot)
  subst a
  obtain ⟨tb,sb,actual,sourceBuffer,result,tr,_,_,post,_⟩ := data_success s target.vectorBinding b frame vectorRun
  have same := Prod.mk.inj (Option.some.inj (tr.symm.trans (resolve_ok s target old ok)))
  have tbEq := same.1
  have actualEq := same.2
  subst tb
  subst actual
  have fullFrame := frameEq.trans post
  have base := (class_peak s out (object target) (object source) ref Proofs.UfClassCopyBridge.profile ran).1
  refine ⟨class_wellFormed s out (object target) (object source) ref Proofs.UfClassCopyBridge.profile ran,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [NState.vectorSlot,slots] using otherOK.slot
  · simpa only [fullFrame,after,Frame.updated] using otherOK.binding
  · simpa only [fullFrame,after,Frame.updated] using otherOK.vtag
  · simpa only [fullFrame,after,Frame.updated,Proofs.CppVectorStore.Store.lookup,List.getElem?_set_ne different] using otherOK.vfound
  · simpa only [fullFrame,after,Frame.updated] using otherOK.lengths
  · simpa only [fullFrame,after,Frame.updated] using otherOK.flag
  · intro owner c found
    rw [scope]
    apply otherOK.strict owner c
    simpa only [fullFrame,after,Frame.updated] using found
  · rw [base,memory]; exact otherOK.base

theorem preserves_other (s out : NState) (target source other : Layout) (old buf : Buffer Value)
    (ps : List Int) (count : Int) (rank : Nat → Nat)
    (cb nb : Proofs.CppState.Binding) (ref : ObjectRef)
    (ok : VOKWF s target.vectorSlot target.vectorBinding target.owner target.scope old)
    (inv : Inv s other ps count rank buf cb nb)
    (different : target.owner ≠ other.owner)
    (countSeparate : Proofs.CppClassAssignValues.Separate s (object target).scalarSlots cb.address)
    (nSeparate : Proofs.CppClassAssignValues.Separate s (object target).scalarSlots nb.address)
    (ran : assignClass s (object target) (object source) Proofs.UfClassCopyBridge.profile = some (out,ref)) :
    Represents out other ps count rank := by
  have nextOK := class_other_ok s out target source other old buf ref ok inv.ok different ran
  have countCell := Proofs.CppClassAssignValues.class_other s out (object target) (object source) ref
    Proofs.UfClassCopyBridge.profile ran other.countSlot i32 cb ⟨i32,count⟩ inv.countCell countSeparate
  have nCell := Proofs.CppClassAssignValues.class_other s out (object target) (object source) ref
    Proofs.UfClassCopyBridge.profile ran other.nSlot i32 nb ⟨i32,ps.length⟩ inv.nCell nSeparate
  exact ⟨buf,cb,nb,nextOK,inv.items,inv.bufferValid,inv.limit,inv.owner,inv.math,
    countCell,inv.writable,nCell,inv.different⟩

end Proofs.UfAssignment
