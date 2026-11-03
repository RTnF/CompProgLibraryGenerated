import Proofs.UfAssignment

namespace Proofs.UfAssignmentView
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorOwnership Proofs.CppNestedVectorStore
open Proofs.CppNestedVectorBindings Proofs.CppNestedProgram Proofs.CppConstructorFinish
open Proofs.UfReceiverState Proofs.UfFindCall Proofs.UfAssignment Proofs.CppClassAssign
open Proofs.DoublingNested (i32)

-- A copy source needs readable fields, not write permission on its bindings.
structure SourceView (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (buffer : Buffer Value) (binding : Binding) (cb nb : Proofs.CppState.Binding) : Prop where
  slot : s.vectorSlot layout.vectorSlot = some layout.vectorBinding
  resolved : s.frame.resolve layout.vectorBinding (.integer i32) = some (binding,buffer)
  items : buffer.items = ps.map Value.integer
  valid : buffer.Valid (accepts (.integer i32))
  limit : buffer.limit = Proofs.CppVectorBindings.sizeLimit i32
  math : Proofs.UfClassInvariant.Valid ps count rank
  countCell : s.scalarCell layout.countSlot i32 = some (cb,⟨i32,count⟩)
  nCell : s.scalarCell layout.nSlot i32 = some (nb,⟨i32,ps.length⟩)

theorem SourceView.of_inv (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (buffer : Buffer Value) (cb nb : Proofs.CppState.Binding) (inv : Inv s layout ps count rank buffer cb nb) :
    SourceView s layout ps count rank buffer ⟨layout.owner,.integer i32,true,.root layout.scope⟩ cb nb :=
  ⟨inv.ok.slot,resolve_ok s layout buffer inv.ok,inv.items,inv.bufferValid,inv.limit,inv.math,inv.countCell,inv.nCell⟩

theorem assign_ready (s : NState) (target source : Layout) (old buffer : Buffer Value)
    (ps : List Int) (count : Int) (rank : Nat → Nat) (binding : Binding)
    (cb nb tb tn : Proofs.CppState.Binding) (tc nc : Proofs.CppState.Cell)
    (ok : VOKWF s target.vectorSlot target.vectorBinding target.owner target.scope old)
    (limit : old.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (view : SourceView s source ps count rank buffer binding cb nb)
    (targetCount : s.scalarCell target.countSlot i32 = some (tb,tc))
    (targetN : s.scalarCell target.nSlot i32 = some (tn,nc))
    (writable : tb.writable = true) (nWritable : tn.writable = true) :
    ∃ out, assignClass s (object target) (object source) Proofs.UfClassCopyBridge.profile = some (out,object target) := by
  apply class_terminate s (object target) (object source) Proofs.UfClassCopyBridge.profile
    target.vectorBinding source.vectorBinding ⟨target.owner,.integer i32,true,.root target.scope⟩ binding old buffer
    rfl ok.slot view.slot (resolve_ok s target old ok) view.resolved rfl
  · rw [limit,← view.limit]
    exact Nat.le_trans view.valid.1 view.valid.2.1
  · exact ⟨rfl,⟨tb,tc,targetCount,writable⟩,⟨cb,⟨i32,count⟩,view.countCell⟩,
      rfl,⟨tn,nc,targetN,nWritable⟩,⟨nb,⟨i32,ps.length⟩,view.nCell⟩,True.intro⟩

theorem assign_represents (s out : NState) (target source : Layout) (old buffer : Buffer Value)
    (ps : List Int) (count : Int) (rank : Nat → Nat) (binding : Binding)
    (cb nb tb tn : Proofs.CppState.Binding) (tc nc : Proofs.CppState.Cell) (ref : ObjectRef)
    (ok : VOKWF s target.vectorSlot target.vectorBinding target.owner target.scope old)
    (limit : old.limit = Proofs.CppVectorBindings.sizeLimit i32)
    (view : SourceView s source ps count rank buffer binding cb nb)
    (targetCount : s.scalarCell target.countSlot i32 = some (tb,tc))
    (targetN : s.scalarCell target.nSlot i32 = some (tn,nc)) (writable : tb.writable = true)
    (different : tb.address ≠ tn.address) (sourceDifferent : tb.address ≠ nb.address)
    (ran : assignClass s (object target) (object source) Proofs.UfClassCopyBridge.profile = some (out,ref)) :
    Represents out target ps count rank := by
  obtain ⟨actualBinding,actualBuffer,result,resolved,nextOK,valid,owner,items,newLimit⟩ :=
    class_target_buffer s out target source old ref ok view.slot ran
  have same := Prod.mk.inj (Option.some.inj (resolved.symm.trans view.resolved))
  have bufferEq := same.2
  subst actualBuffer
  have cells := Proofs.CppClassAssignValues.class_two_fields s out (object target) (object source) ref
    Proofs.UfClassCopyBridge.profile target.countSlot target.nSlot source.countSlot source.nSlot i32 i32
    tb tn cb nb tc nc ⟨i32,count⟩ ⟨i32,ps.length⟩ rfl rfl rfl targetCount targetN view.countCell view.nCell
    different sourceDifferent ran
  exact ⟨result.target.buffer,tb,tn,nextOK,items.trans view.items,valid,newLimit.trans limit,owner,
    view.math,cells.1,writable,cells.2,Ne.symm different⟩


theorem root_resolve_preserved (f g : Frame) (slot scope : Nat) (binding : Binding) (buffer : Buffer Value)
    (bindings : g.bindings = f.bindings) (flags : g.rootWritable = f.rootWritable)
    (forest : g.state.forest = f.state.forest) (root : binding.header = .root scope)
    (objects : ∀ expected, g.object binding.owner expected = f.object binding.owner expected)
    (resolved : f.resolve slot (.integer i32) = some (binding,buffer)) :
    g.resolve slot (.integer i32) = some (binding,buffer) := by
  have fullRun := resolved
  unfold Frame.resolve at resolved
  obtain ⟨b,bindingFound,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ resolved
  obtain ⟨owner,headerFound,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  obtain ⟨⟨actual,tag⟩,objectFound,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  obtain ⟨maximum,maximumFound,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  try dsimp only at rest
  split at rest
  · rename_i good
    obtain ⟨bindingEq,bufferEq⟩ := Prod.mk.inj (Option.some.inj rest)
    subst b
    subst actual
    have headerSame : g.headerOwner binding = f.headerOwner binding := by
      simp only [Frame.headerOwner,root,objects]
    have maximumSame : g.maximum owner = f.maximum owner := by simp only [Frame.maximum,flags,forest]
    have ownerEq : owner = binding.owner := good.1.symm
    have objectSame : g.object owner (.integer i32) = f.object owner (.integer i32) := by
      rw [ownerEq]; exact objects _
    simp only [Frame.resolve,bindings,bindingFound,headerSame,headerFound,objectSame,objectFound,
      maximumSame,maximumFound,Bind.bind,Option.bind]
    exact ite_eq_left good
  · simp at rest


theorem preserves_view (s out : NState) (target source other : Layout) (old buffer : Buffer Value)
    (ps : List Int) (count : Int) (rank : Nat → Nat) (binding : Binding)
    (cb nb : Proofs.CppState.Binding) (ref : ObjectRef)
    (ok : VOKWF s target.vectorSlot target.vectorBinding target.owner target.scope old)
    (view : SourceView s other ps count rank buffer binding cb nb)
    (root : binding.header = .root other.scope) (different : target.owner ≠ binding.owner)
    (countSeparate : Proofs.CppClassAssignValues.Separate s (object target).scalarSlots cb.address)
    (nSeparate : Proofs.CppClassAssignValues.Separate s (object target).scalarSlots nb.address)
    (ran : assignClass s (object target) (object source) Proofs.UfClassCopyBridge.profile = some (out,ref)) :
    SourceView out other ps count rank buffer binding cb nb := by
  obtain ⟨_,a,b,frame,targetSlot,_,vectorRun,_,frameEq,slots,_,_,_,_⟩ :=
    class_success s out (object target) (object source) ref Proofs.UfClassCopyBridge.profile ran
  have aEq : a = target.vectorBinding := Option.some.inj (targetSlot.symm.trans ok.slot)
  subst a
  obtain ⟨tb,sb,actual,sourceBuffer,result,tr,_,_,post,valid⟩ := data_success s target.vectorBinding b frame vectorRun
  have same := Prod.mk.inj (Option.some.inj (tr.symm.trans (resolve_ok s target old ok)))
  have tbEq := same.1
  have actualEq := same.2
  subst tb
  subst actual
  have fullFrame := frameEq.trans post
  have objects : ∀ expected, out.frame.object binding.owner expected = s.frame.object binding.owner expected := by
    intro expected
    rw [fullFrame]
    exact Proofs.CppFrameCopyAssign.after_object_other ⟨s.frame,fun _ _ => 0⟩ target.owner binding.owner old result
      expected different ok.valid (post ▸ valid)
  have resolved := root_resolve_preserved s.frame out.frame other.vectorBinding other.scope binding buffer
    (by simp only [fullFrame,Proofs.CppFrameCopyAssign.after,Frame.updated])
    (by simp only [fullFrame,Proofs.CppFrameCopyAssign.after,Frame.updated])
    (by simp only [fullFrame,Proofs.CppFrameCopyAssign.after,Frame.updated]) root objects view.resolved
  have countCell := Proofs.CppClassAssignValues.class_other s out (object target) (object source) ref
    Proofs.UfClassCopyBridge.profile ran other.countSlot i32 cb ⟨i32,count⟩ view.countCell countSeparate
  have nCell := Proofs.CppClassAssignValues.class_other s out (object target) (object source) ref
    Proofs.UfClassCopyBridge.profile ran other.nSlot i32 nb ⟨i32,ps.length⟩ view.nCell nSeparate
  refine ⟨?_,resolved,view.items,view.valid,view.limit,view.math,countCell,nCell⟩
  simpa only [NState.vectorSlot,slots] using view.slot

end Proofs.UfAssignmentView
