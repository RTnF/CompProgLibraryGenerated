import Proofs.UfObjectConstructionExport
import Proofs.CppConstructorLayout
import Proofs.CppMoveObjectReceiver

namespace Proofs.UfObjectConstructionContext
open Proofs.UfObjectConstructionExport Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppConstructorFinish
open Proofs.CppMoveObjectReceiver Proofs.CppMoveFrame Proofs.DoublingNested Proofs.DynamicResultValid

-- NState includes the immutable grant bindings before the object views.
def unlocation (grants : Nat) : Proofs.CppMixedInvoke.Location → Proofs.CppMixedInvoke.Location
  | .scalar index => .scalar index
  | .vector index => .vector (index-grants)

def exported (s : Context) (after : NState) (n : Nat) : Context :=
  ⟨⟨exportedHeap s after n,s.objects.views++[⟨s.objects.heap.headers.length,true⟩]⟩,
    after.scalars,after.slots.map (unlocation s.objects.heap.grants.length),after.scope,after.peak⟩

theorem scalar_slot (s : Context) (after : NState) (n slot : Nat) :
    Proofs.CppMoveContext.scalarSlot (exported s after n) slot = after.scalarSlot slot := by
  unfold Proofs.CppMoveContext.scalarSlot NState.scalarSlot
  simp only [exported,List.getElem?_map]
  cases entry : after.slots[slot]? with
  | none => rfl
  | some loc => cases loc <;> rfl

theorem field_of_cell (s : Context) (after : NState) (n slot address : Nat) (writable : Bool) (value : Int)
    (cell : after.scalarCell slot i32 = some (⟨address,writable⟩,⟨i32,value⟩)) :
    ∃ field : Field (exported s after n) i32,
      field.slot = slot ∧ field.address = address ∧ field.writable = writable ∧ field.value = value := by
  unfold NState.scalarCell at cell
  obtain ⟨index,located,rest⟩ := bind_some _ _ _ cell
  obtain ⟨binding,bound,rest⟩ := bind_some _ _ _ rest
  obtain ⟨actual,found,rest⟩ := bind_some _ _ _ rest
  split at rest
  · rename_i typed
    obtain ⟨bindingEq,actualEq⟩ := Prod.mk.inj (Option.some.inj rest)
    subst binding
    subst actual
    refine ⟨⟨slot,index,address,writable,value,?_,bound,found,typed.2⟩,rfl,rfl,rfl,rfl⟩
    rw [scalar_slot]
    exact located
  · simp at rest

theorem located_vector (s : Context) (after : NState) (n : Nat) (object : ObjectRef)
    (layout : Proofs.CppConstructorLayout.Layout (project s i32) after object) :
    vectorView (exported s after n) object.vectorSlot = some s.objects.views.length := by
  obtain ⟨oldCells,values,oldLength,oldTypes,memory,bindings,slots,scope,base,objectEq⟩ := layout
  have entry : after.slots[(project s i32).slots.length]? = some (.vector (project s i32).frame.bindings.length) := by
    rw [slots,List.append_assoc]
    simp
  simp only [project,List.length_map] at entry
  rw [objectEq]
  simp [vectorView,Proofs.CppConstructorFinish.reference,exported,List.getElem?_map,entry,unlocation,project,materialize]

theorem resolved_vector (s : Context) (after : NState) (n : Nat) :
    Proofs.CppMoveViews.resolve (exported s after n).objects s.objects.views.length =
      some (⟨s.objects.heap.headers.length,true⟩,
        ⟨some s.objects.heap.allocations.length,s.scope,true,Proofs.CppVectorBindings.sizeLimit i32⟩) := by
  simp [Proofs.CppMoveViews.resolve,exported,exportedHeap,Proofs.CppMoveAppendOwned.appended,
    Proofs.CppMoveHeaders.Heap.header,payload]

theorem receiver (s : Context) (after : NState) (n : Nat)
    (initialized : Proofs.UfConstructionExport.Initialized (project s i32) after (List.replicate n (-1)) n n)
    (layout : Proofs.CppConstructorLayout.Layout (project s i32) after (Proofs.CppConstructorFinish.reference (project s i32) 2)) :
    ∃ r : Receiver (exported s after n) (Proofs.CppConstructorFinish.reference (project s i32) 2) i32,
      r.counter.address = s.scalars.memory.length ∧ r.size.address = s.scalars.memory.length+1 ∧
      r.counter.value = (n : Int) ∧ r.size.value = (n : Int) ∧
      r.header = ⟨some s.objects.heap.allocations.length,s.scope,true,Proofs.CppVectorBindings.sizeLimit i32⟩ ∧
      r.view = ⟨s.objects.heap.headers.length,true⟩ := by
  obtain ⟨counter,slotC,addressC,writableC,valueC⟩ := field_of_cell s after n _ _ true (n : Int) initialized.2.2.1
  obtain ⟨size,slotS,addressS,writableS,valueS⟩ := field_of_cell s after n _ _ true (n : Int) initialized.2.2.2.1
  refine ⟨⟨counter,size,?_,writableC,s.objects.views.length,⟨s.objects.heap.headers.length,true⟩,
    ⟨some s.objects.heap.allocations.length,s.scope,true,Proofs.CppVectorBindings.sizeLimit i32⟩,
    located_vector s after n _ layout,resolved_vector s after n,rfl⟩,addressC,addressS,valueC,valueS,rfl,rfl⟩
  rw [slotC,slotS]
  simp [Proofs.CppConstructorFinish.reference,List.range_succ,Nat.add_assoc]

end Proofs.UfObjectConstructionContext
