import Proofs.BeatsSlotStmt

namespace Proofs.BeatsBindingCycle
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppNestedVectorStore Proofs.CppVectorOwnership Proofs.CppVector
open Proofs.BeatsSlotCycle (cycle uncycle rotate rotate_length rotate_lookup cycle_uncycle)

-- New binding i contains old binding cycle i. Every saved binding index must
-- therefore use the inverse permutation; allocation owners stay unchanged.
def rebind (f : Frame) : Frame := {f with bindings := rotate f.bindings}
def reference (r : Reference) : Reference := {r with slot := uncycle r.slot}

theorem object (f : Frame) (owner : Nat) (element : Element) :
    (rebind f).object owner element = f.object owner element := rfl
theorem maximum (f : Frame) (owner : Nat) : (rebind f).maximum owner = f.maximum owner := rfl
theorem headerOwner (f : Frame) (binding : Binding) :
    (rebind f).headerOwner binding = f.headerOwner binding := rfl

theorem lookup (f : Frame) (long : 16 ≤ f.bindings.length) (i : Nat) :
    (rebind f).bindings[uncycle i]? = f.bindings[i]? := by
  rw [rebind,rotate_lookup _ long,cycle_uncycle]

theorem resolve (f : Frame) (long : 16 ≤ f.bindings.length) (i : Nat) (element : Element) :
    (rebind f).resolve (uncycle i) element = f.resolve i element := by
  simp only [Frame.resolve,lookup f long,headerOwner,object,maximum]

theorem grant (f : Frame) (long : 16 ≤ f.bindings.length) (r : Reference) :
    (rebind f).grant (reference r) = f.grant r := by
  simp only [Frame.grant,reference,lookup f long,maximum]
  rfl

theorem elementRef (f : Frame) (long : 16 ≤ f.bindings.length) (i : Nat) (ty : Ty) (index : Int) :
    (rebind f).elementRef (uncycle i) ty index = (f.elementRef i ty index).map reference := by
  simp only [Frame.elementRef,resolve f long,Bind.bind,Option.map_bind,Function.comp_def]
  cases h : f.resolve i (.integer ty) with
  | none => rfl
  | some pair =>
    dsimp only [Option.bind_some]
    cases CppVector.elementRef pair.2 (accepts (.integer ty)) index <;> rfl

theorem read (f : Frame) (long : 16 ≤ f.bindings.length) (r : Reference) :
    (rebind f).read (reference r) = f.read r := by
  unfold Frame.read
  rw [grant f long]
  simp only [reference,object]

theorem updated (f : Frame) (owner : Nat) (old : Buffer Value) (result : Result Value Unit) :
    (rebind f).updated owner old result = rebind (f.updated owner old result) := rfl

theorem commit (f : Frame) (owner : Nat) (element : Element) (result : Result Value Unit) :
    (rebind f).commit owner element result = (f.commit owner element result).map rebind := by
  simp only [Frame.commit,object,updated]
  cases f.object owner element with
  | none => rfl
  | some pair =>
    dsimp only
    split
    · change (if (f.updated owner pair.1 result).state.wellFormed = true then
        some (rebind (f.updated owner pair.1 result)) else none) = _
      split <;> rfl
    · rfl

theorem write (f : Frame) (long : 16 ≤ f.bindings.length) (r : Reference) (value : Int) :
    (rebind f).write (reference r) value = (f.write r value).map rebind := by
  rcases r with ⟨index,ty,wr,address⟩
  unfold Frame.write
  rw [grant f long]
  simp only [reference,object,Bind.bind,Option.map_bind,Function.comp_def]
  cases f.grant ⟨index,ty,wr,address⟩ with
  | none => rfl
  | some writable =>
    dsimp only [Option.bind_some]
    cases wr <;> cases writable <;> simp [commit,Option.map_bind,Function.comp_def]

theorem addBinding (f : Frame) (long : 16 ≤ f.bindings.length) (binding : Binding) :
    (rebind f).addBinding binding = (rebind (f.addBinding binding).1,(f.addBinding binding).2) := by
  simp only [Frame.addBinding,rebind,Proofs.BeatsSlotCycle.rotate_append _ _ long,rotate_length _ long]

def location : Proofs.CppMixedInvoke.Location → Proofs.CppMixedInvoke.Location
  | .scalar i => .scalar i
  | .vector i => .vector (uncycle i)

def view (s : NState) : NState := {s with frame := rebind s.frame,slots := s.slots.map location}

theorem scalarSlot (s : NState) (i : Nat) : (view s).scalarSlot i = s.scalarSlot i := by
  simp only [NState.scalarSlot,view,List.getElem?_map]
  cases s.slots[i]? with
  | none => rfl
  | some loc => cases loc <;> rfl

theorem vectorSlot (s : NState) (i : Nat) :
    (view s).vectorSlot i = (s.vectorSlot i).map uncycle := by
  simp only [NState.vectorSlot,view,List.getElem?_map]
  cases s.slots[i]? with
  | none => rfl
  | some loc => cases loc <;> rfl

theorem scalarCell (s : NState) (i : Nat) (ty : Ty) :
    (view s).scalarCell i ty = s.scalarCell i ty := by
  unfold NState.scalarCell
  rw [scalarSlot]
  rfl

theorem vector_resolve (s : NState) (long : 16 ≤ s.frame.bindings.length) (i : Nat) (element : Element) :
    ((view s).vectorSlot i).bind (fun index => (view s).frame.resolve index element) =
      (s.vectorSlot i).bind (fun index => s.frame.resolve index element) := by
  rw [vectorSlot]
  cases h : s.vectorSlot i with
  | none => rfl
  | some index => exact resolve s.frame long index element

theorem work (s : NState) : (view s).work = s.work := rfl
theorem observe (s : NState) : view s.observe = (view s).observe := rfl
theorem charge (s : NState) (w p : Nat) : view (s.charge w p) = (view s).charge w p := rfl

-- Slots move separately in BeatsSlotCycle.permute. The binding view only
-- renames their stored reference indices, retaining their positions.
theorem slots_length (s : NState) : (view s).slots.length = s.slots.length := List.length_map location

def unreference (r : Reference) : Reference := {r with slot := cycle r.slot}
theorem reference_inverse (r : Reference) : unreference (reference r) = r := by
  simp only [unreference,reference,cycle_uncycle]

def restore (f : Frame) : Frame := {f with bindings := Proofs.BeatsSlotCycle.unrotate f.bindings}
theorem restore_rebind (f : Frame) (long : 16 ≤ f.bindings.length) : restore (rebind f) = f := by
  simp only [restore,rebind,Proofs.BeatsSlotCycle.unrotate_rotate _ long]

theorem rebind_restore (f : Frame) (long : 16 ≤ f.bindings.length) : rebind (restore f) = f := by
  simp only [restore,rebind,Proofs.BeatsSlotCycle.rotate_unrotate _ long]

end Proofs.BeatsBindingCycle
