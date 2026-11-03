import Proofs.CppMoveArgumentFacts
import Proofs.CppMoveCallBindings
import Proofs.QuotientFrame

namespace Proofs.CppMoveReceiverLayout
open Proofs.CppScalar Proofs.CppMoveContext

-- Typed by-value suffixes preserve the distinction between memory addresses
-- and callee scalar binding indices.
def valueArguments (ty : Ty) (values : List Int) : List SavedArgument :=
  values.map (fun value => .scalar ⟨ty,false,true⟩ (.value value))
def cells (ty : Ty) (values : List Int) : List Proofs.CppState.Cell :=
  values.map (fun value => ⟨ty,value⟩)
def addresses : Nat → Nat → List Nat
  | _,0 => []
  | start,count+1 => start::addresses (start+1) count
def valueBindings (start count : Nat) : List Proofs.CppState.Binding :=
  (addresses start count).map (fun address => ⟨address,true⟩)
def valueSlots (start count : Nat) : List Proofs.CppMixedInvoke.Location :=
  (addresses start count).map .scalar

theorem bind_values (s : Context) (ty : Ty) (values : List Int)
    (valid : ∀ value ∈ values, ty.valid value = true) :
    ∃ out, bindSavedAll s (valueArguments ty values) = some out ∧
      out.objects = s.objects ∧ out.scalars.memory = s.scalars.memory++cells ty values ∧
      out.scalars.bindings = s.scalars.bindings++valueBindings s.scalars.memory.length values.length ∧
      out.slots = s.slots++valueSlots s.scalars.bindings.length values.length ∧
      out.scope = s.scope ∧ out.scalars.baseMemory = s.scalars.baseMemory := by
  induction values generalizing s with
  | nil => exact ⟨s,rfl,rfl,by simp [cells],by simp [valueBindings,addresses],by simp [valueSlots,addresses],rfl,rfl⟩
  | cons value tail ih =>
    have valueValid := valid value (by simp)
    let scalars : Proofs.CppState.State := ({s.scalars with memory := s.scalars.memory++[⟨ty,value⟩], bindings := s.scalars.bindings++[⟨s.scalars.memory.length,true⟩]} : Proofs.CppState.State).observe 0
    let next := observe {s with scalars := scalars,slots := s.slots++[.scalar s.scalars.bindings.length]}
    have head : bindSaved s (.scalar ⟨ty,false,true⟩ (.value value)) = some next :=
      bindSaved_scalar_runs s ⟨ty,false,true⟩ (.value value) scalars
        (by simp [Proofs.CppState.bindArgument,valueValid,scalars])
    obtain ⟨out,run,objects,memory,bindings,slots,scope,base⟩ := ih next (fun v member => valid v (by simp [member]))
    refine ⟨out,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [valueArguments,List.map_cons,bindSavedAll,head,Bind.bind,Option.bind] using run
    · exact objects
    · simpa [next,observe,scalars,Proofs.CppState.State.observe,cells,List.append_assoc] using memory
    · simpa [next,observe,scalars,Proofs.CppState.State.observe,valueBindings,addresses,List.append_assoc] using bindings
    · simpa [next,observe,scalars,Proofs.CppState.State.observe,valueSlots,addresses,List.append_assoc] using slots
    · exact scope
    · exact base


-- A borrowed vector, a scalar field reference and homogeneous value suffix.
-- This is the original UF receiver profile, not all C++ class layouts.
def receiverArguments (borrow : Borrow) (ty : Ty) (address : Nat) (writable : Bool)
    (values : List Int) : List SavedArgument :=
  .vector borrow :: .scalar ⟨ty,true,writable⟩ (.reference address) :: valueArguments ty values

def receiverPrefix (s : Context) : List Proofs.CppState.Cell :=
  s.scalars.memory ++ List.replicate s.slots.length ⟨⟨1,false,true⟩,0⟩ ++ [⟨⟨1,false,true⟩,0⟩]

theorem prepare_receiver (s : Context) (borrow : Borrow) (header : Proofs.CppMoveHeaders.Header)
    (found : s.objects.heap.header borrow.header = some header)
    (permission : borrow.writable = true → header.writable = true)
    (ty : Ty) (address : Nat) (writable : Bool) (count : Int)
    (counter : s.scalars.memory[address]? = some ⟨ty,count⟩)
    (countValid : ty.valid count = true) (values : List Int)
    (valid : ∀ value ∈ values, ty.valid value = true) :
    ∃ out, prepareSaved s (receiverArguments borrow ty address writable values) = some out ∧
      out.objects = ⟨s.objects.heap,s.objects.views++[⟨borrow.header,borrow.writable⟩]⟩ ∧
      out.scalars.memory = receiverPrefix s ++ cells ty values ∧
      out.scalars.bindings = ⟨address,writable⟩ :: valueBindings (receiverPrefix s).length values.length ∧
      out.slots = .vector s.objects.views.length :: .scalar 0 :: valueSlots 1 values.length ∧
      out.scope = s.scope+1 ∧ out.scalars.baseMemory = s.scalars.baseMemory := by
  let initial := prepareBase s (values.length+2)
  let borrowed : Context := observe {initial with
    objects := ⟨s.objects.heap,s.objects.views++[⟨borrow.header,borrow.writable⟩]⟩,
    slots := [.vector s.objects.views.length],
    scalars := ({initial.scalars with memory := initial.scalars.memory++[⟨⟨1,false,true⟩,0⟩]} : Proofs.CppState.State).observe 0}
  have installed := installBorrow_runs initial borrow header found permission
  have first : bindSaved initial (.vector borrow) = some borrowed := by
    simp only [bindSaved,installed,Bind.bind,Option.bind]
    rfl
  have cell : borrowed.scalars.memory[address]? = some ⟨ty,count⟩ := by
    have inside := (List.getElem?_eq_some_iff.mp counter).1
    simp only [borrowed,observe,Proofs.CppState.State.observe,initial,prepareBase]
    rw [List.getElem?_append_left (by simp; omega),List.getElem?_append_left inside]
    exact counter
  let scalars : Proofs.CppState.State := ({borrowed.scalars with bindings := [⟨address,writable⟩]} : Proofs.CppState.State).observe 0
  let referenced : Context := observe {borrowed with scalars := scalars,slots := borrowed.slots++[.scalar 0]}
  have bound : Proofs.CppState.bindArgument borrowed.scalars ⟨ty,true,writable⟩ (.reference address) = some scalars := by
    simp only [Proofs.CppState.bindArgument,cell]
    simp [countValid,scalars,borrowed,initial,prepareBase,observe,Proofs.CppState.State.observe]
  have second : bindSaved borrowed (.scalar ⟨ty,true,writable⟩ (.reference address)) = some referenced := by
    simpa [referenced,borrowed,initial,prepareBase,observe,Proofs.CppState.State.observe] using bindSaved_scalar_runs borrowed ⟨ty,true,writable⟩ (.reference address) scalars bound
  obtain ⟨out,run,objects,memory,bindings,slots,scope,baseline⟩ := bind_values referenced ty values valid
  refine ⟨out,?_,?_,?_,?_,?_,?_,?_⟩
  · have len : (receiverArguments borrow ty address writable values).length = values.length+2 := by simp [receiverArguments,valueArguments]
    unfold prepareSaved
    rw [len]
    change bindSavedAll initial (.vector borrow :: .scalar ⟨ty,true,writable⟩ (.reference address) :: valueArguments ty values) = some out
    simpa only [bindSavedAll,first,second,Bind.bind,Option.bind] using run
  · exact objects
  · simpa [referenced,scalars,borrowed,initial,prepareBase,observe,Proofs.CppState.State.observe,receiverPrefix] using memory
  · simpa [referenced,scalars,borrowed,initial,prepareBase,observe,Proofs.CppState.State.observe,receiverPrefix] using bindings
  · simpa [referenced,scalars,borrowed,initial,prepareBase,observe,Proofs.CppState.State.observe] using slots
  · exact scope
  · exact baseline

-- Argument resolution is still an input obligation. The theorem constructs
-- preparation success and its layout instead of assuming either.
theorem prepareArguments_receiver (s last : Context) (borrow : Borrow)
    (header : Proofs.CppMoveHeaders.Header)
    (found : s.objects.heap.header borrow.header = some header)
    (permission : borrow.writable = true → header.writable = true)
    (ty : Ty) (address : Nat) (writable : Bool) (count : Int)
    (counter : s.scalars.memory[address]? = some ⟨ty,count⟩)
    (countValid : ty.valid count = true) (values : List Int)
    (valid : ∀ value ∈ values, ty.valid value = true)
    (parameters : List Proofs.CppVectorBindings.Parameter)
    (arguments : List Proofs.CppNestedCall.NArgument)
    (resolved : resolveArguments s ty parameters arguments =
      some (last,receiverArguments borrow ty address writable values)) :
    ∃ out, prepareArguments s ty parameters arguments = some out ∧
      out.objects = ⟨s.objects.heap,s.objects.views++[⟨borrow.header,borrow.writable⟩]⟩ ∧
      out.scalars.memory = receiverPrefix s ++ cells ty values ∧
      out.scalars.bindings = ⟨address,writable⟩ :: valueBindings (receiverPrefix s).length values.length ∧
      out.slots = .vector s.objects.views.length :: .scalar 0 :: valueSlots 1 values.length ∧
      out.scope = s.scope+1 ∧ out.scalars.baseMemory = s.scalars.baseMemory := by
  have stable := Proofs.CppMoveArgumentFacts.resolveArguments_stable s last ty parameters arguments _ resolved
  have lastFound : last.objects.heap.header borrow.header = some header := by rw [stable.objects]; exact found
  have lastCounter : last.scalars.memory[address]? = some ⟨ty,count⟩ := by rw [stable.memory]; exact counter
  obtain ⟨out,run,objects,memory,bindings,slots,scope,base⟩ :=
    prepare_receiver last borrow header lastFound permission ty address writable count lastCounter countValid values valid
  have prefixEq : receiverPrefix last = receiverPrefix s := by simp only [receiverPrefix,stable.memory,stable.slots]
  refine ⟨out,by simp [prepareArguments,resolved,run],?_,?_,?_,?_,?_,?_⟩
  · simpa only [stable.objects] using objects
  · simpa only [prefixEq] using memory
  · simpa only [prefixEq] using bindings
  · simpa only [stable.objects] using slots
  · simpa only [stable.scope] using scope
  · simpa only [stable.baseline] using base

-- Construct compaction and QS from the prepared view and scalar slots.
-- Frame well-formedness / UF-specific FW must be established separately.
theorem compact_receiver (out : Context) (ty : Ty) (viewSlot count : Nat)
    (view : Proofs.CppMoveViews.View)
    (found : out.objects.views[viewSlot]? = some view)
    (slots : out.slots = .vector viewSlot :: .scalar 0 :: valueSlots 1 count) :
    ∃ initial, Proofs.CppMoveCallBindings.compact (project out ty) = some initial ∧
      Proofs.QuotientFrame.QS initial [] out.scalars.baseMemory out.scope
        out.scalars.memory out.scalars.bindings (.vector 0 :: .scalar 0 :: valueSlots 1 count) ∧
      initial.frame.state = (project out ty).frame.state ∧
      initial.frame.bindings = [Proofs.CppMoveFrame.viewBinding out.objects ty view] := by
  have binding := Proofs.CppMoveFrame.materialize_view_binding out.objects ty viewSlot view found
  have locations : (project out ty).slots =
      .vector (out.objects.heap.grants.length+viewSlot) ::
        ((0::addresses 1 count).map Proofs.CppMixedInvoke.Location.scalar) := by
    simp [project,slots,valueSlots,List.map_map,location,Function.comp_def]
  have run := Proofs.CppMoveCallBindings.compact_one_vector (project out ty)
    (out.objects.heap.grants.length+viewSlot) (Proofs.CppMoveFrame.viewBinding out.objects ty view)
    (0::addresses 1 count) locations binding
  refine ⟨_,run,?_,rfl,rfl⟩
  exact ⟨by simp [valueSlots],by simp [project],rfl,rfl,rfl⟩

end Proofs.CppMoveReceiverLayout
