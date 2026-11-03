import Proofs.CppClassAssign

namespace Proofs.CppClassAssignValues
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppClassAssign Proofs.CppConstructorFinish Proofs.CppClassCopy
open Proofs.DynamicResultValid

theorem scalar_other (s : NState) (targetBinding : Proofs.CppState.Binding) (targetCell : Proofs.CppState.Cell)
    (value : Int) (slot : Nat) (ty : Ty) (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
    (found : s.scalarCell slot ty = some (binding,cell)) (different : targetBinding.address ≠ binding.address) :
    (scalarStep s targetBinding targetCell value).scalarCell slot ty = some (binding,cell) := by
  obtain ⟨index,slotFound,bindingFound,memoryFound,typed,valid⟩ := Proofs.ExtremaCall.scalarCell_facts found
  have metadata := scalar_fields s targetBinding targetCell value
  unfold NState.scalarCell NState.scalarSlot
  rw [metadata.2.1,metadata.2.2.2.1,metadata.2.2.2.2.1]
  simp [slotFound,bindingFound,List.getElem?_set_ne different,memoryFound,typed,valid]

def Separate (s : NState) (targets : List Nat) (address : Nat) : Prop :=
  ∀ target ∈ targets, ∀ index binding, s.scalarSlot target = some index →
    s.scalars.bindings[index]? = some binding → binding.address ≠ address

theorem separate_transfer (s t : NState) (targets : List Nat) (address : Nat)
    (slots : t.slots = s.slots) (bindings : t.scalars.bindings = s.scalars.bindings)
    (separate : Separate s targets address) : Separate t targets address := by
  intro target member index binding slot found
  have oldSlot : s.scalarSlot target = some index := by simpa only [NState.scalarSlot,slots] using slot
  rw [bindings] at found
  exact separate target member index binding oldSlot found

theorem fields_other (s out : NState) (targets sources : List Nat) (fields : List (Ty × Bool))
    (ran : assignFields s targets sources fields = some out) (slot : Nat) (ty : Ty)
    (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
    (found : s.scalarCell slot ty = some (binding,cell)) (separate : Separate s targets binding.address) :
    out.scalarCell slot ty = some (binding,cell) := by
  induction targets generalizing s sources fields with
  | nil => cases sources <;> cases fields <;> simp_all [assignFields]
  | cons target targets ih =>
    cases sources with
    | nil => simp [assignFields] at ran
    | cons source sources =>
      cases fields with
      | nil => simp [assignFields] at ran
      | cons field fields =>
        obtain ⟨fieldTy,writable⟩ := field
        unfold assignFields at ran
        split at ran
        · obtain ⟨next,head,tail⟩ := bind_some _ _ _ ran
          obtain ⟨tb,sb,tc,sc,targetCell,_,_,nextEq,_⟩ := scalar_success s next target source fieldTy head
          obtain ⟨index,targetSlot,targetBinding,_,_,_⟩ := Proofs.ExtremaCall.scalarCell_facts targetCell
          have oldSlot : s.scalarSlot target = some index := by simp [NState.scalarSlot,targetSlot]
          have different := separate target (by simp) index tb oldSlot targetBinding
          have kept := scalar_other s tb tc sc.value slot ty binding cell found different
          rw [← nextEq] at kept
          have metadata := scalar_fields s tb tc sc.value
          rw [← nextEq] at metadata
          have tailSeparation : Separate s targets binding.address := by
            intro other member i b slot found
            exact separate other (by simp [member]) i b slot found
          have nextSeparation := separate_transfer s next targets binding.address metadata.2.1 metadata.2.2.2.1 tailSeparation
          exact ih next sources fields tail kept nextSeparation
        · simp at ran

theorem class_other (s out : NState) (target source result : ObjectRef) (profile : Profile)
    (ran : assignClass s target source profile = some (out,result)) (slot : Nat) (ty : Ty)
    (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
    (found : s.scalarCell slot ty = some (binding,cell)) (separate : Separate s target.scalarSlots binding.address) :
    out.scalarCell slot ty = some (binding,cell) := by
  obtain ⟨_,a,b,frame,_,_,_,fieldsRun,_⟩ := class_success s out target source result profile ran
  exact fields_other (vectorState s frame) out target.scalarSlots source.scalarSlots profile.scalarFields fieldsRun
    slot ty binding cell found separate



-- A typed successful write yields the assigned value at its target slot.
theorem scalar_written (s : NState) (target : Nat) (ty : Ty)
    (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell) (value : Int)
    (found : s.scalarCell target ty = some (binding,cell)) (valid : ty.valid value = true) :
    (scalarStep s binding cell value).scalarCell target ty = some (binding,⟨ty,value⟩) := by
  obtain ⟨index,slotFound,bindingFound,memoryFound,typed,_⟩ := Proofs.ExtremaCall.scalarCell_facts found
  have inside := (List.getElem?_eq_some_iff.mp memoryFound).1
  have metadata := scalar_fields s binding cell value
  unfold NState.scalarCell NState.scalarSlot
  rw [metadata.2.1,metadata.2.2.2.1,metadata.2.2.2.2.1]
  simp [slotFound,bindingFound,List.getElem?_set_self inside,typed,valid]

-- Later fields must not overwrite the head field's storage address.
theorem fields_head (s out : NState) (target source : Nat) (targets sources : List Nat)
    (ty : Ty) (fields : List (Ty × Bool))
    (ran : assignFields s (target::targets) (source::sources) ((ty,true)::fields) = some out)
    (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
    (found : s.scalarCell target ty = some (binding,cell))
    (separate : Separate s targets binding.address) :
    ∃ sb sc, s.scalarCell source ty = some (sb,sc) ∧
      out.scalarCell target ty = some (binding,⟨ty,sc.value⟩) := by
  simp only [assignFields,ite_true] at ran
  obtain ⟨next,head,tail⟩ := bind_some _ _ _ ran
  obtain ⟨tb,sb,tc,sc,targetFound,sourceFound,_,same,_⟩ := scalar_success s next target source ty head
  have equal := Prod.mk.inj (Option.some.inj (targetFound.symm.trans found))
  have bindingEq := equal.1
  have cellEq := equal.2
  subst tb
  subst tc
  have accepted := (Proofs.CppClassCopyCommands.scalar_cell_facts s source ty sb sc sourceFound).2
  have written := scalar_written s target ty binding cell sc.value found accepted
  rw [← same] at written
  have metadata := scalar_fields s binding cell sc.value
  rw [← same] at metadata
  have separated := separate_transfer s next targets binding.address metadata.2.1 metadata.2.2.2.1 separate
  exact ⟨sb,sc,sourceFound,fields_other next out targets sources fields tail target ty binding ⟨ty,sc.value⟩ written separated⟩


theorem separate_single (s : NState) (target : Nat) (ty : Ty)
    (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell) (address : Nat)
    (found : s.scalarCell target ty = some (binding,cell)) (different : binding.address ≠ address) :
    Separate s [target] address := by
  intro other member index b slot lookup
  have same : other = target := by simpa using member
  subst other
  obtain ⟨actual,rawSlot,bindingFound,_,_,_⟩ := Proofs.ExtremaCall.scalarCell_facts found
  have typedSlot : s.scalarSlot target = some actual := by simp [NState.scalarSlot,rawSlot]
  have equal : index = actual := Option.some.inj (slot.symm.trans typedSlot)
  subst index
  have equal : b = binding := Option.some.inj (lookup.symm.trans bindingFound)
  subst b
  exact different

-- Two distinct destination fields, including a self-assignment source, copy
-- the original typed source values in declaration order.
theorem two_fields (s out : NState) (t0 t1 s0 s1 : Nat) (ty0 ty1 : Ty)
    (tb0 tb1 sb0 sb1 : Proofs.CppState.Binding) (tc0 tc1 sc0 sc1 : Proofs.CppState.Cell)
    (target0 : s.scalarCell t0 ty0 = some (tb0,tc0))
    (target1 : s.scalarCell t1 ty1 = some (tb1,tc1))
    (source0 : s.scalarCell s0 ty0 = some (sb0,sc0))
    (source1 : s.scalarCell s1 ty1 = some (sb1,sc1))
    (targetsDifferent : tb0.address ≠ tb1.address) (sourceDifferent : tb0.address ≠ sb1.address)
    (ran : assignFields s [t0,t1] [s0,s1] [(ty0,true),(ty1,true)] = some out) :
    out.scalarCell t0 ty0 = some (tb0,⟨ty0,sc0.value⟩) ∧
    out.scalarCell t1 ty1 = some (tb1,⟨ty1,sc1.value⟩) := by
  have separate := separate_single s t1 ty1 tb1 tc1 tb0.address target1 (Ne.symm targetsDifferent)
  obtain ⟨b,c,found,headKept⟩ := fields_head s out t0 s0 [t1] [s1] ty0 [(ty1,true)] ran tb0 tc0 target0 separate
  have sourceEq := Prod.mk.inj (Option.some.inj (found.symm.trans source0))
  have valueEq : c.value = sc0.value := congrArg Proofs.CppState.Cell.value sourceEq.2
  rw [valueEq] at headKept
  simp only [assignFields,ite_true] at ran
  obtain ⟨next,head,tail⟩ := bind_some _ _ _ ran
  obtain ⟨tb,sb,tc,sc,targetFound,sourceFound,_,nextEq,_⟩ := scalar_success s next t0 s0 ty0 head
  have te := Prod.mk.inj (Option.some.inj (targetFound.symm.trans target0))
  have se := Prod.mk.inj (Option.some.inj (sourceFound.symm.trans source0))
  have tbEq := te.1
  have tcEq := te.2
  have sbEq := se.1
  have scEq := se.2
  subst tb
  subst tc
  subst sb
  subst sc
  have nextTarget := scalar_other s tb0 tc0 sc0.value t1 ty1 tb1 tc1 target1 targetsDifferent
  have nextSource := scalar_other s tb0 tc0 sc0.value s1 ty1 sb1 sc1 source1 sourceDifferent
  rw [← nextEq] at nextTarget nextSource
  have last : assignScalar next t1 s1 ty1 = some out := by simpa [assignFields] using tail
  obtain ⟨tb,sb,tc,sc,targetFound,sourceFound,_,lastEq,_⟩ := scalar_success next out t1 s1 ty1 last
  have te := Prod.mk.inj (Option.some.inj (targetFound.symm.trans nextTarget))
  have se := Prod.mk.inj (Option.some.inj (sourceFound.symm.trans nextSource))
  have tbEq := te.1
  have tcEq := te.2
  have sbEq := se.1
  have scEq := se.2
  subst tb
  subst tc
  subst sb
  subst sc
  have accepted := (Proofs.CppClassCopyCommands.scalar_cell_facts s s1 ty1 sb1 sc1 source1).2
  have written := scalar_written next t1 ty1 tb1 tc1 sc1.value nextTarget accepted
  rw [← lastEq] at written
  exact ⟨headKept,written⟩


theorem class_two_fields (s out : NState) (target source result : ObjectRef) (profile : Profile)
    (t0 t1 s0 s1 : Nat) (ty0 ty1 : Ty)
    (tb0 tb1 sb0 sb1 : Proofs.CppState.Binding) (tc0 tc1 sc0 sc1 : Proofs.CppState.Cell)
    (targetSlots : target.scalarSlots = [t0,t1]) (sourceSlots : source.scalarSlots = [s0,s1])
    (types : profile.scalarFields = [(ty0,true),(ty1,true)])
    (target0 : s.scalarCell t0 ty0 = some (tb0,tc0))
    (target1 : s.scalarCell t1 ty1 = some (tb1,tc1))
    (source0 : s.scalarCell s0 ty0 = some (sb0,sc0))
    (source1 : s.scalarCell s1 ty1 = some (sb1,sc1))
    (targetsDifferent : tb0.address ≠ tb1.address) (sourceDifferent : tb0.address ≠ sb1.address)
    (ran : assignClass s target source profile = some (out,result)) :
    out.scalarCell t0 ty0 = some (tb0,⟨ty0,sc0.value⟩) ∧
    out.scalarCell t1 ty1 = some (tb1,⟨ty1,sc1.value⟩) := by
  obtain ⟨_,a,b,frame,_,_,_,fieldsRun,_⟩ := class_success s out target source result profile ran
  rw [targetSlots,sourceSlots,types] at fieldsRun
  exact two_fields (vectorState s frame) out t0 t1 s0 s1 ty0 ty1 tb0 tb1 sb0 sb1 tc0 tc1 sc0 sc1
    target0 target1 source0 source1 targetsDifferent sourceDifferent fieldsRun

end Proofs.CppClassAssignValues
