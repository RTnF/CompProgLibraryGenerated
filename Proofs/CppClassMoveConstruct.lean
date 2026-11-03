import Proofs.CppMoveClass
import Proofs.CppClassCopyCommands
import Proofs.CppConstructorPeak
import Proofs.CppMoveReadReceiver

namespace Proofs.CppClassMoveConstruct
open Proofs.CppMoveContext Proofs.CppNestedProgram Proofs.CppConstructorFinish
open Proofs.CppClassCopy Proofs.CppScalar

-- Move changes only object storage; member scalar loads still read the original cells.
def ScalarReady (s : NState) (slots : List Nat) (fields : List (Ty × Bool)) : Prop :=
  slots.length = fields.length ∧
    ∀ slot field, (slot,field) ∈ slots.zip fields →
      ∃ binding cell, s.scalarCell slot field.1 = some (binding,cell)

theorem capture_ready (s : NState) (slots : List Nat) (fields : List (Ty × Bool))
    (ready : ScalarReady s slots fields) :
    ∃ values, CppClassCopy.captureAll s slots fields = some values := by
  induction slots generalizing fields with
  | nil =>
    cases fields with
    | nil => exact ⟨[],rfl⟩
    | cons field fields => simp [ScalarReady] at ready
  | cons slot slots ih =>
    cases fields with
    | nil => simp [ScalarReady] at ready
    | cons field fields =>
      have first := ready.2 slot field (by simp)
      obtain ⟨binding,cell,found⟩ := first
      have tailReady : ScalarReady s slots fields := by
        refine ⟨by have lengths := ready.1; simpa using lengths,?_⟩
        intro index ty member
        exact ready.2 index ty (List.mem_cons_of_mem _ member)
      obtain ⟨values,captured⟩ := ih fields tailReady
      refine ⟨(cell,field.2)::values,?_⟩
      rw [Proofs.CppClassCopyCommands.capture_all_cons]
      simp [CppClassCopy.capture,found,captured]

def finish (s : Context) (objects : Proofs.CppMoveViews.State Int)
    (view : Nat) (values : List ScalarValue) : Context :=
  let scalars : Proofs.CppState.State := {s.scalars with
    memory := s.scalars.memory++values.map Prod.fst
    bindings := s.scalars.bindings++scalarBindings s.scalars.memory.length values
    work := s.scalars.work+(values.length+1)}
  observe {s with
    objects := objects
    scalars := scalars.observe 0
    slots := s.slots++(.vector view::scalarLocations s.scalars.bindings.length values.length)}

theorem scalarCell_after_objects (s : Context) (objects : Proofs.CppMoveViews.State Int)
    (vectorTy fieldTy : Ty) (slot : Nat) :
    (project {s with objects := objects} vectorTy).scalarCell slot fieldTy =
      (project s vectorTy).scalarCell slot fieldTy := by
  rw [project_scalarCell,project_scalarCell]
  rfl

theorem capture_after_objects (s : Context) (objects : Proofs.CppMoveViews.State Int)
    (vectorTy : Ty) (slots : List Nat) (fields : List (Ty × Bool)) :
    CppClassCopy.captureAll (project {s with objects := objects} vectorTy) slots fields =
      CppClassCopy.captureAll (project s vectorTy) slots fields := by
  simp only [CppClassCopy.captureAll,CppClassCopy.capture,scalarCell_after_objects]

def constructClass (s : Context) (source : ObjectRef) (profile : Profile) :
    Option (Context × ObjectRef) := do
  let view ← vectorView s source.vectorSlot
  let (objects,target) ← Proofs.CppMoveViews.construct s.objects profile.element.valid
    view s.scope profile.vectorWritable
  let values ← CppClassCopy.captureAll (project s profile.element) source.scalarSlots profile.scalarFields
  some (finish s objects target values,reference (project s profile.element) values.length)

theorem construct_runs (s : Context) (source : ObjectRef) (profile : Profile)
    (view target : Nat) (objects : Proofs.CppMoveViews.State Int) (values : List ScalarValue)
    (located : vectorView s source.vectorSlot = some view)
    (moved : Proofs.CppMoveViews.construct s.objects profile.element.valid view s.scope
      profile.vectorWritable = some (objects,target))
    (captured : CppClassCopy.captureAll (project s profile.element) source.scalarSlots
      profile.scalarFields = some values) :
    constructClass s source profile =
      some (finish s objects target values,reference (project s profile.element) values.length) := by
  simp [constructClass,located,moved,captured]

theorem construct_success (s out : Context) (source target : ObjectRef) (profile : Profile)
    (run : constructClass s source profile = some (out,target)) :
    ∃ view objects slot values,
      vectorView s source.vectorSlot = some view ∧
      Proofs.CppMoveViews.construct s.objects profile.element.valid view s.scope
        profile.vectorWritable = some (objects,slot) ∧
      CppClassCopy.captureAll (project s profile.element) source.scalarSlots profile.scalarFields = some values ∧
      out = finish s objects slot values ∧ target = reference (project s profile.element) values.length := by
  unfold constructClass at run
  obtain ⟨view,located,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  obtain ⟨pair,moved,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  rcases pair with ⟨objects,slot⟩
  obtain ⟨values,captured,done⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  have equal := Prod.mk.inj (Option.some.inj done)
  exact ⟨view,objects,slot,values,located,moved,captured,equal.1.symm,equal.2.symm⟩

theorem construct_ready (s : Context) (source : ObjectRef) (profile : Profile)
    (slot : Nat) (view : Proofs.CppMoveViews.View) (header : Proofs.CppMoveHeaders.Header)
    (located : vectorView s source.vectorSlot = some slot)
    (resolved : Proofs.CppMoveViews.resolve s.objects slot = some (view,header))
    (writable : view.writable = true)
    (readable : Proofs.CppMoveHeaders.readable s.objects.heap header profile.element.valid = true)
    (scalars : ScalarReady (project s profile.element) source.scalarSlots profile.scalarFields) :
    ∃ out target, constructClass s source profile = some (out,target) := by
  have moved := Proofs.CppMoveViews.construct_ready s.objects profile.element.valid slot s.scope
    profile.vectorWritable view header resolved writable readable
  obtain ⟨values,captured⟩ := capture_ready (project s profile.element) source.scalarSlots profile.scalarFields scalars
  exact ⟨_,_,construct_runs s source profile slot _ _ values located moved captured⟩

theorem finish_metadata (s : Context) (objects : Proofs.CppMoveViews.State Int)
    (view : Nat) (values : List ScalarValue) :
    (finish s objects view values).objects = objects ∧
    (finish s objects view values).scalars.memory = s.scalars.memory++values.map Prod.fst ∧
    (finish s objects view values).scalars.bindings =
      s.scalars.bindings++scalarBindings s.scalars.memory.length values ∧
    (finish s objects view values).slots =
      s.slots++(.vector view::scalarLocations s.scalars.bindings.length values.length) ∧
    (finish s objects view values).scope = s.scope ∧
    (finish s objects view values).scalars.baseMemory = s.scalars.baseMemory :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem capture_length (s : NState) (slots : List Nat) (fields : List (Ty × Bool))
    (values : List ScalarValue) (captured : CppClassCopy.captureAll s slots fields = some values) :
    values.length = fields.length := by
  have reads := Proofs.CppClassCopyCommands.source_values_of_capture s slots fields values captured
  clear captured
  induction slots generalizing fields values with
  | nil => cases fields <;> cases values <;> simp_all [Proofs.CppClassCopyCommands.SourceValues]
  | cons slot slots ih =>
    cases fields with
    | nil => simp [Proofs.CppClassCopyCommands.SourceValues] at reads
    | cons field fields =>
      cases values with
      | nil => simp [Proofs.CppClassCopyCommands.SourceValues] at reads
      | cons value values =>
        exact congrArg Nat.succ (ih fields values reads.2)

theorem old_scalarSlot (s : Context) (objects : Proofs.CppMoveViews.State Int)
    (view : Nat) (values : List ScalarValue) (slot : Nat) (inside : slot < s.slots.length) :
    scalarSlot (finish s objects view values) slot = scalarSlot s slot := by
  simp only [scalarSlot,finish,observe,List.getElem?_append_left inside]

def oldField (s : Context) (objects : Proofs.CppMoveViews.State Int)
    (view : Nat) (values : List ScalarValue) (ty : Ty)
    (field : Proofs.CppMoveObjectReceiver.Field s ty) :
    Proofs.CppMoveObjectReceiver.Field (finish s objects view values) ty := by
  have slotInside : field.slot < s.slots.length := by
    have located := field.located
    unfold scalarSlot at located
    obtain ⟨loc,found,_⟩ := Proofs.DynamicResultValid.bind_some _ _ _ located
    exact (List.getElem?_eq_some_iff.mp found).1
  have bindingInside := (List.getElem?_eq_some_iff.mp field.bound).1
  have addressInside := (List.getElem?_eq_some_iff.mp field.found).1
  refine ⟨field.slot,field.index,field.address,field.writable,field.value,?_,?_,?_,field.valid⟩
  · rw [old_scalarSlot s objects view values field.slot slotInside]
    exact field.located
  · change (s.scalars.bindings++scalarBindings s.scalars.memory.length values)[field.index]? = _
    rw [List.getElem?_append_left bindingInside]
    exact field.bound
  · change (s.scalars.memory++values.map Prod.fst)[field.address]? = _
    rw [List.getElem?_append_left addressInside]
    exact field.found

def newField (s : Context) (objects : Proofs.CppMoveViews.State Int)
    (view : Nat) (values : List ScalarValue) (j : Nat) (cell : Proofs.CppState.Cell) (wr : Bool)
    (found : values[j]? = some (cell,wr)) (valid : cell.type.valid cell.value = true) :
    Proofs.CppMoveObjectReceiver.Field (finish s objects view values) cell.type := by
  have inside : j < values.length := (List.getElem?_eq_some_iff.mp found).1
  refine ⟨s.slots.length+1+j,s.scalars.bindings.length+j,s.scalars.memory.length+j,wr,cell.value,?_,?_,?_,valid⟩
  · unfold scalarSlot
    have located : (finish s objects view values).slots[s.slots.length+1+j]? =
        some (.scalar (s.scalars.bindings.length+j)) := by
      change (s.slots++(.vector view::scalarLocations s.scalars.bindings.length values.length))[s.slots.length+1+j]? = _
      rw [List.getElem?_append_right (by omega)]
      have diff : s.slots.length+1+j-s.slots.length = j+1 := by omega
      rw [diff]
      change (scalarLocations s.scalars.bindings.length values.length)[j]? = _
      simp [scalarLocations,List.getElem?_map,List.getElem?_range inside]
    simp only [located,Bind.bind,Option.bind]
  · change (s.scalars.bindings++scalarBindings s.scalars.memory.length values)[s.scalars.bindings.length+j]? = _
    rw [List.getElem?_append_right (by omega)]
    simpa using scalarBindings_get values s.scalars.memory.length j cell wr found
  · change (s.scalars.memory++values.map Prod.fst)[s.scalars.memory.length+j]? = _
    rw [List.getElem?_append_right (by omega)]
    simp [List.getElem?_map,found]

def receiverTwo (s : Context) (objects : Proofs.CppMoveViews.State Int)
    (slot : Nat) (ty : Ty) (count n : Int) (wc wn : Bool)
    (cv : ty.valid count = true) (nv : ty.valid n = true)
    (view : Proofs.CppMoveViews.View) (header : Proofs.CppMoveHeaders.Header)
    (resolved : Proofs.CppMoveViews.resolve objects slot = some (view,header)) :
    Proofs.CppMoveReadReceiver.ReadReceiver
      (finish s objects slot [(⟨ty,count⟩,wc),(⟨ty,n⟩,wn)])
      (reference (project s ty) 2) ty := by
  refine ⟨newField s objects slot _ 0 ⟨ty,count⟩ wc rfl cv,
    newField s objects slot _ 1 ⟨ty,n⟩ wn rfl nv,?_,slot,view,header,?_,resolved⟩
  · simp [reference,project,List.range_succ,newField]
  · unfold vectorView
    have length : (project s ty).slots.length = s.slots.length := by simp [project]
    rw [show (reference (project s ty) 2).vectorSlot = s.slots.length from length]
    change (do let loc ← (s.slots++(.vector slot::scalarLocations s.scalars.bindings.length 2))[s.slots.length]?
               let .vector view := loc | none
               some view) = some slot
    simp

theorem resources (s : Context) (profile : Profile) (slot target : Nat)
    (objects : Proofs.CppMoveViews.State Int) (values : List ScalarValue)
    (moved : Proofs.CppMoveViews.construct s.objects profile.element.valid slot s.scope
      profile.vectorWritable = some (objects,target)) :
    work (finish s objects target values) = work s+values.length+2 ∧
    objects.heap.liveSpace = s.objects.heap.liveSpace+1 ∧
    objects.heap.peak = max s.objects.heap.peak (objects.heap.liveSpace-s.objects.heap.baseSpace) ∧
    objects.heap.baseSpace = s.objects.heap.baseSpace := by
  obtain ⟨heapWork,space,peak,base⟩ := Proofs.CppMoveViews.construct_resources
    s.objects objects profile.element.valid slot s.scope target profile.vectorWritable moved
  refine ⟨?_,space,peak,base⟩
  simp only [finish,observe,work,Proofs.CppState.State.observe,heapWork]
  omega


theorem construct_invariants (s out : Context) (source target : ObjectRef) (profile : Profile)
    (run : constructClass s source profile = some (out,target))
    (unique : Proofs.CppMoveHeaders.Unique s.objects.heap)
    (covered : Proofs.CppMoveHeaders.OwnsAll s.objects.heap)
    (live : Proofs.CppMoveSpace.HeadersLive s.objects.heap)
    (valid : Proofs.CppMoveFrame.AllocationsValid s.objects.heap profile.element) :
    Proofs.CppMoveHeaders.Unique out.objects.heap ∧
    Proofs.CppMoveHeaders.OwnsAll out.objects.heap ∧
    Proofs.CppMoveSpace.HeadersLive out.objects.heap ∧
    Proofs.CppMoveFrame.AllocationsValid out.objects.heap profile.element := by
  obtain ⟨view,objects,slot,values,_,moved,_,rfl,_⟩ := construct_success s out source target profile run
  exact ⟨Proofs.CppMoveViews.construct_unique s.objects objects profile.element.valid view s.scope slot profile.vectorWritable moved unique,
    Proofs.CppMoveViews.construct_ownsAll s.objects objects profile.element.valid view s.scope slot profile.vectorWritable moved covered,
    Proofs.CppMoveSpace.construct_headersLive s.objects objects profile.element.valid view s.scope slot profile.vectorWritable moved live,
    Proofs.CppMoveFrame.construct_allocationsValid s.objects objects profile.element profile.element.valid view s.scope slot profile.vectorWritable moved valid⟩

theorem construct_storage (s out : Context) (source target : ObjectRef) (profile : Profile)
    (run : constructClass s source profile = some (out,target)) :
    out.objects.heap.allocations = s.objects.heap.allocations ∧
    out.objects.heap.grants = s.objects.heap.grants ∧
    (∀ grant, Proofs.CppMoveHeaders.read out.objects.heap profile.element.valid grant =
      Proofs.CppMoveHeaders.read s.objects.heap profile.element.valid grant) := by
  obtain ⟨view,objects,slot,values,_,moved,_,rfl,_⟩ := construct_success s out source target profile run
  obtain ⟨v,h,destination,_,_,core,_,_⟩ := Proofs.CppMoveViews.construct_success
    s.objects objects profile.element.valid view s.scope slot profile.vectorWritable moved
  obtain ⟨old,_,_,heap⟩ := Proofs.CppMoveHeaders.move_construct_success
    s.objects.heap objects.heap profile.element.valid v.header s.scope destination profile.vectorWritable core
  refine ⟨?_,?_,?_⟩
  · change objects.heap.allocations = _
    rw [heap]
    rfl
  · change objects.heap.grants = _
    rw [heap]
    rfl
  · intro grant
    exact Proofs.CppMoveViews.construct_read s.objects objects profile.element.valid view s.scope slot grant profile.vectorWritable moved

theorem finish_peak (s : Context) (objects : Proofs.CppMoveViews.State Int)
    (view : Nat) (values : List ScalarValue) :
    let scalar := max s.scalars.peak
      (s.scalars.memory.length+values.length-s.scalars.baseMemory+s.scalars.bindings.length+values.length)
    (finish s objects view values).scalars.peak = scalar ∧
    (finish s objects view values).peak = max s.peak (scalar+objects.heap.peak) := by
  dsimp only
  constructor <;> simp only [finish,observe,Proofs.CppState.State.observe,List.length_append,List.length_map,
    Proofs.CppConstructorPeak.scalarBindings_length,Nat.add_zero,Nat.add_assoc]

theorem construct_resources (s out : Context) (source target : ObjectRef) (profile : Profile)
    (run : constructClass s source profile = some (out,target)) :
    let count := profile.scalarFields.length
    let scalar := max s.scalars.peak
      (s.scalars.memory.length+count-s.scalars.baseMemory+s.scalars.bindings.length+count)
    work out = work s+count+2 ∧
    out.objects.heap.liveSpace = s.objects.heap.liveSpace+1 ∧
    out.objects.heap.peak = max s.objects.heap.peak (out.objects.heap.liveSpace-s.objects.heap.baseSpace) ∧
    out.objects.heap.baseSpace = s.objects.heap.baseSpace ∧
    out.scalars.peak = scalar ∧ out.peak = max s.peak (scalar+out.objects.heap.peak) := by
  obtain ⟨view,objects,slot,values,_,moved,captured,rfl,_⟩ := construct_success s out source target profile run
  have counts := capture_length (project s profile.element) source.scalarSlots profile.scalarFields values captured
  have bounds := resources s profile view slot objects values moved
  have peaks := finish_peak s objects slot values
  rw [counts] at bounds peaks
  exact ⟨bounds.1,bounds.2.1,bounds.2.2.1,bounds.2.2.2,peaks.1,peaks.2⟩

end Proofs.CppClassMoveConstruct
