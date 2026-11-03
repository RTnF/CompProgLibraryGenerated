import Proofs.CppClassCopy
import Proofs.CppCopyStatementFacts
import Proofs.CppNestedStmt

-- Memberwise copy through the ordinary nested command interpreter.
namespace Proofs.CppClassCopyCommands
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedStmt
open Proofs.CppClassCopy Proofs.CppConstructorFinish

-- An implicit copy initializes its vector member and then each scalar member
-- in declaration order. The ordinary command interpreter accounts for the
-- source loads separately from the direct copyClass helper.
def scalarCommands : List Nat → List (Ty × Bool) → Option Command
  | [],[] => some (.primitive .skip)
  | slot::slots,field::fields => do
      let rest ← scalarCommands slots fields
      some (.sequence (.primitive (.declare field.1 field.2 (.variable field.1 slot))) rest)
  | _,_ => none

def copyCommand (source : ObjectRef) (profile : Profile) : Option Command := do
  let rest ← scalarCommands source.scalarSlots profile.scalarFields
  some (.sequence (.primitive (.copyVector (.local source.vectorSlot)
    profile.element profile.vectorWritable)) rest)

-- Initial source validation is important for raw ObjectRefs: a nonexistent
-- source slot must not become a readable target slot as declarations append.
-- For well-typed C++ objects these checks are ghost metadata validation.
def runCopyFuel (fuel : Nat) (s : NState) (source : ObjectRef) (profile : Profile) :
    Proofs.CppLoop.Outcome NStep := do
  let _ ← Proofs.CppLoop.liftChecked (CppClassCopy.captureAll s source.scalarSlots profile.scalarFields)
  let command ← Proofs.CppLoop.liftChecked (copyCommand source profile)
  runFuel fuel command s

def scalarStep (s : NState) (ty : Ty) (writable : Bool) (value : Int) : NState :=
  ((s.charge 1 1).declared ty writable value).charge 1 0

theorem scalar_cell_facts (s : NState) (slot : Nat) (ty : Ty)
    (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
    (actual : s.scalarCell slot ty = some (binding,cell)) :
    cell.type = ty ∧ ty.valid cell.value = true := by
  unfold NState.scalarCell at actual
  obtain ⟨index,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ actual
  obtain ⟨b,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  obtain ⟨c,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  by_cases checked : c.type = ty ∧ ty.valid c.value
  · simp only [ite_eq_left checked,Option.some.injEq,Prod.mk.injEq] at rest
    rcases rest with ⟨rfl,rfl⟩
    exact checked
  · simp [checked] at rest

theorem scalar_run (s : NState) (slot : Nat) (ty : Ty) (writable : Bool)
    (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
    (actual : s.scalarCell slot ty = some (binding,cell)) :
    (NStmt.declare ty writable (.variable ty slot)).run s =
      some ⟨scalarStep s ty writable cell.value,none,false⟩ := by
  have evaluated : (NExpr.variable ty slot).eval s = some (s.charge 1 1,cell.value) := by
    simp [NExpr.eval,actual]
  have ran := declare_run (.variable ty slot) ty writable s (s.charge 1 1)
    cell.value cell.value evaluated (Ty.convert_of_valid ty cell.value
      (scalar_cell_facts s slot ty binding cell actual).2)
  simpa only [scalarStep,NState.release,NState.charge,NState.observe,List.take_length] using ran

theorem scalar_step_fields (s : NState) (ty : Ty) (writable : Bool) (value : Int) :
    (scalarStep s ty writable value).frame = s.frame ∧
    (scalarStep s ty writable value).scope = s.scope ∧
    (scalarStep s ty writable value).scalars.memory = s.scalars.memory++[⟨ty,value⟩] ∧
    (scalarStep s ty writable value).scalars.bindings =
      s.scalars.bindings++[⟨s.scalars.memory.length,writable⟩] ∧
    (scalarStep s ty writable value).slots = s.slots++[.scalar s.scalars.bindings.length] :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem scalar_step_work (s : NState) (ty : Ty) (writable : Bool) (value : Int) :
    (scalarStep s ty writable value).work = s.work+2 := by
  simp [scalarStep,NState.declared,NState.charge,NState.observe,NState.work,
    Proofs.CppState.State.observe,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem scalar_step_keeps (s : NState) (newTy : Ty) (writable : Bool) (value : Int)
    (slot : Nat) (ty : Ty) (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
    (actual : s.scalarCell slot ty = some (binding,cell)) :
    (scalarStep s newTy writable value).scalarCell slot ty = some (binding,cell) := by
  unfold NState.scalarCell at actual
  obtain ⟨index,slotFound,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ actual
  obtain ⟨b,found,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  obtain ⟨c,cellFound,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
  have slotBound : slot < s.slots.length := by
    by_cases inside : slot < s.slots.length
    · exact inside
    · have missing := List.getElem?_eq_none_iff.mpr (show s.slots.length ≤ slot by omega)
      simp [NState.scalarSlot,missing] at slotFound
  have bindingBound : index < s.scalars.bindings.length := by
    by_cases inside : index < s.scalars.bindings.length
    · exact inside
    · have missing := List.getElem?_eq_none_iff.mpr (show s.scalars.bindings.length ≤ index by omega)
      simp [missing] at found
  have cellBound : b.address < s.scalars.memory.length := by
    by_cases inside : b.address < s.scalars.memory.length
    · exact inside
    · have missing := List.getElem?_eq_none_iff.mpr (show s.scalars.memory.length ≤ b.address by omega)
      simp [missing] at cellFound
  have slotOut : (scalarStep s newTy writable value).scalarSlot slot = some index := by
    simpa only [scalarStep,NState.charge,NState.observe,NState.declared,NState.scalarSlot,
      List.getElem?_append_left slotBound] using slotFound
  have bindingOut : (scalarStep s newTy writable value).scalars.bindings[index]? = some b := by
    change (s.scalars.bindings++[⟨s.scalars.memory.length,writable⟩])[index]? = some b
    simpa only [List.getElem?_append_left bindingBound] using found
  have cellOut : (scalarStep s newTy writable value).scalars.memory[b.address]? = some c := by
    change (s.scalars.memory++[⟨newTy,value⟩])[b.address]? = some c
    simpa only [List.getElem?_append_left cellBound] using cellFound
  simpa only [NState.scalarCell,slotOut,bindingOut,cellOut,Bind.bind,Option.bind] using rest

theorem scalar_step_peak (s : NState) (ty : Ty) (writable : Bool) (value : Int) :
    (scalarStep s ty writable value).scalars.peak =
      max s.scalars.peak ((s.scalars.memory.length+1)-s.scalars.baseMemory+
        (s.scalars.bindings.length+1)) ∧
    (scalarStep s ty writable value).peak =
      max s.peak ((scalarStep s ty writable value).scalars.peak+s.frame.state.storage.peak) := by
  simp [scalarStep,NState.declared,NState.charge,NState.observe,Proofs.CppState.State.observe,
    Nat.add_assoc]
  omega

theorem capture_step_kept (s : NState) (newTy : Ty) (writable : Bool) (value : Int)
    (slot : Nat) (field : Ty × Bool) (v : ScalarValue)
    (actual : CppClassCopy.capture s slot field = some v) :
    CppClassCopy.capture (scalarStep s newTy writable value) slot field = some v := by
  unfold CppClassCopy.capture at actual
  obtain ⟨pair,read,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ actual
  rcases pair with ⟨b,c⟩
  have kept := scalar_step_keeps s newTy writable value slot field.1 b c read
  simpa only [CppClassCopy.capture,kept,Bind.bind,Option.bind] using rest

def SourceValues (s : NState) : List Nat → List (Ty × Bool) → List ScalarValue → Prop
  | [],[],[] => True
  | slot::slots,field::fields,v::values =>
      CppClassCopy.capture s slot field = some v ∧ SourceValues s slots fields values
  | _,_,_ => False

theorem source_values_kept (s : NState) (newTy : Ty) (writable : Bool) (value : Int)
    (slots : List Nat) (fields : List (Ty × Bool)) (values : List ScalarValue)
    (actual : SourceValues s slots fields values) :
    SourceValues (scalarStep s newTy writable value) slots fields values := by
  induction slots generalizing fields values with
  | nil => cases fields <;> cases values <;> simp_all [SourceValues]
  | cons slot slots ih =>
    cases fields with
    | nil => simp [SourceValues] at actual
    | cons field fields =>
      cases values with
      | nil => simp [SourceValues] at actual
      | cons v values =>
        exact ⟨capture_step_kept s newTy writable value slot field v actual.1,
          ih fields values actual.2⟩

def scalarResult : NState → List ScalarValue → NState
  | s,[] => s
  | s,v::values => scalarResult (scalarStep s v.1.type v.2 v.1.value) values

theorem capture_all_cons (s : NState) (slot : Nat) (slots : List Nat)
    (field : Ty × Bool) (fields : List (Ty × Bool)) :
    CppClassCopy.captureAll s (slot::slots) (field::fields) = (do
      let v ← CppClassCopy.capture s slot field
      let vs ← CppClassCopy.captureAll s slots fields
      some (v::vs)) := by
  by_cases matching : slots.length = fields.length
  · simp [CppClassCopy.captureAll,matching,List.mapM_cons]
  · simp [CppClassCopy.captureAll,matching]

theorem source_values_of_capture (s : NState) (slots : List Nat) (fields : List (Ty × Bool))
    (values : List ScalarValue) (actual : CppClassCopy.captureAll s slots fields = some values) :
    SourceValues s slots fields values := by
  induction slots generalizing fields values with
  | nil => cases fields <;> cases values <;> simp_all [CppClassCopy.captureAll,SourceValues]
  | cons slot slots ih =>
    cases fields with
    | nil => simp [CppClassCopy.captureAll] at actual
    | cons field fields =>
      rw [capture_all_cons] at actual
      obtain ⟨v,first,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ actual
      obtain ⟨vs,tail,done⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
      have same : v::vs = values := Option.some.inj done
      subst values
      exact ⟨first,ih fields vs tail⟩

theorem capture_scalar_run (s : NState) (slot : Nat) (field : Ty × Bool) (v : ScalarValue)
    (actual : CppClassCopy.capture s slot field = some v) :
    (NStmt.declare field.1 field.2 (.variable field.1 slot)).run s =
      some ⟨scalarStep s v.1.type v.2 v.1.value,none,false⟩ := by
  unfold CppClassCopy.capture at actual
  obtain ⟨pair,read,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ actual
  rcases pair with ⟨b,c⟩
  have same : (c,field.2) = v := Option.some.inj rest
  subst v
  have typed := (scalar_cell_facts s slot field.1 b c read).1
  simpa only [typed] using scalar_run s slot field.1 field.2 b c read

open Proofs.CppLoop

theorem primitive_run (fuel : Nat) (stmt : NStmt) (s out : NState)
    (actual : stmt.run s = some ⟨out,none,false⟩) :
    runFuel (fuel+1) (.primitive stmt) s = .finished ⟨out,none,false⟩ := by
  simp [Proofs.CppNestedProgram.runFuel,actual,liftChecked]

theorem sequence_run (fuel : Nat) (first rest : Command) (s mid out : NState)
    (one : runFuel fuel first s = .finished ⟨mid,none,false⟩)
    (two : runFuel fuel rest mid = .finished ⟨out,none,false⟩) :
    runFuel (fuel+1) (.sequence first rest) s = .finished ⟨out,none,false⟩ := by
  simp [Proofs.CppNestedProgram.runFuel,one,two,Bind.bind,Outcome.bind]

theorem scalar_commands_run (s : NState) (slots : List Nat) (fields : List (Ty × Bool))
    (values : List ScalarValue) (actual : SourceValues s slots fields values) :
    ∃ command, scalarCommands slots fields = some command ∧
      runFuel (values.length+1) command s = .finished ⟨scalarResult s values,none,false⟩ := by
  induction slots generalizing s fields values with
  | nil =>
    cases fields with
    | cons => simp [SourceValues] at actual
    | nil =>
      cases values with
      | cons => simp [SourceValues] at actual
      | nil => exact ⟨.primitive .skip,rfl,rfl⟩
  | cons slot slots ih =>
    cases fields with
    | nil => simp [SourceValues] at actual
    | cons field fields =>
      cases values with
      | nil => simp [SourceValues] at actual
      | cons v values =>
        let next := scalarStep s v.1.type v.2 v.1.value
        have preserved := source_values_kept s v.1.type v.2 v.1.value slots fields values actual.2
        obtain ⟨rest,built,ran⟩ := ih next fields values preserved
        refine ⟨.sequence (.primitive (.declare field.1 field.2 (.variable field.1 slot))) rest,?_,?_⟩
        · simp [scalarCommands,built]
        · exact sequence_run (values.length+1) _ rest s next (scalarResult next values)
            (primitive_run values.length _ s next (capture_scalar_run s slot field v actual.1)) ran

theorem scalar_result_work (s : NState) (values : List ScalarValue) :
    (scalarResult s values).work = s.work+2*values.length := by
  induction values generalizing s with
  | nil => simp [scalarResult]
  | cons v values ih =>
    change (scalarResult (scalarStep s v.1.type v.2 v.1.value) values).work = _
    rw [ih,scalar_step_work]
    simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
    omega

theorem scalar_result_frame (s : NState) (values : List ScalarValue) :
    (scalarResult s values).frame = s.frame := by
  induction values generalizing s with
  | nil => rfl
  | cons v values ih => exact (ih _).trans rfl

theorem scalar_result_memory (s : NState) (values : List ScalarValue) :
    (scalarResult s values).scalars.memory = s.scalars.memory++values.map Prod.fst := by
  induction values generalizing s with
  | nil => simp [scalarResult]
  | cons v values ih =>
    change (scalarResult (scalarStep s v.1.type v.2 v.1.value) values).scalars.memory = _
    rw [ih]
    simp [scalarStep,NState.charge,NState.observe,NState.declared,
      Proofs.CppState.State.observe,List.append_assoc]

theorem scalar_result_keeps (s : NState) (values : List ScalarValue) (slot : Nat) (ty : Ty)
    (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
    (actual : s.scalarCell slot ty = some (binding,cell)) :
    (scalarResult s values).scalarCell slot ty = some (binding,cell) := by
  induction values generalizing s with
  | nil => exact actual
  | cons v values ih =>
    exact ih _ (scalar_step_keeps s v.1.type v.2 v.1.value slot ty binding cell actual)

theorem scalar_result_bindings (s : NState) (values : List ScalarValue) :
    (scalarResult s values).scalars.bindings =
      s.scalars.bindings++scalarBindings s.scalars.memory.length values := by
  induction values generalizing s with
  | nil => simp [scalarResult,scalarBindings]
  | cons v values ih =>
    change (scalarResult (scalarStep s v.1.type v.2 v.1.value) values).scalars.bindings = _
    rw [ih]
    simp [scalarStep,NState.charge,NState.observe,NState.declared,
      Proofs.CppState.State.observe,scalarBindings,List.append_assoc]

theorem scalar_locations_cons (start count : Nat) :
    scalarLocations start (count+1) = .scalar start :: scalarLocations (start+1) count := by
  simp [scalarLocations,List.range_succ_eq_map,List.map_map,Function.comp_def,
    Nat.add_left_comm,Nat.add_comm]

theorem scalar_result_slots (s : NState) (values : List ScalarValue) :
    (scalarResult s values).slots = s.slots++scalarLocations s.scalars.bindings.length values.length := by
  induction values generalizing s with
  | nil => simp [scalarResult,scalarLocations]
  | cons v values ih =>
    change (scalarResult (scalarStep s v.1.type v.2 v.1.value) values).slots = _
    rw [ih]
    simp [scalarStep,NState.charge,NState.observe,NState.declared,
      Proofs.CppState.State.observe,scalar_locations_cons,List.append_assoc]

theorem capture_transport (s t : NState)
    (kept : ∀ slot ty binding cell, s.scalarCell slot ty = some (binding,cell) →
      t.scalarCell slot ty = some (binding,cell))
    (slot : Nat) (field : Ty × Bool) (v : ScalarValue)
    (actual : CppClassCopy.capture s slot field = some v) :
    CppClassCopy.capture t slot field = some v := by
  unfold CppClassCopy.capture at actual
  obtain ⟨pair,read,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ actual
  rcases pair with ⟨b,c⟩
  simpa only [CppClassCopy.capture,kept slot field.1 b c read,Bind.bind,Option.bind] using rest

theorem source_values_transport (s t : NState)
    (kept : ∀ slot ty binding cell, s.scalarCell slot ty = some (binding,cell) →
      t.scalarCell slot ty = some (binding,cell))
    (slots : List Nat) (fields : List (Ty × Bool)) (values : List ScalarValue)
    (actual : SourceValues s slots fields values) : SourceValues t slots fields values := by
  induction slots generalizing fields values with
  | nil => cases fields <;> cases values <;> simp_all [SourceValues]
  | cons slot slots ih =>
    cases fields with
    | nil => simp [SourceValues] at actual
    | cons field fields =>
      cases values with
      | nil => simp [SourceValues] at actual
      | cons v values => exact ⟨capture_transport s t kept slot field v actual.1,
          ih fields values actual.2⟩

def vectorResult (s : NState) (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value)
    (profile : Profile) : NState :=
  Proofs.CppCopyStatementFacts.result s (s.charge 1 1) buffer profile.element profile.vectorWritable

theorem vector_keeps_scalar (s : NState)
    (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value) (profile : Profile)
    (slot : Nat) (ty : Ty) (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
    (actual : s.scalarCell slot ty = some (binding,cell)) :
    (vectorResult s buffer profile).scalarCell slot ty = some (binding,cell) :=
  Proofs.CppCopyStatementFacts.keeps_scalar s (s.charge 1 1) buffer profile.element
    profile.vectorWritable slot ty binding cell actual

theorem copy_commands_complete (s : NState) (source : ObjectRef) (profile : Profile)
    (index : Nat) (binding : Proofs.CppNestedVectorBindings.Binding)
    (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value) (values : List ScalarValue)
    (slot : s.vectorSlot source.vectorSlot = some index)
    (resolved : s.frame.resolve index (.integer profile.element) = some (binding,buffer))
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (supported : Proofs.CppVectorBindings.supported profile.element)
    (captured : CppClassCopy.captureAll s source.scalarSlots profile.scalarFields = some values) :
    ∃ command, copyCommand source profile = some command ∧
      runCopyFuel (values.length+2) s source profile =
        .finished ⟨scalarResult (vectorResult s buffer profile) values,none,false⟩ := by
  have evaluated : (Container.local source.vectorSlot).eval s = some (s.charge 1 1,index) := by
    simp [Container.eval,slot]
  have copied := (Proofs.CppCopyStatementFacts.completes s (s.charge 1 1)
    (.local source.vectorSlot) index binding buffer profile.element profile.vectorWritable
    evaluated resolved lengths supported).1
  have oldFields := source_values_of_capture s source.scalarSlots profile.scalarFields values captured
  have after := source_values_transport s (vectorResult s buffer profile)
    (vector_keeps_scalar s buffer profile) source.scalarSlots profile.scalarFields values oldFields
  obtain ⟨rest,built,ran⟩ := scalar_commands_run (vectorResult s buffer profile)
    source.scalarSlots profile.scalarFields values after
  let command := Command.sequence (.primitive (.copyVector (.local source.vectorSlot)
    profile.element profile.vectorWritable)) rest
  have assembled : copyCommand source profile = some command := by simp [copyCommand,built,command]
  refine ⟨command,assembled,?_⟩
  have one := primitive_run values.length
    (.copyVector (.local source.vectorSlot) profile.element profile.vectorWritable)
    s (vectorResult s buffer profile) copied
  have completed := sequence_run (values.length+1) _ rest s (vectorResult s buffer profile)
    (scalarResult (vectorResult s buffer profile) values) one ran
  simpa only [runCopyFuel,captured,assembled,liftChecked,Bind.bind,Outcome.bind] using completed

theorem vector_result_work (s : NState)
    (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value) (profile : Profile)
    (valid : s.frame.state.wellFormed = true) :
    (vectorResult s buffer profile).work = s.work+buffer.items.length+3 := by
  have charged : (s.charge 1 1).work = s.work+1 := by
    simp [NState.work,NState.charge,NState.observe,Proofs.CppState.State.observe,
      Nat.add_assoc,Nat.add_comm]
  have cost := (Proofs.CppCopyStatementFacts.result_cost s (s.charge 1 1) buffer
    profile.element profile.vectorWritable valid).1
  rw [charged] at cost
  change (Proofs.CppCopyStatementFacts.result s (s.charge 1 1) buffer
    profile.element profile.vectorWritable).work = _
  omega

theorem copy_result_work (s : NState)
    (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value) (profile : Profile)
    (values : List ScalarValue) (valid : s.frame.state.wellFormed = true) :
    (scalarResult (vectorResult s buffer profile) values).work =
      s.work+buffer.items.length+3+2*values.length := by
  rw [scalar_result_work,vector_result_work s buffer profile valid]

theorem copy_result_keeps_scalar (s : NState)
    (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value) (profile : Profile)
    (values : List ScalarValue) (slot : Nat) (ty : Ty) (binding : Proofs.CppState.Binding)
    (cell : Proofs.CppState.Cell) (actual : s.scalarCell slot ty = some (binding,cell)) :
    (scalarResult (vectorResult s buffer profile) values).scalarCell slot ty = some (binding,cell) :=
  scalar_result_keeps (vectorResult s buffer profile) values slot ty binding cell
    (vector_keeps_scalar s buffer profile slot ty binding cell actual)

theorem copy_result_keeps_read (s : NState) (source : ObjectRef) (profile : Profile)
    (index : Nat) (binding : Proofs.CppNestedVectorBindings.Binding)
    (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value) (values : List ScalarValue)
    (slot : s.vectorSlot source.vectorSlot = some index)
    (resolved : s.frame.resolve index (.integer profile.element) = some (binding,buffer))
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (supported : Proofs.CppVectorBindings.supported profile.element)
    (reference : Proofs.CppNestedVectorBindings.Reference) (value : Int)
    (actual : s.frame.read reference = some value) :
    (scalarResult (vectorResult s buffer profile) values).frame.read reference = some value := by
  rw [scalar_result_frame]
  have evaluated : (Container.local source.vectorSlot).eval s = some (s.charge 1 1,index) := by
    simp [Container.eval,slot]
  have released : ((s.charge 1 1).release s).frame.read reference = some value := by
    simpa only [NState.release,NState.charge,NState.observe,List.take_length] using actual
  exact Proofs.CppCopyStatementFacts.keeps_read s (s.charge 1 1) (.local source.vectorSlot)
    index binding buffer profile.element profile.vectorWritable evaluated resolved lengths supported
    reference value released

open Proofs.CppNestedEval

theorem scalar_step_bounds (s : NState) (ty : Ty) (writable : Bool) (value : Int) :
    liveS (scalarStep s ty writable value) ≤ liveS s+2 ∧
    (scalarStep s ty writable value).scalars.peak ≤ max s.scalars.peak (liveS s+2) ∧
    (scalarStep s ty writable value).peak ≤
      max s.peak (max s.scalars.peak (liveS s+2)+s.frame.state.storage.peak) := by
  simp [liveS,scalarStep,NState.declared,NState.charge,NState.observe,
    Proofs.CppState.State.observe,Nat.add_assoc]
  omega

theorem scalar_result_bounds (s : NState) (values : List ScalarValue) :
    (scalarResult s values).scalars.peak ≤ max s.scalars.peak (liveS s+2*values.length) ∧
    (scalarResult s values).peak ≤
      max s.peak (max s.scalars.peak (liveS s+2*values.length)+s.frame.state.storage.peak) := by
  induction values generalizing s with
  | nil => simp [scalarResult]; omega
  | cons v values ih =>
    have step := scalar_step_bounds s v.1.type v.2 v.1.value
    have later := ih (scalarStep s v.1.type v.2 v.1.value)
    have frame : (scalarStep s v.1.type v.2 v.1.value).frame.state.storage.peak =
        s.frame.state.storage.peak := rfl
    rw [frame] at later
    change (scalarResult (scalarStep s v.1.type v.2 v.1.value) values).scalars.peak ≤ _ ∧
      (scalarResult (scalarStep s v.1.type v.2 v.1.value) values).peak ≤ _
    simp only [List.length_cons]
    constructor <;> omega

def copiedStoragePeak (s : NState)
    (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value) : Nat :=
  max s.frame.state.storage.peak
    (s.frame.state.liveSpace+buffer.items.length+2-s.frame.state.storage.baseSpace)

theorem vector_result_peaks (s : NState)
    (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value) (profile : Profile)
    (valid : s.frame.state.wellFormed = true) :
    (vectorResult s buffer profile).scalars.peak = max s.scalars.peak (liveS s+1) ∧
    (vectorResult s buffer profile).frame.state.storage.peak = copiedStoragePeak s buffer ∧
    (vectorResult s buffer profile).peak =
      max s.peak (max s.scalars.peak (liveS s+1)+copiedStoragePeak s buffer) ∧
    liveS (vectorResult s buffer profile) = liveS s := by
  have storage := (Proofs.CppCopyStatementFacts.result_cost s (s.charge 1 1) buffer
    profile.element profile.vectorWritable valid).2.2
  change (vectorResult s buffer profile).frame.state.storage.peak = copiedStoragePeak s buffer at storage
  have scalar : (vectorResult s buffer profile).scalars.peak = max s.scalars.peak (liveS s+1) := by
    simp [vectorResult,Proofs.CppCopyStatementFacts.result,NState.charge,NState.observe,
      NState.release,Proofs.CppState.State.observe,liveS]
  have live : liveS (vectorResult s buffer profile) = liveS s := rfl
  refine ⟨scalar,storage,?_,live⟩
  have larger : s.frame.state.storage.peak ≤ copiedStoragePeak s buffer := Nat.le_max_left _ _
  change max (max s.peak ((s.charge 1 1).scalars.peak+s.frame.state.storage.peak))
    ((vectorResult s buffer profile).scalars.peak+
      (vectorResult s buffer profile).frame.state.storage.peak) = _
  rw [scalar,storage]
  have initial : (s.charge 1 1).scalars.peak = max s.scalars.peak (liveS s+1) := rfl
  rw [initial]
  omega

theorem copy_result_peaks (s : NState)
    (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value) (profile : Profile)
    (values : List ScalarValue) (valid : s.frame.state.wellFormed = true) :
    (scalarResult (vectorResult s buffer profile) values).scalars.peak ≤
      max s.scalars.peak (liveS s+1+2*values.length) ∧
    (scalarResult (vectorResult s buffer profile) values).frame.state.storage.peak =
      copiedStoragePeak s buffer ∧
    (scalarResult (vectorResult s buffer profile) values).peak ≤
      max s.peak (max s.scalars.peak (liveS s+1+2*values.length)+copiedStoragePeak s buffer) := by
  obtain ⟨scalar,storage,outer,live⟩ := vector_result_peaks s buffer profile valid
  have bounds := scalar_result_bounds (vectorResult s buffer profile) values
  rw [scalar,storage,outer,live] at bounds
  refine ⟨?_,?_,?_⟩
  · omega
  · rw [scalar_result_frame,storage]
  · omega

theorem scalar_result_stable (s : NState) (values : List ScalarValue) :
    (scalarResult s values).scope = s.scope ∧
    (scalarResult s values).scalars.baseMemory = s.scalars.baseMemory := by
  induction values generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons v values ih =>
    obtain ⟨scope,base⟩ := ih (scalarStep s v.1.type v.2 v.1.value)
    exact ⟨scope.trans rfl,base.trans rfl⟩

-- Core equality is paired with the separate work and three-peak theorems;
-- it is not equality of the resource-accounted whole states.
theorem copy_result_core (s : NState)
    (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value) (profile : Profile)
    (values : List ScalarValue) :
    Core (CppClassCopy.finish s
      (Proofs.CppFrameCopy.copiedFrame s.frame buffer profile.element s.scope profile.vectorWritable)
      s.frame.bindings.length values)
      (scalarResult (vectorResult s buffer profile) values) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [scalar_result_frame]
    simp [CppClassCopy.finish,vectorResult,Proofs.CppCopyStatementFacts.result,
      NState.charge,NState.observe,NState.release,List.take_length]
  · rw [scalar_result_slots]
    simp [CppClassCopy.finish,vectorResult,Proofs.CppCopyStatementFacts.result,
      NState.charge,NState.observe,NState.release,Proofs.CppState.State.observe,List.append_assoc]
  · exact (scalar_result_stable _ values).1
  · rw [scalar_result_memory]
    simp [CppClassCopy.finish,vectorResult,Proofs.CppCopyStatementFacts.result,
      NState.charge,NState.observe,NState.release,Proofs.CppState.State.observe]
  · rw [scalar_result_bindings]
    simp [CppClassCopy.finish,vectorResult,Proofs.CppCopyStatementFacts.result,
      NState.charge,NState.observe,NState.release,Proofs.CppState.State.observe]
  · exact (scalar_result_stable _ values).2

end Proofs.CppClassCopyCommands
