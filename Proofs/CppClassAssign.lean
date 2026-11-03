import Proofs.CppFrameCopyAssign
import Proofs.CppClassCopyCommands
import Proofs.ExtremaCall

namespace Proofs.CppClassAssign
open Proofs.CppScalar Proofs.CppVector Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppFrameCopyAssign

theorem primitive_data {β : Type} (target source : Buffer Value)
    (targetGen sourceGen : Nat → Nat) (accept : Value → Bool) (writable : Bool)
    (next : Buffer Value → Nat → Nat → Option β) :
    (do
      let result ← Proofs.CppVectorCopyAssign.copyAssign ⟨target,targetGen⟩ ⟨source,sourceGen⟩ accept writable
      next result.target.buffer result.work result.peak) =
    (do
      let result ← Proofs.CppVectorCopyAssign.copyAssign ⟨target,fun _ => 0⟩ ⟨source,fun _ => 0⟩ accept writable
      next result.target.buffer result.work result.peak) := by
  unfold Proofs.CppVectorCopyAssign.copyAssign
  dsimp only
  split
  · split
    · rfl
    · unfold Proofs.CppVectorCopyAssign.assigned
      split <;> rfl
  · rfl

-- Candidate next step: define the data evaluator by projection at zero ghost
-- metadata, then prove every tracked execution has the same data result.
-- Metadata must still be threaded extrinsically in lifetime theorems; saved
-- external refs must use TrackedReference, never legacy Frame.read directly.
def dataAssign (f : Frame) (target source : Nat) (ty : Ty) : Option Frame :=
  (copyAssign ⟨f,fun _ _ => 0⟩ target source ty).map (·.frame)


theorem frame_data (s : TrackedFrame) (target source : Nat) (ty : Ty) :
    (copyAssign s target source ty).map (·.frame) = dataAssign s.frame target source ty := by
  unfold dataAssign copyAssign
  cases targetResolved : s.frame.resolve target (.integer ty) with
  | none => simp
  | some pair =>
    obtain ⟨tb,targetBuffer⟩ := pair
    cases sourceResolved : s.frame.resolve source (.integer ty) with
    | none => simp
    | some pair =>
      obtain ⟨sb,sourceBuffer⟩ := pair
      simp only [bind,Option.map_bind,Function.comp_def,Option.map_some,Option.bind_some,Option.bind_fun_some]
      exact primitive_data targetBuffer sourceBuffer (s.generation tb.owner) (s.generation sb.owner)
        (accepts (.integer ty)) tb.writable (fun buffer work peak =>
          s.frame.commit tb.owner (.integer ty) ⟨buffer,(),work,peak⟩)


open Proofs.CppNestedProgram Proofs.CppConstructorFinish Proofs.CppClassCopy
open Proofs.DynamicResultValid

def scalarStep (s : NState) (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell) (value : Int) : NState :=
  let released := (s.charge 1 1).release s
  ({released with scalars := {released.scalars with memory := released.scalars.memory.set binding.address ⟨cell.type,value⟩}} : NState).charge 1 0

def assignScalar (s : NState) (target source : Nat) (ty : Ty) : Option NState := do
  let (_,value) ← s.scalarCell source ty
  let (binding,cell) ← s.scalarCell target ty
  if binding.writable then some (scalarStep s binding cell value.value) else none

theorem scalar_command (s : NState) (target source : Nat) (ty : Ty)
    (tb sb : Proofs.CppState.Binding) (tc sc : Proofs.CppState.Cell)
    (targetCell : s.scalarCell target ty = some (tb,tc)) (sourceCell : s.scalarCell source ty = some (sb,sc))
    (permission : tb.writable = true) :
    (NStmt.assign target ty (.variable ty source)).run s = some ⟨scalarStep s tb tc sc.value,none,false⟩ := by
  have evaluated : (NExpr.variable ty source).eval s = some (s.charge 1 1,sc.value) := by
    simp [NExpr.eval,sourceCell]
  have releasedCell : ((s.charge 1 1).release s).scalarCell target ty = some (tb,tc) := by
    simpa only [NState.release,NState.charge,NState.observe,NState.scalarCell,NState.scalarSlot,Proofs.CppState.State.observe] using targetCell
  have converted := Ty.convert_of_valid ty sc.value
    (Proofs.CppClassCopyCommands.scalar_cell_facts s source ty sb sc sourceCell).2
  simp only [NStmt.run,evaluated,bind,Option.bind,releasedCell,permission,↓reduceIte,converted,scalarStep]

theorem scalar_runs (s : NState) (target source : Nat) (ty : Ty)
    (tb sb : Proofs.CppState.Binding) (tc sc : Proofs.CppState.Cell)
    (targetCell : s.scalarCell target ty = some (tb,tc)) (sourceCell : s.scalarCell source ty = some (sb,sc))
    (permission : tb.writable = true) :
    assignScalar s target source ty = some (scalarStep s tb tc sc.value) := by
  simp [assignScalar,targetCell,sourceCell,permission]

theorem scalar_fields (s : NState) (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell) (value : Int) :
    (scalarStep s binding cell value).frame = s.frame ∧ (scalarStep s binding cell value).slots = s.slots ∧
      (scalarStep s binding cell value).scope = s.scope ∧
      (scalarStep s binding cell value).scalars.bindings = s.scalars.bindings ∧
      (scalarStep s binding cell value).scalars.memory = s.scalars.memory.set binding.address ⟨cell.type,value⟩ ∧
      (scalarStep s binding cell value).work = s.work+2 := by
  simp [scalarStep,NState.release,NState.charge,NState.observe,NState.work,Proofs.CppState.State.observe,List.take_length,
    Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

theorem scalar_success (s out : NState) (target source : Nat) (ty : Ty)
    (ran : assignScalar s target source ty = some out) :
    ∃ tb sb tc sc, s.scalarCell target ty = some (tb,tc) ∧ s.scalarCell source ty = some (sb,sc) ∧
      tb.writable = true ∧ out = scalarStep s tb tc sc.value ∧
      (NStmt.assign target ty (.variable ty source)).run s = some ⟨out,none,false⟩ := by
  unfold assignScalar at ran
  obtain ⟨⟨sb,sc⟩,sourceCell,rest⟩ := bind_some _ _ _ ran
  obtain ⟨⟨tb,tc⟩,targetCell,rest⟩ := bind_some _ _ _ rest
  dsimp only at rest
  split at rest
  · rename_i permission
    have same := Option.some.inj rest
    refine ⟨tb,sb,tc,sc,targetCell,sourceCell,permission,same.symm,?_⟩
    rw [← same]
    exact scalar_command s target source ty tb sb tc sc targetCell sourceCell permission
  · simp at rest

def assignFields : NState → List Nat → List Nat → List (Ty × Bool) → Option NState
  | s,[],[],[] => some s
  | s,target::targets,source::sources,(ty,writable)::fields => do
    if writable then
      let next ← assignScalar s target source ty
      assignFields next targets sources fields
    else none
  | _,_,_,_ => none

theorem fields_metadata (s out : NState) (targets sources : List Nat) (fields : List (Ty × Bool))
    (ran : assignFields s targets sources fields = some out) :
    out.frame = s.frame ∧ out.slots = s.slots ∧ out.scope = s.scope ∧
      out.scalars.bindings = s.scalars.bindings ∧ out.scalars.memory.length = s.scalars.memory.length ∧
      out.work = s.work+2*fields.length := by
  induction targets generalizing s sources fields with
  | nil => cases sources <;> cases fields <;> simp_all [assignFields]
  | cons target targets ih =>
    cases sources with
    | nil => simp [assignFields] at ran
    | cons source sources =>
      cases fields with
      | nil => simp [assignFields] at ran
      | cons field fields =>
        obtain ⟨ty,writable⟩ := field
        unfold assignFields at ran
        split at ran
        · obtain ⟨next,head,tail⟩ := bind_some _ _ _ ran
          obtain ⟨tb,sb,tc,sc,_,_,_,nextEq,_⟩ := scalar_success s next target source ty head
          have one := scalar_fields s tb tc sc.value
          rw [← nextEq] at one
          have rest := ih next sources fields tail
          have mem : next.scalars.memory.length = s.scalars.memory.length := by rw [nextEq,(scalar_fields s tb tc sc.value).2.2.2.2.1]; exact List.length_set
          refine ⟨rest.1.trans one.1,rest.2.1.trans one.2.1,rest.2.2.1.trans one.2.2.1,
            rest.2.2.2.1.trans one.2.2.2.1,rest.2.2.2.2.1.trans mem,?_⟩
          simp only [List.length_cons,Nat.mul_add,Nat.mul_one]
          omega
        · simp at ran


def vectorState (s : NState) (frame : Frame) : NState := ({s with frame := frame} : NState).charge 1 0

def assignClass (s : NState) (target source : ObjectRef) (profile : Profile) : Option (NState × ObjectRef) := do
  if profile.vectorWritable then
    let targetSlot ← s.vectorSlot target.vectorSlot
    let sourceSlot ← s.vectorSlot source.vectorSlot
    let frame ← dataAssign s.frame targetSlot sourceSlot profile.element
    let out ← assignFields (vectorState s frame) target.scalarSlots source.scalarSlots profile.scalarFields
    some (out,target)
  else none

abbrev Generations := Nat → Nat → Nat

-- The ghost result is carried outside NState. Returning the destination object
-- models operator= returning its lvalue reference; no copied object is created.
def trackedAssignClass (s : NState) (generation : Generations) (target source : ObjectRef) (profile : Profile) :
    Option ((NState × ObjectRef) × Generations) := do
  if profile.vectorWritable then
    let targetSlot ← s.vectorSlot target.vectorSlot
    let sourceSlot ← s.vectorSlot source.vectorSlot
    let tracked ← Proofs.CppFrameCopyAssign.copyAssign ⟨s.frame,generation⟩ targetSlot sourceSlot profile.element
    let out ← assignFields (vectorState s tracked.frame) target.scalarSlots source.scalarSlots profile.scalarFields
    some ((out,target),tracked.generation)
  else none

theorem frame_bind {β : Type} (s : TrackedFrame) (target source : Nat) (ty : Ty) (next : Frame → Option β) :
    ((Proofs.CppFrameCopyAssign.copyAssign s target source ty).bind (fun tracked => next tracked.frame)) =
      (dataAssign s.frame target source ty).bind next := by
  rw [← frame_data s target source ty]
  simp only [Option.bind_map,Function.comp_def]

theorem tracked_class_data (s : NState) (generation : Generations) (target source : ObjectRef) (profile : Profile) :
    (trackedAssignClass s generation target source profile).map Prod.fst = assignClass s target source profile := by
  unfold trackedAssignClass assignClass
  split
  · cases targetSlot : s.vectorSlot target.vectorSlot with
    | none => simp
    | some a =>
      cases sourceSlot : s.vectorSlot source.vectorSlot with
      | none => simp
      | some b =>
        simp only [bind,Option.map_bind,Function.comp_def,Option.map_some,Option.bind_some]
        exact frame_bind ⟨s.frame,generation⟩ a b profile.element (fun frame => do
          let out ← assignFields (vectorState s frame) target.scalarSlots source.scalarSlots profile.scalarFields
          some (out,target))
  · rfl

theorem class_runs (s : NState) (target source : ObjectRef) (profile : Profile) (a b : Nat)
    (frame : Frame) (out : NState) (permission : profile.vectorWritable = true)
    (targetSlot : s.vectorSlot target.vectorSlot = some a) (sourceSlot : s.vectorSlot source.vectorSlot = some b)
    (vectorRun : dataAssign s.frame a b profile.element = some frame)
    (fieldsRun : assignFields (vectorState s frame) target.scalarSlots source.scalarSlots profile.scalarFields = some out) :
    assignClass s target source profile = some (out,target) := by
  simp [assignClass,permission,targetSlot,sourceSlot,vectorRun,fieldsRun]

theorem class_success (s out : NState) (target source result : ObjectRef) (profile : Profile)
    (ran : assignClass s target source profile = some (out,result)) :
    result = target ∧ ∃ a b frame,
      s.vectorSlot target.vectorSlot = some a ∧ s.vectorSlot source.vectorSlot = some b ∧
      dataAssign s.frame a b profile.element = some frame ∧
      assignFields (vectorState s frame) target.scalarSlots source.scalarSlots profile.scalarFields = some out ∧
      out.frame = frame ∧ out.slots = s.slots ∧ out.scope = s.scope ∧
      out.scalars.bindings = s.scalars.bindings ∧ out.scalars.memory.length = s.scalars.memory.length ∧
      out.work = s.scalars.work+frame.state.storage.work+2*profile.scalarFields.length+1 := by
  unfold assignClass at ran
  split at ran
  · obtain ⟨a,targetSlot,rest⟩ := bind_some _ _ _ ran
    obtain ⟨b,sourceSlot,rest⟩ := bind_some _ _ _ rest
    obtain ⟨frame,vectorRun,rest⟩ := bind_some _ _ _ rest
    obtain ⟨actual,fieldsRun,rest⟩ := bind_some _ _ _ rest
    have same := Prod.mk.inj (Option.some.inj rest)
    have eqState := same.1
    have eqRef := same.2
    subst actual
    subst result
    have properties := fields_metadata (vectorState s frame) out target.scalarSlots source.scalarSlots profile.scalarFields fieldsRun
    refine ⟨rfl,a,b,frame,targetSlot,sourceSlot,vectorRun,fieldsRun,properties.1,properties.2.1,properties.2.2.1,
      properties.2.2.2.1,properties.2.2.2.2.1,?_⟩
    have work := properties.2.2.2.2.2
    change out.work = s.scalars.work+1+frame.state.storage.work+2*profile.scalarFields.length at work
    omega
  · simp at ran


theorem scalar_readable (s : NState) (target : Nat) (ty : Ty) (tb : Proofs.CppState.Binding)
    (tc : Proofs.CppState.Cell) (value : Int) (targetCell : s.scalarCell target ty = some (tb,tc))
    (accepted : ty.valid value = true) (slot : Nat) (otherTy : Ty) (binding : Proofs.CppState.Binding)
    (cell : Proofs.CppState.Cell) (found : s.scalarCell slot otherTy = some (binding,cell)) :
    ∃ nextCell, (scalarStep s tb tc value).scalarCell slot otherTy = some (binding,nextCell) := by
  obtain ⟨targetIndex,targetSlot,targetBinding,targetMemory,targetTyped,_⟩ := Proofs.ExtremaCall.scalarCell_facts targetCell
  obtain ⟨index,oldSlot,oldBinding,oldMemory,typed,valid⟩ := Proofs.ExtremaCall.scalarCell_facts found
  have metadata := scalar_fields s tb tc value
  by_cases same : binding.address = tb.address
  · have cells : tc = cell := Option.some.inj (targetMemory.symm.trans (by simpa only [same] using oldMemory))
    have equalTy : ty = otherTy := targetTyped.symm.trans (cells ▸ typed)
    refine ⟨⟨tc.type,value⟩,?_⟩
    unfold NState.scalarCell NState.scalarSlot
    rw [metadata.2.1,metadata.2.2.2.1,metadata.2.2.2.2.1]
    simp only [oldSlot,oldBinding,bind,Option.bind]
    have inside := (List.getElem?_eq_some_iff.mp targetMemory).1
    simp [same,List.getElem?_set_self inside,cells,typed,equalTy] at accepted ⊢
    exact accepted
  · refine ⟨cell,?_⟩
    unfold NState.scalarCell NState.scalarSlot
    rw [metadata.2.1,metadata.2.2.2.1,metadata.2.2.2.2.1]
    simp [oldSlot,oldBinding,List.getElem?_set_ne (Ne.symm same),oldMemory,typed,valid]

def Ready : NState → List Nat → List Nat → List (Ty × Bool) → Prop
  | _,[],[],[] => True
  | s,target::targets,source::sources,(ty,writable)::fields =>
      writable = true ∧ (∃ tb tc, s.scalarCell target ty = some (tb,tc) ∧ tb.writable = true) ∧
      (∃ sb sc, s.scalarCell source ty = some (sb,sc)) ∧ Ready s targets sources fields
  | _,_,_,_ => False

theorem ready_after_scalar (s : NState) (target : Nat) (ty : Ty) (tb : Proofs.CppState.Binding)
    (tc : Proofs.CppState.Cell) (value : Int) (targetCell : s.scalarCell target ty = some (tb,tc))
    (accepted : ty.valid value = true) (targets sources : List Nat) (fields : List (Ty × Bool))
    (ready : Ready s targets sources fields) : Ready (scalarStep s tb tc value) targets sources fields := by
  induction targets generalizing sources fields with
  | nil => cases sources <;> cases fields <;> simp_all [Ready]
  | cons t targets ih =>
    cases sources with
    | nil => exact False.elim ready
    | cons source sources =>
      cases fields with
      | nil => exact False.elim ready
      | cons field fields =>
        obtain ⟨ft,fw⟩ := field
        obtain ⟨permission,⟨b,c,found,writable⟩,⟨sb,sc,sourceFound⟩,tail⟩ := ready
        obtain ⟨nextCell,nextFound⟩ := scalar_readable s target ty tb tc value targetCell accepted t ft b c found
        obtain ⟨nextSource,nextSourceFound⟩ := scalar_readable s target ty tb tc value targetCell accepted source ft sb sc sourceFound
        exact ⟨permission,⟨b,nextCell,nextFound,writable⟩,⟨sb,nextSource,nextSourceFound⟩,ih sources fields tail⟩

theorem fields_terminate (s : NState) (targets sources : List Nat) (fields : List (Ty × Bool))
    (ready : Ready s targets sources fields) : ∃ out, assignFields s targets sources fields = some out := by
  induction targets generalizing s sources fields with
  | nil => cases sources <;> cases fields <;> simp_all [Ready,assignFields]
  | cons target targets ih =>
    cases sources with
    | nil => exact False.elim ready
    | cons source sources =>
      cases fields with
      | nil => exact False.elim ready
      | cons field fields =>
        obtain ⟨ty,writable⟩ := field
        obtain ⟨permission,⟨tb,tc,targetCell,targetWritable⟩,⟨sb,sc,sourceCell⟩,tail⟩ := ready
        have scalarRun := scalar_runs s target source ty tb sb tc sc targetCell sourceCell targetWritable
        have nextReady := ready_after_scalar s target ty tb tc sc.value targetCell
          (Proofs.CppClassCopyCommands.scalar_cell_facts s source ty sb sc sourceCell).2 targets sources fields tail
        obtain ⟨out,ran⟩ := ih (scalarStep s tb tc sc.value) sources fields nextReady
        refine ⟨out,?_⟩
        simp [assignFields,permission,scalarRun,ran]


theorem ready_transfer (s t : NState) (targets sources : List Nat) (fields : List (Ty × Bool))
    (same : ∀ slot ty, t.scalarCell slot ty = s.scalarCell slot ty)
    (ready : Ready s targets sources fields) : Ready t targets sources fields := by
  induction targets generalizing sources fields with
  | nil => cases sources <;> cases fields <;> simp_all [Ready]
  | cons target targets ih =>
    cases sources with
    | nil => exact False.elim ready
    | cons source sources =>
      cases fields with
      | nil => exact False.elim ready
      | cons field fields =>
        obtain ⟨ty,writable⟩ := field
        obtain ⟨permission,⟨tb,tc,tr,w⟩,⟨sb,sc,sr⟩,tail⟩ := ready
        exact ⟨permission,⟨tb,tc,by rw [same]; exact tr,w⟩,⟨sb,sc,by rw [same]; exact sr⟩,ih sources fields tail⟩

theorem class_terminate (s : NState) (target source : ObjectRef) (profile : Profile) (a b : Nat)
    (tb sb : Binding) (targetBuffer sourceBuffer : Buffer Value)
    (permission : profile.vectorWritable = true)
    (targetSlot : s.vectorSlot target.vectorSlot = some a) (sourceSlot : s.vectorSlot source.vectorSlot = some b)
    (tr : s.frame.resolve a (.integer profile.element) = some (tb,targetBuffer))
    (sr : s.frame.resolve b (.integer profile.element) = some (sb,sourceBuffer))
    (writable : tb.writable = true) (bound : sourceBuffer.items.length ≤ targetBuffer.limit)
    (ready : Ready s target.scalarSlots source.scalarSlots profile.scalarFields) :
    ∃ out, assignClass s target source profile = some (out,target) := by
  obtain ⟨result,primitive,vectorRun,valid⟩ := Proofs.CppFrameCopyAssign.assign_runs ⟨s.frame,fun _ _ => 0⟩ a b profile.element
    tb sb targetBuffer sourceBuffer tr sr writable bound
  have data : dataAssign s.frame a b profile.element = some (after ⟨s.frame,fun _ _ => 0⟩ tb.owner targetBuffer result).frame := by
    rw [← frame_data ⟨s.frame,fun _ _ => 0⟩ a b profile.element]
    simp [vectorRun]
  have nextReady := ready_transfer s (vectorState s (after ⟨s.frame,fun _ _ => 0⟩ tb.owner targetBuffer result).frame)
    target.scalarSlots source.scalarSlots profile.scalarFields (fun _ _ => rfl) ready
  obtain ⟨out,fieldsRun⟩ := fields_terminate _ _ _ _ nextReady
  exact ⟨out,class_runs s target source profile a b _ out permission targetSlot sourceSlot data fieldsRun⟩

theorem data_lifts (s out : NState) (generation : Generations) (target source result : ObjectRef) (profile : Profile)
    (ran : assignClass s target source profile = some (out,result)) :
    ∃ nextGeneration, trackedAssignClass s generation target source profile = some ((out,result),nextGeneration) := by
  have projected := (tracked_class_data s generation target source profile).trans ran
  obtain ⟨⟨pair,g⟩,tracked,equal⟩ := Option.map_eq_some_iff.mp projected
  cases equal
  exact ⟨g,tracked⟩

theorem tracked_retired (s out : NState) (generation nextGeneration : Generations)
    (target source result : ObjectRef) (profile : Profile)
    (ran : trackedAssignClass s generation target source profile = some ((out,result),nextGeneration))
    (ref : TrackedReference) (old : Retired ⟨s.frame,generation⟩ ref) : Retired ⟨out.frame,nextGeneration⟩ ref := by
  unfold trackedAssignClass at ran
  split at ran
  · obtain ⟨a,targetSlot,rest⟩ := bind_some _ _ _ ran
    obtain ⟨b,sourceSlot,rest⟩ := bind_some _ _ _ rest
    obtain ⟨tracked,vectorRun,rest⟩ := bind_some _ _ _ rest
    obtain ⟨actual,fieldsRun,rest⟩ := bind_some _ _ _ rest
    have same := Prod.mk.inj (Option.some.inj rest)
    have dataSame := Prod.mk.inj same.1
    have frameSame := (fields_metadata _ actual target.scalarSlots source.scalarSlots profile.scalarFields fieldsRun).1
    have next := Proofs.CppFrameCopyAssign.assign_retired ⟨s.frame,generation⟩ tracked a b profile.element vectorRun ref old
    rw [dataSame.1] at frameSame
    rw [frameSame,← same.2]
    exact next
  · simp at ran

inductive ClassAssignments : NState → Generations → NState → Generations → Prop where
  | done (s : NState) (g : Generations) : ClassAssignments s g s g
  | step (s next out : NState) (g middle final : Generations) (target source result : ObjectRef) (profile : Profile)
      (ran : trackedAssignClass s g target source profile = some ((next,result),middle))
      (tail : ClassAssignments next middle out final) : ClassAssignments s g out final

theorem ClassAssignments.retired {s out : NState} {g final : Generations}
    (runs : ClassAssignments s g out final) (ref : TrackedReference) (old : Retired ⟨s.frame,g⟩ ref) :
    Retired ⟨out.frame,final⟩ ref := by
  induction runs with
  | done s g => exact old
  | step s next out g middle final target source result profile ran tail ih =>
    exact ih (tracked_retired s next g middle target source result profile ran ref old)

theorem ClassAssignments.no_resurrection {s out : NState} {g final : Generations}
    (runs : ClassAssignments s g out final) (ref : TrackedReference) (old : Retired ⟨s.frame,g⟩ ref) :
    Proofs.CppFrameCopyAssign.read ⟨out.frame,final⟩ ref = none :=
  retired_read _ ref (runs.retired ref old)


open Proofs.CppLoop (Outcome)

def fieldsCommand : List Nat → List Nat → List (Ty × Bool) → Option Command
  | [],[],[] => some (.primitive .skip)
  | target::targets,source::sources,(ty,writable)::fields => do
    if writable then
      let tail ← fieldsCommand targets sources fields
      some (.sequence (.primitive (.assign target ty (.variable ty source))) tail)
    else none
  | _,_,_ => none

theorem fields_program (s out : NState) (targets sources : List Nat) (fields : List (Ty × Bool))
    (ran : assignFields s targets sources fields = some out) :
    ∃ command, fieldsCommand targets sources fields = some command ∧
      runFuel (fields.length+1) command s = .finished ⟨out,none,false⟩ := by
  induction targets generalizing s sources fields with
  | nil =>
    cases sources <;> cases fields <;> simp_all [assignFields]
    exact ⟨.primitive .skip,rfl,rfl⟩
  | cons target targets ih =>
    cases sources with
    | nil => simp [assignFields] at ran
    | cons source sources =>
      cases fields with
      | nil => simp [assignFields] at ran
      | cons field fields =>
        obtain ⟨ty,writable⟩ := field
        unfold assignFields at ran
        split at ran
        · rename_i permission
          obtain ⟨next,head,tail⟩ := bind_some _ _ _ ran
          obtain ⟨tb,sb,tc,sc,_,_,_,_,commandRun⟩ := scalar_success s next target source ty head
          obtain ⟨command,generated,executed⟩ := ih next sources fields tail
          refine ⟨.sequence (.primitive (.assign target ty (.variable ty source))) command,?_,?_⟩
          · simp [fieldsCommand,permission,generated]
          · have firstRun : runFuel (fields.length+1) (.primitive (.assign target ty (.variable ty source))) s =
                .finished ⟨next,none,false⟩ := by
              rw [runFuel,commandRun]
              rfl
            change runFuel (fields.length+2) (.sequence (.primitive (.assign target ty (.variable ty source))) command) s = _
            rw [runFuel,firstRun]
            change runFuel (fields.length+1) command next = _
            exact executed
        · simp at ran


def liveScalar (s : NState) : Nat := s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length

theorem scalar_peak (s : NState) (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell) (value : Int) :
    (scalarStep s binding cell value).scalars.baseMemory = s.scalars.baseMemory ∧
      (scalarStep s binding cell value).scalars.peak = max s.scalars.peak (liveScalar s+1) ∧
      (scalarStep s binding cell value).peak =
        max s.peak (max s.scalars.peak (liveScalar s+1)+s.frame.state.storage.peak) := by
  simp only [scalarStep,NState.release,NState.charge,NState.observe,Proofs.CppState.State.observe,
    List.take_length,List.length_set,liveScalar]
  constructor
  · trivial
  · constructor <;> omega

theorem fields_peak (s out : NState) (targets sources : List Nat) (fields : List (Ty × Bool))
    (ran : assignFields s targets sources fields = some out) :
    out.scalars.baseMemory = s.scalars.baseMemory ∧
      out.scalars.peak ≤ max s.scalars.peak (liveScalar s+1) ∧
      out.peak ≤ max s.peak (max s.scalars.peak (liveScalar s+1)+s.frame.state.storage.peak) := by
  induction targets generalizing s sources fields with
  | nil => cases sources <;> cases fields <;> simp_all [assignFields]; omega
  | cons target targets ih =>
    cases sources with
    | nil => simp [assignFields] at ran
    | cons source sources =>
      cases fields with
      | nil => simp [assignFields] at ran
      | cons field fields =>
        obtain ⟨ty,writable⟩ := field
        unfold assignFields at ran
        split at ran
        · obtain ⟨next,head,tail⟩ := bind_some _ _ _ ran
          obtain ⟨tb,sb,tc,sc,_,_,_,nextEq,_⟩ := scalar_success s next target source ty head
          have one := scalar_peak s tb tc sc.value
          have data := scalar_fields s tb tc sc.value
          rw [← nextEq] at one data
          have live : liveScalar next = liveScalar s := by
            unfold liveScalar
            rw [one.1,data.2.2.2.1,data.2.2.2.2.1,List.length_set]
          have rest := ih next sources fields tail
          rw [live,one.2.1,one.2.2,data.1] at rest
          refine ⟨rest.1.trans one.1,?_,?_⟩ <;> omega
        · simp at ran


theorem class_peak (s out : NState) (target source result : ObjectRef) (profile : Profile)
    (ran : assignClass s target source profile = some (out,result)) :
    out.scalars.baseMemory = s.scalars.baseMemory ∧
      out.scalars.peak ≤ max s.scalars.peak (liveScalar s+1) ∧
      out.peak ≤ max s.peak (max s.scalars.peak (liveScalar s+1)+out.frame.state.storage.peak) := by
  obtain ⟨_,a,b,frame,_,_,_,fieldsRun,frameEq,_⟩ := class_success s out target source result profile ran
  have peaks := fields_peak (vectorState s frame) out target.scalarSlots source.scalarSlots profile.scalarFields fieldsRun
  have scalarInit : (vectorState s frame).scalars.peak = max s.scalars.peak (liveScalar s) := rfl
  have outerInit : (vectorState s frame).peak = max s.peak (max s.scalars.peak (liveScalar s)+frame.state.storage.peak) := rfl
  have live : liveScalar (vectorState s frame) = liveScalar s := rfl
  rw [live,scalarInit,outerInit] at peaks
  refine ⟨peaks.1,?_,?_⟩
  · omega
  · rw [frameEq]
    change out.peak ≤ max s.peak (max s.scalars.peak (liveScalar s+1)+frame.state.storage.peak)
    change out.scalars.baseMemory = s.scalars.baseMemory ∧ _ ∧ out.peak ≤
      max (max s.peak (max s.scalars.peak (liveScalar s)+frame.state.storage.peak))
        (max (max s.scalars.peak (liveScalar s)) (liveScalar s+1)+frame.state.storage.peak) at peaks
    omega

theorem class_wellFormed (s out : NState) (target source result : ObjectRef) (profile : Profile)
    (ran : assignClass s target source profile = some (out,result)) : out.frame.state.wellFormed = true := by
  obtain ⟨_,a,b,frame,_,_,vectorRun,_,frameEq,_⟩ := class_success s out target source result profile ran
  unfold dataAssign at vectorRun
  obtain ⟨tracked,trackedRun,equal⟩ := Option.map_eq_some_iff.mp vectorRun
  obtain ⟨tb,sb,t,v,assignment,tr,sr,w,bound,primitive,post,valid⟩ :=
    Proofs.CppFrameCopyAssign.assign_success ⟨s.frame,fun _ _ => 0⟩ tracked a b profile.element trackedRun
  rw [frameEq,← equal]
  exact valid

end Proofs.CppClassAssign
