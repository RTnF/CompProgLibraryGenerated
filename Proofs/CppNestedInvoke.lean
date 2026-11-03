import Proofs.CppClassCopyCommands
import Proofs.CppConstructorView
import Proofs.CppClassAssign

-- Ordinary NProgram calls with a caller-owned scalar result local.
namespace Proofs.CppNestedInvoke
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedStmt
open Proofs.CppLoop

def saveResult (s : NState) (ty : Ty) (value : Int) : NState :=
  (s.declared ty false value).charge 1 0

-- callFuel consumes the callee's return and retires its scope. The enclosing
-- caller continues with a fresh read-only scalar local and no pending return.
def invokeScalarFuel (program : NProgram) (fuel : Nat) (caller : NState)
    (arguments : List NArgument) : Outcome NStep := do
  let .scalar ty := program.result | .fault
  let (next,returned) ← program.callFuel fuel caller arguments
  let .scalar value := returned | .fault
  pure ⟨saveResult next ty value,none,false⟩

theorem invoke_of_call (program : NProgram) (fuel : Nat) (caller next : NState)
    (arguments : List NArgument) (ty : Ty) (value : Int)
    (kind : program.result = .scalar ty)
    (actual : program.callFuel fuel caller arguments = .finished (next,.scalar value)) :
    invokeScalarFuel program fuel caller arguments =
      .finished ⟨saveResult next ty value,none,false⟩ := by
  simp [invokeScalarFuel,kind,actual,Bind.bind,Outcome.bind,Pure.pure]

theorem invoke_of_steps (program : NProgram) (fuel : Nat) (caller initial callee next : NState)
    (arguments : List NArgument) (ty : Ty) (value : Int) (returned : Option Ret)
    (kind : program.result = .scalar ty)
    (prepared : prepare caller program.parameters arguments = some initial)
    (executed : Proofs.CppNestedProgram.runFuel fuel program.body initial =
      .finished ⟨callee,returned,false⟩)
    (finished : finish caller callee (.scalar ty) returned = some (next,.scalar value)) :
    invokeScalarFuel program fuel caller arguments =
      .finished ⟨saveResult next ty value,none,false⟩ := by
  apply invoke_of_call program fuel caller next arguments ty value kind
  simp [NProgram.callFuel,prepared,executed,kind,finished,liftChecked,Bind.bind,Outcome.bind]

theorem save_result_fields (s : NState) (ty : Ty) (value : Int) :
    (saveResult s ty value).frame = s.frame ∧
    (saveResult s ty value).scope = s.scope ∧
    (saveResult s ty value).scalars.memory = s.scalars.memory++[⟨ty,value⟩] ∧
    (saveResult s ty value).scalars.bindings = s.scalars.bindings++[⟨s.scalars.memory.length,false⟩] ∧
    (saveResult s ty value).slots = s.slots++[.scalar s.scalars.bindings.length] :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem save_result_keeps (s : NState) (newTy : Ty) (value : Int) (slot : Nat) (ty : Ty)
    (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell)
    (actual : s.scalarCell slot ty = some (binding,cell)) :
    (saveResult s newTy value).scalarCell slot ty = some (binding,cell) :=
  Proofs.CppClassCopyCommands.scalar_step_keeps s newTy false value slot ty binding cell actual


theorem save_result_vector_slot (s : NState) (newTy : Ty) (value : Int)
    (slot index : Nat) (actual : s.vectorSlot slot = some index) :
    (saveResult s newTy value).vectorSlot slot = some index := by
  have inside : slot < s.slots.length := by
    by_cases inside : slot < s.slots.length
    · exact inside
    · have missing := List.getElem?_eq_none_iff.mpr (show s.slots.length ≤ slot by omega)
      simp [NState.vectorSlot,missing] at actual
  simpa only [NState.vectorSlot,saveResult,NState.declared,NState.charge,NState.observe,
    List.getElem?_append_left inside] using actual

theorem save_result_work (s : NState) (ty : Ty) (value : Int) :
    (saveResult s ty value).work = s.work+1 := by
  simp [saveResult,NState.declared,NState.charge,NState.observe,NState.work,
    Proofs.CppState.State.observe,Nat.add_assoc,Nat.add_comm]

theorem save_result_peak (s : NState) (ty : Ty) (value : Int) :
    (saveResult s ty value).scalars.peak = max s.scalars.peak
      ((s.scalars.memory.length+1)-s.scalars.baseMemory+(s.scalars.bindings.length+1)) ∧
    (saveResult s ty value).peak =
      max s.peak ((saveResult s ty value).scalars.peak+s.frame.state.storage.peak) := by
  constructor
  · simp [saveResult,NState.declared,NState.charge,NState.observe,Proofs.CppState.State.observe]
  · rfl


theorem save_result_cell (s : NState) (ty : Ty) (value : Int)
    (valid : ty.valid value = true) :
    (saveResult s ty value).scalarCell s.slots.length ty =
      some (⟨s.scalars.memory.length,false⟩,⟨ty,value⟩) := by
  simp [NState.scalarCell,NState.scalarSlot,saveResult,NState.declared,
    NState.charge,NState.observe,Proofs.CppState.State.observe,valid]

-- No restriction on which caller cells the callee mutates is imposed here.
-- finish restores the caller's environment with the callee's updated values.
theorem finish_scalar_facts (caller callee next : NState) (ty : Ty)
    (returned : Option Ret) (value : Int)
    (actual : finish caller callee (.scalar ty) returned = some (next,.scalar value)) :
    ty.valid value = true ∧ next.slots = caller.slots ∧
      next.scalars.bindings = caller.scalars.bindings ∧
      next.scalars.memory.length = caller.scalars.memory.length ∧ next.scope = caller.scope := by
  cases returned with
  | none => simp [finish] at actual
  | some ret =>
    cases ret with
    | unit => simp [finish] at actual
    | vector owner element => simp [finish] at actual
    | scalar v =>
      unfold finish at actual
      dsimp only at actual
      split at actual
      · rename_i guarded
        try dsimp only at actual
        split at actual
        · rename_i valid
          obtain ⟨⟨frame,r⟩,finished,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ actual
          have eq := Option.some.inj finished
          cases eq
          obtain ⟨retired,ran,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
          have eq := Option.some.inj rest
          cases eq
          exact ⟨valid,rfl,rfl,by simp [NState.observe,Proofs.CppState.State.observe,
            List.length_take,Nat.min_eq_left guarded.1],rfl⟩
        · simp at actual
      · simp at actual

theorem call_scalar_facts (program : NProgram) (fuel : Nat) (caller next : NState)
    (arguments : List NArgument) (ty : Ty) (value : Int)
    (kind : program.result = .scalar ty)
    (actual : program.callFuel fuel caller arguments = .finished (next,.scalar value)) :
    ty.valid value = true ∧ next.slots = caller.slots ∧
      next.scalars.bindings = caller.scalars.bindings ∧
      next.scalars.memory.length = caller.scalars.memory.length ∧ next.scope = caller.scope := by
  cases prep : prepare caller program.parameters arguments with
  | none => simp [NProgram.callFuel,prep,liftChecked,Bind.bind,Outcome.bind] at actual
  | some initial =>
    cases ran : Proofs.CppNestedProgram.runFuel fuel program.body initial with
    | fault => simp [NProgram.callFuel,prep,ran,liftChecked,Bind.bind,Outcome.bind] at actual
    | exhausted => simp [NProgram.callFuel,prep,ran,liftChecked,Bind.bind,Outcome.bind] at actual
    | finished step =>
      cases breaking : step.breaking with
      | true => simp [NProgram.callFuel,prep,ran,breaking,liftChecked,Bind.bind,Outcome.bind] at actual
      | false =>
        have finished : finish caller step.state (.scalar ty) step.returned = some (next,.scalar value) := by
          cases result : finish caller step.state (.scalar ty) step.returned with
          | none => simp [NProgram.callFuel,prep,ran,breaking,kind,result,liftChecked,Bind.bind,Outcome.bind] at actual
          | some pair =>
            have eq : pair = (next,.scalar value) := by
              simpa [NProgram.callFuel,prep,ran,breaking,kind,result,liftChecked,Bind.bind,Outcome.bind] using actual
            simp only [eq]
        exact finish_scalar_facts caller step.state next ty step.returned value finished


theorem invoke_result (program : NProgram) (fuel : Nat) (caller next : NState)
    (arguments : List NArgument) (ty : Ty) (value : Int)
    (kind : program.result = .scalar ty)
    (actual : program.callFuel fuel caller arguments = .finished (next,.scalar value)) :
    invokeScalarFuel program fuel caller arguments = .finished ⟨saveResult next ty value,none,false⟩ ∧
    (saveResult next ty value).scalarCell caller.slots.length ty =
      some (⟨caller.scalars.memory.length,false⟩,⟨ty,value⟩) ∧
    (saveResult next ty value).work = next.work+1 ∧
    (saveResult next ty value).frame = next.frame ∧
    (saveResult next ty value).scope = caller.scope := by
  obtain ⟨valid,slots,bindings,memory,scope⟩ :=
    call_scalar_facts program fuel caller next arguments ty value kind actual
  refine ⟨invoke_of_call program fuel caller next arguments ty value kind actual,?_,
    save_result_work next ty value,rfl,scope⟩
  simpa only [slots,memory] using save_result_cell next ty value valid

theorem invoke_fault (program : NProgram) (fuel : Nat) (caller : NState)
    (arguments : List NArgument) (ty : Ty) (kind : program.result = .scalar ty)
    (actual : program.callFuel fuel caller arguments = .fault) :
    invokeScalarFuel program fuel caller arguments = .fault := by
  simp [invokeScalarFuel,kind,actual,Bind.bind,Outcome.bind]

theorem invoke_exhausted (program : NProgram) (fuel : Nat) (caller : NState)
    (arguments : List NArgument) (ty : Ty) (kind : program.result = .scalar ty)
    (actual : program.callFuel fuel caller arguments = .exhausted) :
    invokeScalarFuel program fuel caller arguments = .exhausted := by
  simp [invokeScalarFuel,kind,actual,Bind.bind,Outcome.bind]


-- Scalar results get a fresh local; void methods only update the caller.
def invokeMethodFuel (program : NProgram) (fuel : Nat) (caller : NState)
    (arguments : List NArgument) : Outcome NStep :=
  match program.result with
  | .scalar _ => invokeScalarFuel program fuel caller arguments
  | .unit => do
      let (out,result) ← program.callFuel fuel caller arguments
      let .unit := result | .fault
      pure ⟨out,none,false⟩
  | .vector _ => .fault

theorem invoke_unit (program : NProgram) (fuel : Nat) (caller out : NState)
    (arguments : List NArgument) (kind : program.result = .unit)
    (actual : program.callFuel fuel caller arguments = .finished (out,.unit)) :
    invokeMethodFuel program fuel caller arguments = .finished ⟨out,none,false⟩ := by
  simp [invokeMethodFuel,kind,actual,Bind.bind,Outcome.bind,Pure.pure]

-- A separate caller interpreter avoids recursively embedding NProgram in its
-- own body type. Method bodies still run through the original interpreter;
-- argument binding, mutation, return validation and retirement use callFuel.
inductive CallerCommand where
  | nested (body : Command)
  | invoke (program : NProgram) (arguments : List NArgument)
  | sequence (first rest : CallerCommand)
  | scope (body : CallerCommand)
  | branch (condition : NExpr) (yes no : CallerCommand)
  | whileLoop (condition : NExpr) (body : CallerCommand)
  | breakLoop
  | copyObject (source : Proofs.CppConstructorFinish.ObjectRef) (profile : Proofs.CppClassCopy.Profile)
  | constructObject (program : NProgram) (arguments : List NArgument) (vectorSlot : Nat)
      (fields : List Proofs.CppConstructorFinish.ScalarField) (profile : Proofs.CppClassCopy.Profile)
  | assignObject (target source : Proofs.CppConstructorFinish.ObjectRef) (profile : Proofs.CppClassCopy.Profile)

def runCallerFuel : Nat → CallerCommand → NState → Outcome NStep
  | 0,_,_ => .exhausted
  | fuel+1,command,s => match command with
    | .nested body => Proofs.CppNestedProgram.runFuel fuel body s
    | .invoke program arguments => invokeMethodFuel program fuel s arguments
    | .sequence first rest => do
        let step ← runCallerFuel fuel first s
        if step.returned.isSome || step.breaking then pure step
        else runCallerFuel fuel rest step.state
    | .scope body => do
        let step ← runCallerFuel fuel body {s with scope := s.scope+1}
        let restored ← liftChecked (s.leave step.state step.returned)
        pure {step with state := restored}
    | .branch condition yes no => do
        let (next,value) ← liftChecked (condition.eval s)
        let released := next.release s
        if value == 0 then runCallerFuel fuel no (released.charge 1 0)
        else runCallerFuel fuel yes (released.charge 1 0)
    | .whileLoop condition body => do
        let (next,value) ← liftChecked (condition.eval s)
        let released := next.release s
        if value == 0 then pure ⟨released.charge 1 0,none,false⟩ else do
          let step ← runCallerFuel fuel body (released.charge 1 0)
          if step.returned.isSome then pure step
          else if step.breaking then pure {step with breaking := false}
          else runCallerFuel fuel (.whileLoop condition body) step.state
    | .breakLoop => pure ⟨s.charge 1 0,none,true⟩
    | .copyObject source profile => Proofs.CppClassCopyCommands.runCopyFuel fuel s source profile
    | .constructObject program arguments vectorSlot fields profile => do
        let (out,_) ← Proofs.CppConstructorView.constructProfileFuel program fuel s arguments vectorSlot fields profile
        pure ⟨out,none,false⟩
    | .assignObject target source profile => do
        let (out,_) ← liftChecked (Proofs.CppClassAssign.assignClass s target source profile)
        pure ⟨out,none,false⟩

theorem caller_assign (fuel : Nat) (s out : NState)
    (target source : Proofs.CppConstructorFinish.ObjectRef) (profile : Proofs.CppClassCopy.Profile)
    (ran : Proofs.CppClassAssign.assignClass s target source profile = some (out,target)) :
    runCallerFuel (fuel+1) (.assignObject target source profile) s = .finished ⟨out,none,false⟩ := by
  simp [runCallerFuel,ran,liftChecked,bind,Outcome.bind,pure]

theorem caller_assign_tracked (fuel : Nat) (s out : NState) (generation : Proofs.CppClassAssign.Generations)
    (target source : Proofs.CppConstructorFinish.ObjectRef) (profile : Proofs.CppClassCopy.Profile)
    (ran : Proofs.CppClassAssign.assignClass s target source profile = some (out,target)) :
    ∃ nextGeneration,
      runCallerFuel (fuel+1) (.assignObject target source profile) s = .finished ⟨out,none,false⟩ ∧
      Proofs.CppClassAssign.trackedAssignClass s generation target source profile = some ((out,target),nextGeneration) := by
  obtain ⟨nextGeneration,tracked⟩ := Proofs.CppClassAssign.data_lifts s out generation target source target profile ran
  exact ⟨nextGeneration,caller_assign fuel s out target source profile ran,tracked⟩

theorem caller_construct_of_steps (program : NProgram) (fuel : Nat)
    (caller initial callee out : NState) (arguments : List NArgument)
    (vectorSlot : Nat) (fields : List Proofs.CppConstructorFinish.ScalarField)
    (profile : Proofs.CppClassCopy.Profile) (obj : Proofs.CppConstructorFinish.ObjectRef)
    (prepared : prepare caller program.parameters arguments = some initial)
    (executed : Proofs.CppNestedProgram.runFuel fuel program.body initial = .finished ⟨callee,none,false⟩)
    (finished : Proofs.CppConstructorView.finishProfile caller callee vectorSlot fields profile = some (out,obj)) :
    runCallerFuel (fuel+1) (.constructObject program arguments vectorSlot fields profile) caller =
      .finished ⟨out,none,false⟩ := by
  have actual := Proofs.CppConstructorView.construct_of_steps program fuel caller initial callee out
    arguments vectorSlot fields profile obj prepared executed finished
  simp [runCallerFuel,actual,Bind.bind,Outcome.bind,Pure.pure]

theorem caller_copy_complete (s : NState) (source : Proofs.CppConstructorFinish.ObjectRef)
    (profile : Proofs.CppClassCopy.Profile) (index : Nat)
    (binding : Proofs.CppNestedVectorBindings.Binding)
    (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value)
    (values : List Proofs.CppConstructorFinish.ScalarValue)
    (slot : s.vectorSlot source.vectorSlot = some index)
    (resolved : s.frame.resolve index (.integer profile.element) = some (binding,buffer))
    (lengths : s.frame.rootWritable.length = s.frame.state.forest.objects.length)
    (supported : Proofs.CppVectorBindings.supported profile.element)
    (captured : Proofs.CppClassCopy.captureAll s source.scalarSlots profile.scalarFields = some values) :
    runCallerFuel (values.length+3) (.copyObject source profile) s =
      .finished ⟨Proofs.CppClassCopyCommands.scalarResult
        (Proofs.CppClassCopyCommands.vectorResult s buffer profile) values,none,false⟩ := by
  obtain ⟨_,_,ran⟩ := Proofs.CppClassCopyCommands.copy_commands_complete s source profile index
    binding buffer values slot resolved lengths supported captured
  change Proofs.CppClassCopyCommands.runCopyFuel (values.length+2) s source profile = _
  exact ran

theorem caller_invoke (program : NProgram) (fuel : Nat) (caller next : NState)
    (arguments : List NArgument) (ty : Ty) (value : Int)
    (kind : program.result = .scalar ty)
    (actual : program.callFuel fuel caller arguments = .finished (next,.scalar value)) :
    runCallerFuel (fuel+1) (.invoke program arguments) caller =
      .finished ⟨saveResult next ty value,none,false⟩ :=
by
  change invokeMethodFuel program fuel caller arguments = _
  simp only [invokeMethodFuel,kind]
  exact invoke_of_call program fuel caller next arguments ty value kind actual

theorem caller_sequence (fuel : Nat) (first rest : CallerCommand) (s middle : NState)
    (out : NStep)
    (firstRun : runCallerFuel fuel first s = .finished ⟨middle,none,false⟩)
    (restRun : runCallerFuel fuel rest middle = .finished out) :
    runCallerFuel (fuel+1) (.sequence first rest) s = .finished out := by
  simp [runCallerFuel,firstRun,restRun,Bind.bind,Outcome.bind]

theorem caller_return (fuel : Nat) (first rest : CallerCommand) (s : NState) (out : NStep)
    (firstRun : runCallerFuel fuel first s = .finished out)
    (returned : out.returned.isSome = true) :
    runCallerFuel (fuel+1) (.sequence first rest) s = .finished out := by
  simp [runCallerFuel,firstRun,returned,Bind.bind,Outcome.bind,Pure.pure]

-- A source-level caller has its own call boundary, in addition to those of
-- its invoked methods. Flattened receiver fields are ordinary reference
-- parameters; reads by value for individual methods happen at that call.
structure CallerProgram where
  parameters : List Proofs.CppVectorBindings.Parameter
  result : Ty
  body : CallerCommand

def CallerProgram.callFuel (program : CallerProgram) (fuel : Nat) (caller : NState)
    (arguments : List NArgument) : Outcome (NState × Ret) := do
  let initial ← liftChecked (prepare caller program.parameters arguments)
  let step ← runCallerFuel fuel program.body initial
  if step.breaking then .fault else
    liftChecked (finish caller step.state (.scalar program.result) step.returned)

theorem caller_program_of_steps (program : CallerProgram) (fuel : Nat)
    (caller initial callee out : NState) (arguments : List NArgument)
    (returned : Option Ret) (value : Int)
    (prepared : prepare caller program.parameters arguments = some initial)
    (executed : runCallerFuel fuel program.body initial = .finished ⟨callee,returned,false⟩)
    (finished : finish caller callee (.scalar program.result) returned = some (out,.scalar value)) :
    program.callFuel fuel caller arguments = .finished (out,.scalar value) := by
  simp [CallerProgram.callFuel,prepared,executed,finished,liftChecked,Bind.bind,Outcome.bind]

-- Void source callers share the same prepared environment and cleanup, with
-- an explicit unit result kind rather than a fabricated scalar return value.
structure UnitCallerProgram where
  parameters : List Proofs.CppVectorBindings.Parameter
  body : CallerCommand

def UnitCallerProgram.callFuel (program : UnitCallerProgram) (fuel : Nat) (caller : NState)
    (arguments : List NArgument) : Outcome (NState × Ret) := do
  let initial ← liftChecked (prepare caller program.parameters arguments)
  let step ← runCallerFuel fuel program.body initial
  if step.breaking then .fault else
    liftChecked (finish caller step.state .unit step.returned)

theorem unit_caller_of_steps (program : UnitCallerProgram) (fuel : Nat)
    (caller initial callee out : NState) (arguments : List NArgument) (returned : Option Ret)
    (prepared : prepare caller program.parameters arguments = some initial)
    (executed : runCallerFuel fuel program.body initial = .finished ⟨callee,returned,false⟩)
    (finished : finish caller callee .unit returned = some (out,.unit)) :
    program.callFuel fuel caller arguments = .finished (out,.unit) := by
  simp [UnitCallerProgram.callFuel,prepared,executed,finished,liftChecked,Bind.bind,Outcome.bind]

end Proofs.CppNestedInvoke



