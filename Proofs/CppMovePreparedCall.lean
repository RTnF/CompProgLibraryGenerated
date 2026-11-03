import Proofs.CppNoResizeValid
import Proofs.CppMoveCallRestore
import Proofs.CppMoveArgumentFacts

namespace Proofs.CppMovePreparedCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppMoveContext
open Proofs.CppMoveHeaders Proofs.CppMoveRestore Proofs.CppLoop Proofs.CppMoveCallRestore
open Proofs.DynamicResultValid

-- Prepare only live caller slots and real parameters, not historical grants.
def preparedCallFuel (program : NProgram) (fuel : Nat) (caller : Context) (ty : Ty)
    (arguments : List NArgument) : Outcome (Context × Ret) :=
  if eligible program then do
    let initial ← liftChecked (prepareArguments caller ty program.parameters arguments)
    let step ← runFuel fuel program.body (project initial ty)
    if step.breaking then .fault else do
      let (after,result) ← liftChecked (Proofs.CppNestedCall.finish (project caller ty) step.state program.result step.returned)
      let out ← liftChecked (restoreContext caller ty after)
      pure (out,result)
  else .fault

theorem installBorrow_scope (s out : Context) (argument : Borrow) (slot : Nat)
    (run : installBorrow s argument = some (out,slot)) : out.scope = s.scope := by
  unfold installBorrow at run
  obtain ⟨pair,_,rest⟩ := bind_some _ _ _ run
  have eq := (Prod.mk.inj (Option.some.inj rest)).1
  rw [← eq]

theorem bindSaved_scope (s out : Context) (argument : SavedArgument)
    (run : bindSaved s argument = some out) : out.scope = s.scope := by
  cases argument with
  | scalar parameter argument =>
    unfold bindSaved at run
    obtain ⟨scalars,_,rest⟩ := bind_some _ _ _ run
    have eq := Option.some.inj rest
    subst out
    rfl
  | vector argument =>
    unfold bindSaved at run
    obtain ⟨pair,installed,rest⟩ := bind_some _ _ _ run
    rcases pair with ⟨next,slot⟩
    have eq := Option.some.inj rest
    subst out
    exact installBorrow_scope s next argument slot installed

theorem bindSavedAll_scope (s out : Context) (arguments : List SavedArgument)
    (run : bindSavedAll s arguments = some out) : out.scope = s.scope := by
  induction arguments generalizing s with
  | nil => cases Option.some.inj run; rfl
  | cons head tail ih =>
    obtain ⟨next,first,rest⟩ := bind_some _ _ _ run
    exact (ih next rest).trans (bindSaved_scope s next head first)

theorem prepareArguments_effects (caller initial : Context) (ty : Ty)
    (parameters : List Proofs.CppVectorBindings.Parameter) (arguments : List NArgument)
    (run : prepareArguments caller ty parameters arguments = some initial) :
    initial.objects.heap = caller.objects.heap ∧ initial.scope = caller.scope+1 := by
  unfold prepareArguments at run
  obtain ⟨pair,resolved,prepared⟩ := bind_some _ _ _ run
  rcases pair with ⟨last,saved⟩
  have stable := Proofs.CppMoveArgumentFacts.resolveArguments_stable caller last ty parameters arguments saved resolved
  have heap := (prepareSaved_effects last initial saved prepared).1
  have scope := bindSavedAll_scope (prepareBase last saved.length) initial saved prepared
  exact ⟨heap.trans (congrArg Proofs.CppMoveViews.State.heap stable.objects),by simpa [prepareBase,observe,stable.scope] using scope⟩

theorem retire_work (before after : Proofs.CppNestedVectorBindings.Frame) (scope : Nat)
    (fresh : ∀ owner, before.state.forest.context owner ≠ some scope)
    (actual : before.retireScope scope = some after) : after.state.storage.work = before.state.storage.work := by
  unfold Proofs.CppNestedVectorBindings.Frame.retireScope at actual
  obtain ⟨state,retired,done⟩ := bind_some _ _ _ actual
  unfold Proofs.CppNestedVectorStore.State.retireScope at retired
  split at retired
  · dsimp only at retired
    split at retired
    · have eq := Option.some.inj retired
      subst state
      have eq := Option.some.inj done
      subst after
      rw [Proofs.CppNestedScope.retired_fresh before.state scope fresh]
    · simp at retired
  · simp at retired

theorem finish_work (caller callee out : NState) (ty : Ty) (returned : Option Ret) (result : Ret)
    (fresh : ∀ owner, callee.frame.state.forest.context owner ≠ some callee.scope)
    (actual : Proofs.CppNestedCall.finish caller callee (.scalar ty) returned = some (out,result)) :
    out.work = callee.work+1 := by
  cases returned with
  | none => simp [Proofs.CppNestedCall.finish] at actual
  | some ret =>
    cases ret with
    | unit => simp [Proofs.CppNestedCall.finish] at actual
    | vector owner element => simp [Proofs.CppNestedCall.finish] at actual
    | scalar value =>
      unfold Proofs.CppNestedCall.finish at actual
      dsimp only at actual
      split at actual
      · split at actual
        · obtain ⟨⟨frame,r⟩,finished,rest⟩ := bind_some _ _ _ actual
          have eq := congrArg Prod.fst (Option.some.inj finished)
          change callee.frame = frame at eq
          subst frame
          obtain ⟨retired,ran,done⟩ := bind_some _ _ _ rest
          have eq := congrArg Prod.fst (Option.some.inj done)
          change _ = out at eq
          subst out
          have work := retire_work callee.frame retired callee.scope fresh ran
          change callee.scalars.work+1+retired.state.storage.work =
            callee.scalars.work+callee.frame.state.storage.work+1
          rw [work]
          omega
        · simp at actual
      · simp at actual

theorem retire_peak (before after : Proofs.CppNestedVectorBindings.Frame) (scope : Nat)
    (actual : before.retireScope scope = some after) :
    after.state.storage.peak = max before.state.storage.peak (before.state.liveSpace-before.state.storage.baseSpace) := by
  unfold Proofs.CppNestedVectorBindings.Frame.retireScope at actual
  obtain ⟨state,retired,done⟩ := bind_some _ _ _ actual
  unfold Proofs.CppNestedVectorStore.State.retireScope at retired
  split at retired
  · dsimp only at retired
    split at retired
    · have eq := Option.some.inj retired
      subst state
      have eq := Option.some.inj done
      subst after
      rfl
    · simp at retired
  · simp at retired

theorem finish_counters (caller callee out : NState) (ty : Ty) (returned : Option Ret) (result : Ret)
    (actual : Proofs.CppNestedCall.finish caller callee (.scalar ty) returned = some (out,result)) :
    out.scalars.peak = max (max caller.scalars.peak callee.scalars.peak)
      (caller.scalars.memory.length-caller.scalars.baseMemory+caller.scalars.bindings.length) ∧
    out.frame.state.storage.peak = max callee.frame.state.storage.peak
      (callee.frame.state.liveSpace-callee.frame.state.storage.baseSpace) ∧
    out.peak = max (max caller.peak callee.peak) (out.scalars.peak+out.frame.state.storage.peak) := by
  cases returned with
  | none => simp [Proofs.CppNestedCall.finish] at actual
  | some ret =>
    cases ret with
    | unit => simp [Proofs.CppNestedCall.finish] at actual
    | vector owner element => simp [Proofs.CppNestedCall.finish] at actual
    | scalar value =>
      unfold Proofs.CppNestedCall.finish at actual
      dsimp only at actual
      split at actual
      · rename_i guarded
        split at actual
        · obtain ⟨⟨frame,r⟩,finished,rest⟩ := bind_some _ _ _ actual
          have eq := congrArg Prod.fst (Option.some.inj finished)
          change callee.frame = frame at eq
          subst frame
          obtain ⟨retired,ran,done⟩ := bind_some _ _ _ rest
          have eq := congrArg Prod.fst (Option.some.inj done)
          change _ = out at eq
          subst out
          refine ⟨?_,retire_peak callee.frame retired callee.scope ran,rfl⟩
          simp [NState.observe,Proofs.CppState.State.observe,List.length_take,Nat.min_eq_left guarded.1]
        · simp at actual
      · simp at actual

theorem restored_finish_counters (caller out : Context) (ty retType : Ty) (callee after : NState) (returned : Option Ret) (result : Ret)
    (finished : Proofs.CppNestedCall.finish (project caller ty) callee (.scalar retType) returned = some (after,result))
    (restored : restoreContext caller ty after = some out) (covered : OwnsAll caller.objects.heap) :
    out.scalars.peak = max (max caller.scalars.peak callee.scalars.peak)
      (caller.scalars.memory.length-caller.scalars.baseMemory+caller.scalars.bindings.length) ∧
    out.objects.heap.peak = max callee.frame.state.storage.peak
      (callee.frame.state.liveSpace-callee.frame.state.storage.baseSpace) ∧
    out.peak = max (max caller.peak callee.peak) (out.scalars.peak+out.objects.heap.peak) := by
  have counters := finish_counters (project caller ty) callee after retType returned result finished
  rw [← restoreContext_project caller out ty after restored covered] at counters
  exact counters

-- Normal result conditions construct the actual finish, rather than assuming it.
theorem finish_ready (caller callee : NState) (ty : Ty) (value : Int)
    (fits : caller.scalars.memory.length ≤ callee.scalars.memory.length)
    (types : (callee.scalars.memory.take caller.scalars.memory.length).map Proofs.CppState.Cell.type =
      caller.scalars.memory.map Proofs.CppState.Cell.type)
    (valid : callee.frame.state.wellFormed = true) (valueValid : ty.valid value = true) :
    ∃ out, Proofs.CppNestedCall.finish caller callee (.scalar ty) (some (.scalar value)) = some (out,.scalar value) := by
  let retired : Proofs.CppNestedVectorBindings.Frame :=
    {callee.frame with state := callee.frame.state.retired callee.scope}
  have ran : callee.frame.retireScope callee.scope = some retired := by
    simp [Proofs.CppNestedVectorBindings.Frame.retireScope,
      Proofs.CppNestedVectorStore.retireScope_valid_input callee.frame.state callee.scope valid,retired]
  let scalars : Proofs.CppState.State := {caller.scalars with
    memory := callee.scalars.memory.take caller.scalars.memory.length,
    work := callee.scalars.work+1,peak := max caller.scalars.peak callee.scalars.peak}
  let frame := {retired with bindings := caller.frame.bindings}
  exact ⟨((⟨scalars.observe 0,frame,caller.slots,caller.scope,max caller.peak callee.peak⟩ : NState).observe),
    by simp [Proofs.CppNestedCall.finish,fits,types,valueValid,ran,scalars,frame]⟩

theorem preparedCall_ready (program : NProgram) (fuel : Nat) (caller initial : Context)
    (ty retType : Ty) (arguments : List NArgument) (step : NStep) (after : NState) (result : Ret)
    (scalar : program.result = .scalar retType)
    (allowed : Proofs.CppNoResizeScope.Allowed program.body = true)
    (contexts : ∀ owner scope, (project caller ty).frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (covered : OwnsAll caller.objects.heap)
    (prepared : prepareArguments caller ty program.parameters arguments = some initial)
    (ran : runFuel fuel program.body (project initial ty) = .finished step)
    (notBreaking : step.breaking = false)
    (finished : Proofs.CppNestedCall.finish (project caller ty) step.state (.scalar retType) step.returned = some (after,result)) :
    ∃ out, preparedCallFuel program fuel caller ty arguments = .finished (out,result) ∧ project out ty = after ∧
      work out = step.state.work+1 := by
  have prep := prepareArguments_effects caller initial ty program.parameters arguments prepared
  have state : (project initial ty).frame.state = (project caller ty).frame.state := by
    simp only [project,Proofs.CppMoveFrame.materialize,prep.1]
  have flags : (project initial ty).frame.rootWritable = (project caller ty).frame.rootWritable := by
    simp only [project,Proofs.CppMoveFrame.materialize,prep.1]
  have scope : (project initial ty).scope = (project caller ty).scope+1 := prep.2
  have innerContexts : ∀ owner sc, (project initial ty).frame.state.forest.context owner = some sc → sc ≤ initial.scope := by
    intro owner sc found
    rw [state] at found
    rw [prep.2]
    exact Nat.le_trans (contexts owner sc found) (Nat.le_succ _)
  have body := Proofs.CppNoResizeRun.run_headers fuel program.body (project initial ty) step allowed innerContexts ran
  have headers : Proofs.CppBufferHeaders.SameHeaders (project caller ty).frame.state step.state.frame.state := by
    rw [← state]
    exact body.headers
  have effects := Proofs.CppCallFrame.finish_scalar_frame (project caller ty) step.state after retType step.returned result
    headers (body.flags.trans flags) (body.scopedState.trans scope) contexts finished
  obtain ⟨out,restored⟩ := restoreContext_ready caller ty after effects.slots effects.scopedState effects.vectorBindings
    effects.scalarBindings effects.memoryLength effects.base effects.headers effects.flags covered
    (finish_valid (project caller ty) step.state after retType step.returned result finished)
  have fresh : ∀ owner, step.state.frame.state.forest.context owner ≠ some step.state.scope := by
    intro owner found
    rw [headers.forest] at found
    have bound := contexts owner step.state.scope found
    rw [body.scopedState,scope] at bound
    change caller.scope+1 ≤ caller.scope at bound
    omega
  refine ⟨out,?_,restoreContext_project caller out ty after restored covered,?_⟩
  · simp [preparedCallFuel,eligible,scalar,allowed,prepared,ran,notBreaking,finished,restored,
      bind,Outcome.bind,liftChecked,pure]
  · rw [← project_work out ty,restoreContext_project caller out ty after restored covered]
    exact finish_work (project caller ty) step.state after retType step.returned result fresh finished

theorem preparedCall_of_body (program : NProgram) (fuel : Nat) (caller initial : Context)
    (ty retType : Ty) (arguments : List NArgument) (callee : NState) (value : Int)
    (scalar : program.result = .scalar retType)
    (allowed : Proofs.CppNoResizeScope.Allowed program.body = true)
    (contexts : ∀ owner scope, (project caller ty).frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (covered : OwnsAll caller.objects.heap)
    (valid : (project caller ty).frame.state.wellFormed = true)
    (prepared : prepareArguments caller ty program.parameters arguments = some initial)
    (ran : runFuel fuel program.body (project initial ty) = .finished ⟨callee,some (.scalar value),false⟩)
    (fits : caller.scalars.memory.length ≤ callee.scalars.memory.length)
    (types : (callee.scalars.memory.take caller.scalars.memory.length).map Proofs.CppState.Cell.type =
      caller.scalars.memory.map Proofs.CppState.Cell.type)
    (valueValid : retType.valid value = true) :
    ∃ out, preparedCallFuel program fuel caller ty arguments = .finished (out,.scalar value) ∧
      work out = callee.work+1 := by
  have prep := prepareArguments_effects caller initial ty program.parameters arguments prepared
  have state : (project initial ty).frame.state = (project caller ty).frame.state := by
    simp only [project,Proofs.CppMoveFrame.materialize,prep.1]
  have innerContexts : ∀ owner sc, (project initial ty).frame.state.forest.context owner = some sc → sc ≤ initial.scope := by
    intro owner sc found
    rw [state] at found
    rw [prep.2]
    exact Nat.le_trans (contexts owner sc found) (Nat.le_succ _)
  have initialValid : (project initial ty).frame.state.wellFormed = true := by rw [state]; exact valid
  have calleeValid := Proofs.CppNoResizeValid.run_valid fuel program.body (project initial ty)
    ⟨callee,some (.scalar value),false⟩ allowed innerContexts initialValid ran
  obtain ⟨after,finished⟩ := finish_ready (project caller ty) callee retType value fits types calleeValid valueValid
  obtain ⟨out,actual,_,cost⟩ := preparedCall_ready program fuel caller initial ty retType arguments
    ⟨callee,some (.scalar value),false⟩ after (.scalar value) scalar allowed contexts covered prepared ran rfl finished
  exact ⟨out,actual,cost⟩

end Proofs.CppMovePreparedCall
