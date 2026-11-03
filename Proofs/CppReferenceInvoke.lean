import Proofs.CppLoop

namespace Proofs.CppReferenceInvoke
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop

-- Reference arguments identify an existing caller binding, never an arbitrary
-- address or a newly manufactured temporary reference.
inductive CallArgument where
  | value (expression : Expr)
  | reference (slot : Nat)
  deriving DecidableEq, Repr

def CallArgument.nodes : CallArgument → Nat
  | .value e => e.nodes
  | .reference _ => 1

def resolveArgument (caller : State) (parameter : Parameter) : CallArgument → Option (Argument × Nat)
  | .value expression => do
      if parameter.reference then none else do
        let result ← caller.evaluate expression
        pure (.value result.value,result.work)
  | .reference slot => do
      if !parameter.reference then none else do
        let binding ← caller.bindings[slot]?
        if parameter.writable && !binding.writable then none else do
          let cell ← caller.memory[binding.address]?
          if cell.type != parameter.type || !parameter.type.valid cell.value then none else
            pure (.reference binding.address,1)

def resolveArguments (caller : State) : List Parameter → List CallArgument → Option (List Argument × Nat)
  | [], [] => some ([],0)
  | p :: ps, a :: args => do
      let (argument,work) ← resolveArgument caller p a
      let (arguments,restWork) ← resolveArguments caller ps args
      pure (argument::arguments,work+restWork)
  | _, _ => none

def argumentPeak (caller : State) (arguments : List CallArgument) : Nat :=
  arguments.foldl (fun peak a => max peak ((caller.observe (arguments.length+a.nodes)).peak)) caller.peak

def prepare (caller : State) (parameters : List Parameter) (arguments : List CallArgument) : Option State := do
  let (resolved,argumentWork) ← resolveArguments caller parameters arguments
  let initial : State := {caller with
    memory := caller.memory ++ List.replicate caller.bindings.length ⟨⟨1,false,true⟩,0⟩
    bindings := []
    work := caller.work+1+argumentWork+parameters.length
    peak := argumentPeak caller arguments}
  bindArguments (initial.observe 0) parameters resolved

-- Preserve mutations of the caller prefix. Discard callee copies, bindings and
-- local cells; retain one private, read-only cell for the scalar return value.
def finish (caller : State) (resultType : Ty) (step : Step) : Option Step := do
  if step.breaking then none else do
    let value ← step.returned
    if !resultType.valid value || step.state.memory.length < caller.memory.length then none else do
      let next : State := {caller with
        memory := step.state.memory.take caller.memory.length ++ [⟨resultType,value⟩]
        bindings := caller.bindings ++ [⟨caller.memory.length,false⟩]
        work := step.state.work+1
        peak := max caller.peak step.state.peak}
      pure ⟨next.observe 0,none,false⟩

def run (caller : State) (parameters : List Parameter) (resultType : Ty)
    (arguments : List CallArgument) (body : Stmt) : Option Step := do
  let callee ← prepare caller parameters arguments
  let step ← body.run callee
  finish caller resultType step

def runFuel (fuel : Nat) (caller : State) (parameters : List Parameter) (resultType : Ty)
    (arguments : List CallArgument) (body : Stmt) : Outcome Step := do
  let callee ← liftChecked (prepare caller parameters arguments)
  let step ← CppLoop.runFuel fuel body callee
  liftChecked (finish caller resultType step)

theorem readonly_rejected (caller : State) (ty : Ty) (slot : Nat) (binding : Binding)
    (found : caller.bindings[slot]? = some binding) (readonly : binding.writable = false) :
    resolveArgument caller ⟨ty,true,true⟩ (.reference slot) = none := by
  simp [resolveArgument,found,readonly]

theorem readonly_allowed (caller : State) (ty : Ty) (slot : Nat) (binding : Binding)
    (found : caller.bindings[slot]? = some binding) (value : Int)
    (cell : caller.memory[binding.address]? = some ⟨ty,value⟩) (valid : ty.valid value = true) :
    resolveArgument caller ⟨ty,true,false⟩ (.reference slot) = some (.reference binding.address,1) := by
  simp [resolveArgument,found,cell,valid]

theorem reference_resolves (caller : State) (ty : Ty) (slot : Nat) (binding : Binding)
    (found : caller.bindings[slot]? = some binding) (writable : binding.writable = true) (value : Int)
    (cell : caller.memory[binding.address]? = some ⟨ty,value⟩) (valid : ty.valid value = true) :
    resolveArgument caller ⟨ty,true,true⟩ (.reference slot) = some (.reference binding.address,1) := by
  simp [resolveArgument,found,writable,cell,valid]

theorem missing_reference_rejected (caller : State) (parameter : Parameter) (slot : Nat)
    (missing : caller.bindings[slot]? = none) :
    resolveArgument caller parameter (.reference slot) = none := by
  cases h : parameter.reference <;> simp [resolveArgument,h,missing]

theorem temporary_reference_rejected (caller : State) (ty : Ty) (writable : Bool) (e : Expr) :
    resolveArgument caller ⟨ty,true,writable⟩ (.value e) = none := rfl

theorem resolution_work (caller : State) (parameter : Parameter) (argument : CallArgument)
    (resolved : Argument) (work : Nat)
    (success : resolveArgument caller parameter argument = some (resolved,work)) :
    work = argument.nodes := by
  cases argument with
  | reference slot =>
      cases hr : parameter.reference <;> simp [resolveArgument,hr] at success
      cases found : caller.bindings[slot]? with
      | none => simp [found] at success
      | some binding =>
          cases cell : caller.memory[binding.address]? with
          | none => simp [found,cell] at success
          | some value =>
              simp [found,cell] at success
              rcases success with ⟨_,_,_,rfl⟩
              rfl
  | value e =>
      cases hr : parameter.reference <;> simp [resolveArgument,hr] at success
      cases result : caller.evaluate e with
      | none => simp [result] at success
      | some value =>
          simp [result] at success
          rcases success with ⟨_,workEq⟩
          rw [← workEq]
          cases env : caller.environment with
          | none => simp [State.evaluate,env] at result
          | some values =>
              simp only [State.evaluate,env] at result
              exact Expr.eval_work e values value result

theorem finish_result (caller callee : State) (ty : Ty) (value : Int)
    (valid : ty.valid value = true) (length : caller.memory.length ≤ callee.memory.length) :
    finish caller ty ⟨callee,some value,false⟩ = some
      ⟨({caller with
        memory := callee.memory.take caller.memory.length ++ [⟨ty,value⟩]
        bindings := caller.bindings ++ [⟨caller.memory.length,false⟩]
        work := callee.work+1
        peak := max caller.peak callee.peak} : State).observe 0,none,false⟩ := by
  simp [finish,valid,Nat.not_lt_of_ge length]

theorem finish_preserves_bindings (caller : State) (ty : Ty) (step result : Step)
    (success : finish caller ty step = some result) :
    result.state.bindings.take caller.bindings.length = caller.bindings ∧
    result.state.memory.take caller.memory.length = step.state.memory.take caller.memory.length ∧
    result.state.memory.length = caller.memory.length+1 ∧
    result.state.work = step.state.work+1 ∧
    result.state.baseMemory = caller.baseMemory ∧
    result.returned = none ∧ result.breaking = false := by
  cases step with
  | mk callee returned breaking =>
      cases breaking with
      | true => simp [finish] at success
      | false =>
          cases returned with
          | none => simp [finish] at success
          | some value =>
              by_cases valid : ty.valid value = true
              · by_cases length : caller.memory.length ≤ callee.memory.length
                · rw [finish_result caller callee ty value valid length] at success
                  cases success
                  simp [State.observe,List.length_take,Nat.min_eq_left length]
                · simp [finish,Nat.lt_of_not_ge length] at success
              · simp [finish,valid] at success

theorem run_composed (caller callee : State) (parameters : List Parameter) (resultType : Ty)
    (arguments : List CallArgument) (body : Stmt) (step : Step)
    (prepared : prepare caller parameters arguments = some callee)
    (completed : body.run callee = some step) :
    run caller parameters resultType arguments body = finish caller resultType step := by
  simp [run,prepared,completed]

theorem fuel_composed (fuel : Nat) (caller callee : State) (parameters : List Parameter) (resultType : Ty)
    (arguments : List CallArgument) (body : Stmt) (step : Step)
    (prepared : prepare caller parameters arguments = some callee)
    (completed : CppLoop.runFuel fuel body callee = .finished step) :
    runFuel fuel caller parameters resultType arguments body = liftChecked (finish caller resultType step) := by
  simp [runFuel,prepared,completed,liftChecked,bind,Outcome.bind]

theorem resolution_arguments (caller : State) (parameters : List Parameter)
    (arguments : List CallArgument) (resolved : List Argument) (work : Nat)
    (success : resolveArguments caller parameters arguments = some (resolved,work)) :
    parameters.length = arguments.length ∧ resolved.length = parameters.length ∧
    work = (arguments.map CallArgument.nodes).sum := by
  induction parameters generalizing arguments resolved work with
  | nil =>
      cases arguments <;> simp [resolveArguments] at success
      rcases success with ⟨rfl,rfl⟩; simp
  | cons p ps ih =>
      cases arguments with
      | nil => simp [resolveArguments] at success
      | cons a args =>
          cases first : resolveArgument caller p a with
          | none => simp [resolveArguments,first] at success
          | some head =>
              rcases head with ⟨argument,argumentWork⟩
              cases rest : resolveArguments caller ps args with
              | none => simp [resolveArguments,first,rest] at success
              | some tail =>
                  rcases tail with ⟨others,restWork⟩
                  simp [resolveArguments,first,rest] at success
                  rcases success with ⟨rfl,rfl⟩
                  obtain ⟨lengths,count,work⟩ := ih args others restWork rest
                  simp [lengths,count,work,resolution_work caller p a argument argumentWork first]

theorem bind_argument_frame (s : State) (p : Parameter) (a : Argument) (result : State)
    (success : bindArgument s p a = some result) :
    result.memory.take s.memory.length = s.memory ∧
    s.memory.length ≤ result.memory.length ∧ result.memory.length ≤ s.memory.length+1 ∧
    result.bindings.length = s.bindings.length+1 ∧
    result.work = s.work ∧ result.baseMemory = s.baseMemory := by
  cases a with
  | value v =>
      cases reference : p.reference <;> cases valid : p.type.valid v <;>
        simp [bindArgument,reference,valid] at success
      cases success
      simp [State.observe]
  | reference address =>
      cases cell : s.memory[address]? with
      | none => simp [bindArgument,cell] at success
      | some found =>
          simp [bindArgument,cell] at success
          rcases success with ⟨_,_,_,success⟩
          simp [State.observe]

theorem bind_arguments_frame (s : State) (parameters : List Parameter)
    (arguments : List Argument) (result : State)
    (success : bindArguments s parameters arguments = some result) :
    result.memory.take s.memory.length = s.memory ∧
    s.memory.length ≤ result.memory.length ∧ result.memory.length ≤ s.memory.length+parameters.length ∧
    result.bindings.length = s.bindings.length+parameters.length ∧
    result.work = s.work ∧ result.baseMemory = s.baseMemory := by
  induction parameters generalizing s arguments result with
  | nil =>
      cases arguments <;> simp [bindArguments] at success
      cases success; simp
  | cons p ps ih =>
      cases arguments with
      | nil => simp [bindArguments] at success
      | cons a args =>
          cases first : bindArgument s p a with
          | none => simp [bindArguments,first] at success
          | some next =>
              have recurse : bindArguments next ps args = some result := by
                simpa [bindArguments,first] using success
              obtain ⟨memoryPrefix,low,high,count,work,base⟩ := ih next args result recurse
              obtain ⟨onePrefix,oneLow,oneHigh,oneCount,oneWork,oneBase⟩ :=
                bind_argument_frame s p a next first
              refine ⟨?_,by omega,by simp only [List.length_cons]; omega,
                by simp only [List.length_cons]; omega,work.trans oneWork,base.trans oneBase⟩
              have taken := congrArg (fun cells : List Cell => cells.take s.memory.length) memoryPrefix
              simpa only [List.take_take,Nat.min_eq_left oneLow,onePrefix] using taken

theorem prepare_frame (caller : State) (parameters : List Parameter) (arguments : List CallArgument)
    (callee : State) (success : prepare caller parameters arguments = some callee) :
    callee.memory.take caller.memory.length = caller.memory ∧
    caller.memory.length+caller.bindings.length ≤ callee.memory.length ∧
    callee.memory.length ≤ caller.memory.length+caller.bindings.length+parameters.length ∧
    callee.bindings.length = parameters.length ∧ callee.baseMemory = caller.baseMemory ∧
    parameters.length = arguments.length ∧
    callee.work = caller.work+1+(arguments.map CallArgument.nodes).sum+parameters.length := by
  cases resolution : resolveArguments caller parameters arguments with
  | none => simp [prepare,resolution] at success
  | some resolved =>
      rcases resolved with ⟨values,argumentWork⟩
      let initial : State := ({caller with
        memory := caller.memory ++ List.replicate caller.bindings.length ⟨⟨1,false,true⟩,0⟩
        bindings := [],work := caller.work+1+argumentWork+parameters.length
        peak := argumentPeak caller arguments} : State).observe 0
      have bound : bindArguments initial parameters values = some callee := by
        simpa [prepare,resolution,initial] using success
      obtain ⟨memoryPrefix,low,high,count,work,base⟩ := bind_arguments_frame initial parameters values callee bound
      obtain ⟨lengths,_,argumentWorkEq⟩ := resolution_arguments caller parameters arguments values argumentWork resolution
      refine ⟨?_,?_,?_,?_,?_,lengths,?_⟩
      · have initialLength : caller.memory.length ≤ initial.memory.length := by simp [initial,State.observe]
        have taken := congrArg (fun cells : List Cell => cells.take caller.memory.length) memoryPrefix
        simp only [List.take_take,Nat.min_eq_left initialLength] at taken
        simpa [initial,State.observe] using taken
      · simpa [initial,State.observe] using low
      · simpa [initial,State.observe] using high
      · simpa [initial,State.observe] using count
      · simpa [initial,State.observe] using base
      · simpa [initial,State.observe,argumentWorkEq] using work

theorem fuel_success_mono (fuel extra : Nat) (caller : State) (parameters : List Parameter)
    (ty : Ty) (arguments : List CallArgument) (body : Stmt) (result : Step)
    (success : runFuel fuel caller parameters ty arguments body = .finished result) :
    runFuel (fuel+extra) caller parameters ty arguments body = .finished result := by
  cases prepared : prepare caller parameters arguments with
  | none => simp [runFuel,prepared,liftChecked,bind,Outcome.bind] at success
  | some callee =>
      cases completed : CppLoop.runFuel fuel body callee with
      | fault => simp [runFuel,prepared,completed,liftChecked,bind,Outcome.bind] at success
      | exhausted => simp [runFuel,prepared,completed,liftChecked,bind,Outcome.bind] at success
      | finished step =>
          have larger := CppLoop.runFuel_success_mono fuel extra body callee step completed
          simpa [runFuel,prepared,completed,larger,liftChecked,bind,Outcome.bind] using success

theorem reference_address_bound (caller : State) (parameter : Parameter) (slot address work : Nat)
    (success : resolveArgument caller parameter (.reference slot) = some (.reference address,work)) :
    address < caller.memory.length := by
  cases reference : parameter.reference <;> simp [resolveArgument,reference] at success
  cases found : caller.bindings[slot]? with
  | none => simp [found] at success
  | some binding =>
      cases cell : caller.memory[binding.address]? with
      | none => simp [found,cell] at success
      | some value =>
          simp [found,cell] at success
          rcases success with ⟨_,_,addressEq,_⟩
          have bound := (List.getElem?_eq_some_iff.mp cell).1
          omega

end Proofs.CppReferenceInvoke
