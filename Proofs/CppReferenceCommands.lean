import Proofs.CppReferenceInvoke

namespace Proofs.CppReferenceCommands
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop Proofs.CppReferenceInvoke

-- An extension layer reuses the existing scalar statements and expression
-- semantics. Calls carry source-generated bodies, including nested calls.
inductive Command where
  | legacy (statement : Stmt)
  | invoke (parameters : List Parameter) (resultType : Ty) (arguments : List CallArgument) (body : Command)
  | sequence (first rest : Command)
  | scope (body : Command)
  | branch (condition : Expr) (yes no : Command)
  | whileLoop (condition : Expr) (body : Command)
  deriving DecidableEq, Repr

def Command.run (s : State) : Command → Option Step
  | .legacy statement => statement.run s
  | .invoke parameters resultType arguments body => do
      let callee ← prepare s parameters arguments
      let step ← body.run callee
      finish s resultType step
  | .sequence first rest => do
      let step ← first.run s
      if step.returned.isSome || step.breaking then some step else rest.run step.state
  | .scope body => do
      let step ← body.run s
      some {step with state := {step.state with
        memory := step.state.memory.take s.memory.length
        bindings := step.state.bindings.take s.bindings.length}}
  | .branch condition yes no => do
      let result ← s.evaluate condition
      let next := ({s with work := s.work+result.work+1}).observe condition.nodes
      if result.value == 0 then no.run next else yes.run next
  | .whileLoop _ _ => none

def runFuel : Nat → Command → State → Outcome Step
  | 0, _, _ => .exhausted
  | fuel+1, command, s =>
      match command with
      | .legacy statement => CppLoop.runFuel (fuel+1) statement s
      | .invoke parameters resultType arguments body => do
          let callee ← liftChecked (prepare s parameters arguments)
          let step ← runFuel fuel body callee
          liftChecked (finish s resultType step)
      | .sequence first rest => do
          let step ← runFuel fuel first s
          if step.returned.isSome || step.breaking then pure step else runFuel fuel rest step.state
      | .scope body => do
          let step ← runFuel fuel body s
          pure {step with state := {step.state with
            memory := step.state.memory.take s.memory.length
            bindings := step.state.bindings.take s.bindings.length}}
      | .branch condition yes no => do
          let result ← liftChecked (s.evaluate condition)
          let next := ({s with work := s.work+result.work+1}).observe condition.nodes
          if result.value == 0 then runFuel fuel no next else runFuel fuel yes next
      | .whileLoop condition body => do
          let result ← liftChecked (s.evaluate condition)
          let next := ({s with work := s.work+result.work+1}).observe condition.nodes
          if result.value == 0 then pure ⟨next,none,false⟩ else do
            let step ← runFuel fuel body next
            if step.returned.isSome then pure step
            else if step.breaking then pure {step with breaking := false}
            else runFuel fuel (.whileLoop condition body) step.state

structure Program where
  parameters : List Parameter
  resultType : Ty
  body : Command
  deriving DecidableEq, Repr

def Program.call (program : Program) (memory : List Cell) (arguments : List Argument) : Option CallResult := do
  if !(arguments.all fun a => match a with
    | .value _ => true | .reference address => decide (address < memory.length)) then none else do
    let initial ← bindArguments {memory := memory,bindings := [],baseMemory := memory.length} program.parameters arguments
    let step ← program.body.run initial
    if step.breaking then none else do
      let value ← step.returned
      if program.resultType.valid value then
        some ⟨value,step.state.memory.take memory.length,step.state.work,step.state.peak⟩
      else none

def Program.callFuel (program : Program) (fuel : Nat) (memory : List Cell)
    (arguments : List Argument) : Outcome CallResult := do
  if !(arguments.all fun a => match a with
    | .value _ => true | .reference address => decide (address < memory.length)) then .fault else do
    let initial ← liftChecked (bindArguments {memory := memory,bindings := [],baseMemory := memory.length} program.parameters arguments)
    let step ← runFuel fuel program.body initial
    if step.breaking then .fault else do
      let value ← liftChecked step.returned
      if program.resultType.valid value then
        pure ⟨value,step.state.memory.take memory.length,step.state.work,step.state.peak⟩
      else .fault

theorem legacy_run (stmt : Stmt) (s : State) : (Command.legacy stmt).run s = stmt.run s := rfl

theorem legacy_fuel (fuel : Nat) (stmt : Stmt) (s : State) :
    runFuel fuel (.legacy stmt) s = CppLoop.runFuel fuel stmt s := by cases fuel <;> rfl

theorem invoke_composed (s callee : State) (parameters : List Parameter) (ty : Ty)
    (arguments : List CallArgument) (body : Command) (step : Step)
    (prepared : prepare s parameters arguments = some callee) (completed : body.run callee = some step) :
    (Command.invoke parameters ty arguments body).run s = finish s ty step := by
  simp [Command.run,prepared,completed]

theorem invoke_fuel_composed (fuel : Nat) (s callee : State) (parameters : List Parameter) (ty : Ty)
    (arguments : List CallArgument) (body : Command) (step : Step)
    (prepared : prepare s parameters arguments = some callee)
    (completed : runFuel fuel body callee = .finished step) :
    runFuel (fuel+1) (.invoke parameters ty arguments body) s = liftChecked (finish s ty step) := by
  simp [runFuel,prepared,completed,liftChecked,bind,Outcome.bind]

-- This is the structural form emitted for a call-bearing while/for test.
-- Its scope drops condition result slots, preserving updated outer cells.
def conditionIteration (setup : Command) (condition : Expr) (body : Command) : Command :=
  .scope (.sequence setup (.branch condition body (.legacy .breakLoop)))

def conditionState (s : State) (condition : Expr) (result : Result) : State :=
  ({s with work := s.work + result.work + 1}).observe condition.nodes

theorem condition_false_breaks (fuel : Nat) (s tested : State)
    (setup body : Command) (condition : Expr) (result : Result)
    (prepared : runFuel (fuel+2) setup s = .finished ⟨tested,none,false⟩)
    (evaluated : tested.evaluate condition = some result) (isFalse : result.value = 0) :
    runFuel (fuel+4) (conditionIteration setup condition body) s =
      .finished ⟨{conditionState tested condition result with
        memory := tested.memory.take s.memory.length,
        bindings := tested.bindings.take s.bindings.length,
        work := (conditionState tested condition result).work+1},none,true⟩ := by
  rw [conditionIteration,runFuel,runFuel,prepared]
  simp only [bind,Outcome.bind,Option.isSome_none,Bool.false_or,Bool.false_eq_true,ite_false]
  rw [runFuel,evaluated]
  simp only [liftChecked,bind,Outcome.bind,isFalse]
  rw [runFuel,CppLoop.runFuel]
  simp [pure,conditionState,State.observe]

theorem condition_true_runs_body (fuel : Nat) (s tested : State)
    (setup body : Command) (condition : Expr) (result : Result) (step : Step)
    (prepared : runFuel (fuel+2) setup s = .finished ⟨tested,none,false⟩)
    (evaluated : tested.evaluate condition = some result) (isTrue : result.value ≠ 0)
    (completed : runFuel (fuel+1) body (conditionState tested condition result) = .finished step) :
    runFuel (fuel+4) (conditionIteration setup condition body) s =
      .finished {step with state := {step.state with
        memory := step.state.memory.take s.memory.length,
        bindings := step.state.bindings.take s.bindings.length}} := by
  rw [conditionIteration,runFuel,runFuel,prepared]
  simp only [bind,Outcome.bind,Option.isSome_none,Bool.false_or,Bool.false_eq_true,ite_false]
  rw [runFuel,evaluated]
  simp only [liftChecked,bind,Outcome.bind,beq_iff_eq,isTrue,ite_false]
  change (runFuel (fuel+1) body (conditionState tested condition result) >>= _) = _
  rw [completed]
  rfl

theorem condition_call_fault (fuel : Nat) (s : State)
    (setup body : Command) (condition : Expr)
    (failed : runFuel (fuel+2) setup s = .fault) :
    runFuel (fuel+4) (conditionIteration setup condition body) s = .fault := by
  rw [conditionIteration,runFuel,runFuel,failed]
  rfl

theorem runFuel_success_mono (fuel extra : Nat) (stmt : Command) (s : State) (step : Step)
    (h : runFuel fuel stmt s = .finished step) :
    runFuel (fuel + extra) stmt s = .finished step := by
  induction fuel generalizing stmt s step with
  | zero => simp [runFuel] at h
  | succ fuel ih =>
      have hs : fuel + 1 + extra = (fuel + extra) + 1 := by omega
      rw [hs]
      cases stmt with
      | legacy statement =>
          have completed : CppLoop.runFuel (fuel+1) statement s = .finished step := by
            simpa [runFuel] using h
          have larger := CppLoop.runFuel_success_mono (fuel+1) extra statement s step completed
          simpa [runFuel,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using larger
      | invoke parameters resultType arguments body =>
          cases hp : prepare s parameters arguments with
          | none => simp [runFuel,hp,liftChecked,bind,Outcome.bind] at h
          | some callee =>
              cases hb : runFuel fuel body callee with
              | fault => simp [runFuel,hp,hb,liftChecked,bind,Outcome.bind] at h
              | exhausted => simp [runFuel,hp,hb,liftChecked,bind,Outcome.bind] at h
              | finished middle =>
                  have hi := ih body callee middle hb
                  simpa [runFuel,hp,hb,hi,liftChecked,bind,Outcome.bind] using h
      | scope body =>
          cases hb : runFuel fuel body s with
          | fault => simp [runFuel, hb, bind, Outcome.bind] at h
          | exhausted => simp [runFuel, hb, bind, Outcome.bind] at h
          | finished middle =>
              have hi := ih body s middle hb
              simpa [runFuel, hb, hi, bind, pure, Outcome.bind] using h
      | branch condition yes no =>
          cases he : s.evaluate condition with
          | none => simp [runFuel, he, liftChecked, bind, Outcome.bind] at h
          | some result =>
              let next := ({ s with work := s.work + result.work + 1 }).observe condition.nodes
              by_cases hz : result.value = 0
              · have hb : runFuel fuel no next = .finished step := by
                  simpa [runFuel, he, liftChecked, bind, Outcome.bind, hz, next] using h
                have hi := ih no next step hb
                simpa [runFuel, he, liftChecked, bind, Outcome.bind, hz, next] using hi
              · have hb : runFuel fuel yes next = .finished step := by
                  simpa [runFuel, he, liftChecked, bind, Outcome.bind, hz, next] using h
                have hi := ih yes next step hb
                simpa [runFuel, he, liftChecked, bind, Outcome.bind, hz, next] using hi
      | sequence first rest =>
          cases hb : runFuel fuel first s with
          | fault => simp [runFuel, hb, bind, Outcome.bind] at h
          | exhausted => simp [runFuel, hb, bind, Outcome.bind] at h
          | finished middle =>
              have hi := ih first s middle hb
              by_cases hr : (middle.returned.isSome || middle.breaking) = true
              · simpa [runFuel, hb, hi, bind, pure, Outcome.bind, hr] using h
              · have ht : runFuel fuel rest middle.state = .finished step := by
                  simpa [runFuel, hb, bind, Outcome.bind, hr] using h
                have hj := ih rest middle.state step ht
                simpa [runFuel, hb, hi, bind, Outcome.bind, hr] using hj
      | whileLoop condition body =>
          cases he : s.evaluate condition with
          | none => simp [runFuel, he, liftChecked, bind, Outcome.bind] at h
          | some result =>
              let next := ({ s with work := s.work + result.work + 1 }).observe condition.nodes
              by_cases hz : result.value = 0
              · simpa [runFuel, he, liftChecked, bind, pure, Outcome.bind, hz, next] using h
              · cases hb : runFuel fuel body next with
                | fault => simp [runFuel, he, hb, liftChecked, bind, Outcome.bind, hz, next] at h
                | exhausted => simp [runFuel, he, hb, liftChecked, bind, Outcome.bind, hz, next] at h
                | finished middle =>
                    have hi := ih body next middle hb
                    by_cases hr : middle.returned.isSome = true
                    · simpa [runFuel, he, hb, hi, liftChecked, bind, pure, Outcome.bind, hz, hr, next] using h
                    · by_cases hbreak : middle.breaking = true
                      · simpa [runFuel, he, hb, hi, liftChecked, bind, pure, Outcome.bind, hz, hr, hbreak, next] using h
                      · have ht : runFuel fuel (.whileLoop condition body) middle.state = .finished step := by
                          simpa [runFuel, he, hb, liftChecked, bind, Outcome.bind, hz, hr, hbreak, next] using h
                        have hj := ih (.whileLoop condition body) middle.state step ht
                        simpa [runFuel, he, hb, hi, liftChecked, bind, Outcome.bind, hz, hr, hbreak, next] using hj

theorem runFuel_success_unique (fuelA fuelB : Nat) (command : Command) (s : State)
    (resultA resultB : Step)
    (first : runFuel fuelA command s = .finished resultA)
    (second : runFuel fuelB command s = .finished resultB) : resultA = resultB := by
  have a := runFuel_success_mono fuelA fuelB command s resultA first
  have b := runFuel_success_mono fuelB fuelA command s resultB second
  rw [Nat.add_comm fuelB fuelA,a] at b
  exact Outcome.finished.inj b

theorem Program.callFuel_success_mono (p : Program) (fuel extra : Nat)
    (memory : List Cell) (args : List Argument) (result : CallResult)
    (h : p.callFuel fuel memory args = .finished result) :
    p.callFuel (fuel + extra) memory args = .finished result := by
  cases hs : bindArguments
      { memory := memory, bindings := [], baseMemory := memory.length } p.parameters args with
  | none => simp [callFuel, hs, liftChecked, bind, Outcome.bind] at h
  | some state =>
      cases hr : runFuel fuel p.body state with
      | fault => simp [callFuel, hs, hr, liftChecked, bind, Outcome.bind] at h
      | exhausted =>
          have he := h
          simp [callFuel, hs, hr, liftChecked, bind, Outcome.bind] at he
          split at he <;> contradiction
      | finished step =>
          have hm := runFuel_success_mono fuel extra p.body state step hr
          simpa [callFuel, hs, hr, hm, liftChecked, bind, pure, Outcome.bind] using h


end Proofs.CppReferenceCommands
