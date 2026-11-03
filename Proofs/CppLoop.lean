import Proofs.CppState

namespace Proofs.CppLoop
open Proofs.CppScalar Proofs.CppState

inductive Outcome (α : Type) where
  | finished (value : α)
  | fault
  | exhausted
deriving DecidableEq, Repr

def Outcome.bind (result : Outcome α) (next : α → Outcome β) : Outcome β :=
  match result with
  | .finished value => next value
  | .fault => .fault
  | .exhausted => .exhausted

instance : Monad Outcome where
  pure := Outcome.finished
  bind := Outcome.bind

def liftChecked (result : Option α) : Outcome α :=
  match result with
  | some value => .finished value
  | none => .fault

def runFuel : Nat → Stmt → State → Outcome Step
  | 0, _, _ => .exhausted
  | fuel + 1, stmt, s =>
    match stmt with
    | .invoke parameters resultType arguments body => do
        let callee ← liftChecked (prepareInvoke s parameters arguments)
        let step ← runFuel fuel body callee
        liftChecked (finishInvoke s resultType step)
    | .whileLoop condition body => do
        let result ← liftChecked (s.evaluate condition)
        let next := ({ s with work := s.work + result.work + 1 }).observe condition.nodes
        if result.value == 0 then pure ⟨next, none, false⟩ else do
          let step ← runFuel fuel body next
          if step.returned.isSome then pure step
          else if step.breaking then pure { step with breaking := false }
          else runFuel fuel (.whileLoop condition body) step.state
    | .sequence first rest => do
        let step ← runFuel fuel first s
        if step.returned.isSome || step.breaking then pure step else runFuel fuel rest step.state
    | .breakLoop => pure ⟨{ s with work := s.work + 1 }, none, true⟩
    | .scope body => do
        let step ← runFuel fuel body s
        pure { step with state := { step.state with
          memory := step.state.memory.take s.memory.length
          bindings := step.state.bindings.take s.bindings.length } }
    | .branch condition yes no => do
        let result ← liftChecked (s.evaluate condition)
        let next := ({ s with work := s.work + result.work + 1 }).observe condition.nodes
        if result.value == 0 then runFuel fuel no next else runFuel fuel yes next
    | _ => liftChecked (stmt.run s)

structure LoopProgram where
  parameters : List Parameter
  resultType : Ty
  body : Stmt
deriving DecidableEq, Repr

def LoopProgram.callFuel (p : LoopProgram) (fuel : Nat) (memory : List Cell)
    (arguments : List Argument) : Outcome CallResult := do
  if !(arguments.all fun a => match a with
      | .value _ => true
      | .reference address => decide (address < memory.length)) then .fault else do
  let state ← liftChecked (bindArguments
    { memory := memory, bindings := [], baseMemory := memory.length } p.parameters arguments)
  let step ← runFuel fuel p.body state
  if step.breaking then .fault else do
  let value ← liftChecked step.returned
  if p.resultType.valid value then
    pure ⟨value, step.state.memory.take memory.length, step.state.work, step.state.peak⟩
  else .fault

-- Termination/success requires a witness, not merely a finite fuel limit.
def LoopProgram.Terminates (p : LoopProgram) (memory : List Cell) (args : List Argument) : Prop :=
  ∃ fuel result, p.callFuel fuel memory args = .finished result

-- A zero budget is an observation limit; it supplies no successful run.
theorem runFuel_zero (stmt : Stmt) (s : State) :
    runFuel 0 stmt s = .exhausted := rfl

theorem skip_succeeds (fuel : Nat) (s : State) :
    runFuel (fuel + 1) .skip s = .finished ⟨s, none, false⟩ := rfl

theorem break_succeeds (fuel : Nat) (s : State) :
    runFuel (fuel + 1) .breakLoop s =
      .finished ⟨{ s with work := s.work + 1 }, none, true⟩ := rfl

theorem break_sequence_skips (fuel : Nat) (rest : Stmt) (s : State) :
    runFuel (fuel + 2) (.sequence .breakLoop rest) s =
      .finished ⟨{ s with work := s.work + 1 }, none, true⟩ := rfl

theorem while_break_exits (fuel : Nat) (condition : Expr) (s : State) (result : Result)
    (he : s.evaluate condition = some result) (hn : result.value ≠ 0) :
    runFuel (fuel + 2) (.whileLoop condition .breakLoop) s =
      .finished ⟨{ (({ s with work := s.work + result.work + 1 }).observe condition.nodes)
        with work := s.work + result.work + 1 + 1 }, none, false⟩ := by
  simp [runFuel, he, hn, liftChecked, bind, pure, Outcome.bind, State.observe]

theorem runFuel_success_mono (fuel extra : Nat) (stmt : Stmt) (s : State) (step : Step)
    (h : runFuel fuel stmt s = .finished step) :
    runFuel (fuel + extra) stmt s = .finished step := by
  induction fuel generalizing stmt s step with
  | zero => simp [runFuel] at h
  | succ fuel ih =>
      have hs : fuel + 1 + extra = (fuel + extra) + 1 := by omega
      rw [hs]
      cases stmt with
      | skip => simpa [runFuel] using h
      | declare ty writable e => simpa [runFuel] using h
      | assign slot e => simpa [runFuel] using h
      | swap left right => simpa [runFuel] using h
      | ret e => simpa [runFuel] using h
      | breakLoop => simpa [runFuel] using h
      | check e => simpa [runFuel] using h
      | invoke parameters resultType arguments body =>
          cases hp : prepareInvoke s parameters arguments with
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

theorem LoopProgram.callFuel_success_mono (p : LoopProgram) (fuel extra : Nat)
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

theorem runFuel_success_unique (fuel₁ fuel₂ : Nat) (stmt : Stmt) (s : State)
    (step₁ step₂ : Step)
    (h₁ : runFuel fuel₁ stmt s = .finished step₁)
    (h₂ : runFuel fuel₂ stmt s = .finished step₂) : step₁ = step₂ := by
  have first := runFuel_success_mono fuel₁ fuel₂ stmt s step₁ h₁
  have second := runFuel_success_mono fuel₂ fuel₁ stmt s step₂ h₂
  rw [Nat.add_comm fuel₂ fuel₁, first] at second
  exact Outcome.finished.inj second

theorem LoopProgram.callFuel_success_unique (p : LoopProgram) (fuel₁ fuel₂ : Nat)
    (memory : List Cell) (args : List Argument) (result₁ result₂ : CallResult)
    (h₁ : p.callFuel fuel₁ memory args = .finished result₁)
    (h₂ : p.callFuel fuel₂ memory args = .finished result₂) : result₁ = result₂ := by
  have first := p.callFuel_success_mono fuel₁ fuel₂ memory args result₁ h₁
  have second := p.callFuel_success_mono fuel₂ fuel₁ memory args result₂ h₂
  rw [Nat.add_comm fuel₂ fuel₁, first] at second
  exact Outcome.finished.inj second

end Proofs.CppLoop
