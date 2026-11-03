import Proofs.CppScalar

namespace Proofs.CppState
open Proofs.CppScalar

structure Cell where
  type : Ty
  value : Int
deriving DecidableEq, Repr
structure Binding where
  address : Nat
  writable : Bool
deriving DecidableEq, Repr
structure State where
  memory : List Cell
  bindings : List Binding
  work : Nat := 0
  baseMemory : Nat := 0
  peak : Nat := 0
deriving DecidableEq, Repr

-- Abstract live scalar cells/bindings, excluding caller-owned cells, plus a
-- conservative bound on scalar expression temporaries. Not Lean's heap usage.
def State.observe (s : State) (temporaries : Nat) : State :=
  { s with peak := max s.peak (s.memory.length - s.baseMemory + s.bindings.length + temporaries) }

def State.environment (s : State) : Option (List Int) :=
  s.bindings.mapM fun b => do
    let cell ← s.memory[b.address]?
    if cell.type.valid cell.value then some cell.value else none

def State.evaluate (s : State) (e : Expr) : Option Result := do
  let env ← s.environment
  e.eval env

-- Internal by-value calls have no caller aliases or global-state access.
-- Reserved cells account for the caller bindings that remain live while the
-- callee uses its own binding environment.
def bindValueResults : State → List (Ty × Bool) → List Result → Option State
  | s, [], [] => some s
  | s, p :: ps, value :: values => do
      if !p.1.valid value.value then none else do
        let next : State := {s with
          memory := s.memory ++ [⟨p.1,value.value⟩]
          bindings := s.bindings ++ [⟨s.memory.length,p.2⟩]
          work := s.work + value.work + 1}
        bindValueResults (next.observe 0) ps values
  | _, _, _ => none

def prepareInvoke (s : State) (parameters : List (Ty × Bool)) (arguments : List Expr) : Option State := do
  let values ← arguments.mapM s.evaluate
  let argumentPeak := arguments.foldl
    (fun peak e => max peak ((s.observe (arguments.length+e.nodes)).peak)) s.peak
  let initial : State := {s with
    memory := s.memory ++ List.replicate s.bindings.length ⟨⟨1,false,true⟩,0⟩
    bindings := [], work := s.work+1, peak := argumentPeak}
  bindValueResults (initial.observe 0) parameters values

inductive Stmt where
  | skip
  | declare (type : Ty) (writable : Bool) (value : Expr)
  | assign (slot : Nat) (value : Expr)
  | swap (left right : Nat)
  | ret (value : Expr)
  | branch (condition : Expr) (yes no : Stmt)
  | sequence (first rest : Stmt)
  | scope (body : Stmt)
  | whileLoop (condition : Expr) (body : Stmt)
  | breakLoop
  | check (condition : Expr)
  | invoke (parameters : List (Ty × Bool)) (resultType : Ty) (arguments : List Expr) (body : Stmt)
deriving DecidableEq, Repr

structure Step where
  state : State
  returned : Option Int := none
  breaking : Bool := false
deriving DecidableEq, Repr

def finishInvoke (caller : State) (resultType : Ty) (step : Step) : Option Step := do
  if step.breaking then none else do
    let value ← step.returned
    if !resultType.valid value then none else do
      let next : State := {caller with
        memory := caller.memory ++ [⟨resultType,value⟩]
        bindings := caller.bindings ++ [⟨caller.memory.length,false⟩]
        work := step.state.work+1, peak := max caller.peak step.state.peak}
      some ⟨next.observe 0,none,false⟩

def Stmt.run (s : State) : Stmt → Option Step
  | .skip => some ⟨s, none, false⟩
  | .invoke parameters resultType arguments body => do
      let callee ← prepareInvoke s parameters arguments
      let step ← body.run callee
      finishInvoke s resultType step
  | .check e => do
      let result ← s.evaluate e
      if result.value == 0 then none else
        some ⟨({s with work := s.work + result.work + 1}).observe e.nodes, none, false⟩
  | .declare ty writable e => do
      let result ← s.evaluate e
      let value ← ty.convert result.value
      let next : State := { s with
        memory := s.memory ++ [⟨ty, value⟩]
        bindings := s.bindings ++ [⟨s.memory.length, writable⟩]
        work := s.work + result.work + 1 }
      some ⟨next.observe e.nodes, none, false⟩
  | .assign slot e => do
      let binding ← s.bindings[slot]?
      if !binding.writable then none else do
        let cell ← s.memory[binding.address]?
        let result ← s.evaluate e
        let value ← cell.type.convert result.value
        let next : State := { s with
          memory := s.memory.set binding.address ⟨cell.type, value⟩
          work := s.work + result.work + 1 }
        some ⟨next.observe e.nodes, none, false⟩
  | .swap left right => do
      let lhs ← s.bindings[left]?
      let rhs ← s.bindings[right]?
      if !lhs.writable || !rhs.writable then none else do
        let a ← s.memory[lhs.address]?
        let b ← s.memory[rhs.address]?
        if a.type != b.type || !a.type.valid a.value || !b.type.valid b.value then none else do
        let next : State := { s with
          memory := (s.memory.set lhs.address b).set rhs.address a
          work := s.work + 6 }
        -- One scalar temporary and two callee reference bindings.
        some ⟨next.observe 3, none, false⟩
  | .ret e => do
      let result ← s.evaluate e
      some ⟨({ s with work := s.work + result.work + 1 }).observe e.nodes, some result.value, false⟩
  | .branch e yes no => do
      let condition ← s.evaluate e
      let next := ({ s with work := s.work + condition.work + 1 }).observe e.nodes
      if condition.value == 0 then no.run next else yes.run next
  | .sequence first rest => do
      let step ← first.run s
      if step.returned.isSome then some step else rest.run step.state
  | .scope body => do
      let step ← body.run s
      some { step with state := { step.state with
        memory := step.state.memory.take s.memory.length
        bindings := step.state.bindings.take s.bindings.length } }
  -- Unbounded loops are handled by CppLoop's explicit fuel outcome, never by
  -- an arbitrary implicit limit in the straight-line evaluator.
  | .whileLoop _ _ | .breakLoop => none

-- Checks are executable guards: a false predicate yields failure, never a proof assumption.
theorem check_succeeds (s : State) (e : Expr) (result : Result)
    (evaluated : s.evaluate e = some result) (nonzero : result.value ≠ 0) :
    (Stmt.check e).run s =
      some ⟨({s with work := s.work+result.work+1}).observe e.nodes,none,false⟩ := by
  simp [Stmt.run,evaluated,nonzero]

theorem check_fails (s : State) (e : Expr) (result : Result)
    (evaluated : s.evaluate e = some result) (zero : result.value = 0) :
    (Stmt.check e).run s = none := by simp [Stmt.run,evaluated,zero]

structure Parameter where
  type : Ty
  reference : Bool
  writable : Bool
deriving DecidableEq, Repr
inductive Argument where
  | value (value : Int)
  | reference (address : Nat)
deriving DecidableEq, Repr

def bindArgument (s : State) (p : Parameter) (a : Argument) : Option State := do
  match a with
  | .value value =>
      if p.reference || !p.type.valid value then none else do
      let next : State := { s with
        memory := s.memory ++ [⟨p.type, value⟩]
        bindings := s.bindings ++ [⟨s.memory.length, p.writable⟩] }
      some (next.observe 0)
  | .reference address =>
      let cell ← s.memory[address]?
      if !p.reference || cell.type != p.type || !p.type.valid cell.value then none else
      some (({ s with bindings := s.bindings ++ [⟨address, p.writable⟩] } : State).observe 0)

def bindArguments (s : State) : List Parameter → List Argument → Option State
  | [], [] => some s
  | p :: ps, a :: args => do
      let next ← bindArgument s p a
      bindArguments next ps args
  | _, _ => none

structure StateProgram where
  parameters : List Parameter
  resultType : Ty
  body : Stmt
deriving DecidableEq, Repr
structure CallResult where
  value : Int
  memory : List Cell
  work : Nat
  peak : Nat
deriving DecidableEq, Repr

def StateProgram.call (p : StateProgram) (memory : List Cell) (arguments : List Argument) : Option CallResult := do
  if !(arguments.all fun a => match a with
      | .value _ => true
      | .reference address => decide (address < memory.length)) then none else do
  let state ← bindArguments { memory := memory, bindings := [], baseMemory := memory.length } p.parameters arguments
  let step ← p.body.run state
  let value ← step.returned
  if p.resultType.valid value then
    some ⟨value, step.state.memory.take memory.length, step.state.work, step.state.peak⟩
  else none

theorem assign_preserves_storage (s : State) (slot : Nat) (e : Expr) (step : Step)
    (h : (Stmt.assign slot e).run s = some step) :
    step.state.memory.length = s.memory.length ∧ step.state.bindings = s.bindings := by
  cases hb : s.bindings[slot]? with
  | none => simp [Stmt.run, hb] at h
  | some binding =>
      by_cases hw : binding.writable = true
      · cases hc : s.memory[binding.address]? with
        | none => simp [Stmt.run, hb, hw, hc] at h
        | some cell =>
            cases he : s.evaluate e with
            | none => simp [Stmt.run, hb, he] at h
            | some result =>
                cases hv : cell.type.convert result.value with
                | none => simp [Stmt.run, hb, hw, hc, he, hv] at h
                | some value =>
                    simp [Stmt.run, hb, hw, hc, he, hv] at h
                    subst step
                    simp [State.observe]
      · simp [Stmt.run, hb, hw] at h

theorem swap_canonical (ty : Ty) (a b : Int) (tail : List Cell := [])
    (ha : ty.valid a = true) (hb : ty.valid b = true) :
    (Stmt.swap 0 1).run
      ⟨[⟨ty,a⟩,⟨ty,b⟩] ++ tail,[⟨0,true⟩,⟨1,true⟩],0,2+tail.length,0⟩ =
      some ⟨⟨[⟨ty,b⟩,⟨ty,a⟩] ++ tail,[⟨0,true⟩,⟨1,true⟩],6,2+tail.length,5⟩,none,false⟩ := by
  simp [Stmt.run, ha, hb, State.observe]
  omega

theorem swap_alias (ty : Ty) (a : Int) (tail : List Cell := [])
    (ha : ty.valid a = true) :
    (Stmt.swap 0 1).run
      ⟨⟨ty,a⟩::tail,[⟨0,true⟩,⟨0,true⟩],0,1+tail.length,0⟩ =
      some ⟨⟨⟨ty,a⟩::tail,[⟨0,true⟩,⟨0,true⟩],6,1+tail.length,5⟩,none,false⟩ := by
  simp [Stmt.run, ha, State.observe]
  omega

theorem swap_preserves_storage_and_work (s : State) (left right : Nat) (step : Step)
    (h : (Stmt.swap left right).run s = some step) :
    step.state.memory.length = s.memory.length ∧ step.state.bindings = s.bindings ∧
      step.state.work = s.work + 6 ∧ step.returned = none ∧ step.breaking = false := by
  cases hl : s.bindings[left]? with
  | none => simp [Stmt.run, hl] at h
  | some lhs =>
      cases hr : s.bindings[right]? with
      | none => simp [Stmt.run, hl, hr] at h
      | some rhs =>
          cases ha : s.memory[lhs.address]? with
          | none => simp [Stmt.run, hl, hr, ha] at h
          | some a =>
              cases hb : s.memory[rhs.address]? with
              | none => simp [Stmt.run, hl, hr, hb] at h
              | some b =>
                  simp [Stmt.run, hl, hr, ha, hb] at h
                  rcases h with ⟨_, _, he⟩
                  subst step
                  simp [State.observe]

end Proofs.CppState
