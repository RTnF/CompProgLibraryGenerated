import Proofs.CppScalarReturnFrame
import Proofs.CppMoveCallBindings
import Proofs.CppNestedStmt

namespace Proofs.CppScalarGetterCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
open Proofs.CppNestedEval Proofs.CppMoveContext Proofs.CppMoveCallBindings Proofs.CppMoveHeaders

theorem body_good (initial : NState) (expression : NExpr) (rest : Command) (value : Int)
    (scalar : expression.scalarOnly = true)
    (denotes : expression.denote (envOf initial) = some value) :
    ∃ callee, Proofs.CppNestedProgram.runFuel 2 (.sequence (.primitive (.ret expression)) rest) initial =
      .finished ⟨callee,some (.scalar value),false⟩ ∧
      Good initial callee (expression.nodes+1) expression.nodes := by
  obtain ⟨evaluated,eval,good⟩ := Proofs.CppNestedStmt.scalar_eval expression initial value scalar denotes
  have released : evaluated.release initial = evaluated := by
    simp [NState.release,← good.1.1]
  let callee := evaluated.charge 1 0
  have actual : Proofs.CppNestedProgram.runFuel 2 (.sequence (.primitive (.ret expression)) rest) initial =
      .finished ⟨callee,some (.scalar value),false⟩ := by
    simp [Proofs.CppNestedProgram.runFuel,NStmt.run,eval,liftChecked,released,callee,bind,Outcome.bind,pure]
  exact ⟨callee,actual,by simpa only [Nat.max_zero] using good.trans (Good.charge evaluated 1 0)⟩

theorem body_runs (initial : NState) (expression : NExpr) (rest : Command) (value : Int)
    (scalar : expression.scalarOnly = true)
    (denotes : expression.denote (envOf initial) = some value) :
    ∃ callee, Proofs.CppNestedProgram.runFuel 2 (.sequence (.primitive (.ret expression)) rest) initial =
      .finished ⟨callee,some (.scalar value),false⟩ ∧ Core initial callee ∧
      callee.work ≤ initial.work+expression.nodes+1 := by
  obtain ⟨callee,actual,good⟩ := body_good initial expression rest value scalar denotes
  refine ⟨callee,actual,good.1,?_⟩
  have cost := good.2.2.1
  simp only [NState.work,good.1.1]
  omega

def scalarBudget (caller : Context) (initial : NState) (nodes : Nat) : Nat :=
  max (max caller.scalars.peak initial.scalars.peak)
    (max (liveS initial+nodes) (scalarLive caller))
def heapBudget (initial : NState) : Nat :=
  max initial.frame.state.storage.peak (initial.frame.state.liveSpace-initial.frame.state.storage.baseSpace)
def totalBudget (caller : Context) (initial : NState) (nodes : Nat) : Nat :=
  max (max caller.peak initial.peak) (scalarBudget caller initial nodes+heapBudget initial)

structure Resources (caller : Context) (initial : NState) (out : Context) (nodes : Nat) : Prop where
  scalar : out.scalars.peak ≤ scalarBudget caller initial nodes
  heap : out.objects.heap.peak = heapBudget initial
  total : out.peak ≤ totalBudget caller initial nodes

-- Preparation and its memoryPrefix are explicit intermediate obligations, not a
-- successful method/body/finish assumption. They can be discharged by each
-- source receiver adapter; this lemma constructs actual body and finish.
theorem call_resources (program : NProgram) (caller prepared : Context) (initial : NState)
    (ty retType : Ty) (arguments : List NArgument) (expression : NExpr) (rest : Command) (value : Int)
    (body : program.body = .sequence (.primitive (.ret expression)) rest)
    (scalar : program.result = .scalar retType)
    (onlyScalar : expression.scalarOnly = true)
    (allowed : Proofs.CppNoResizeScope.Allowed program.body = true)
    (contexts : ∀ owner scope, (project caller ty).frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (covered : OwnsAll caller.objects.heap)
    (valid : (project caller ty).frame.state.wellFormed = true)
    (preparedRun : prepareArguments caller ty program.parameters arguments = some prepared)
    (compacted : compact (project prepared ty) = some initial)
    (memoryPrefix : initial.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory)
    (denotes : expression.denote (envOf initial) = some value)
    (valueValid : retType.valid value = true) :
    ∃ out, callFuel program 2 caller ty arguments = .finished (out,.scalar value) ∧
      out.scalars.memory = caller.scalars.memory ∧
      (∀ owner, (project out ty).frame.state.storage.lookup owner = initial.frame.state.storage.lookup owner) ∧
      work out ≤ initial.work+expression.nodes+2 ∧ Resources caller initial out expression.nodes := by
  obtain ⟨callee,ran,good⟩ := body_good initial expression rest value onlyScalar denotes
  have core := good.1
  have cost : callee.work ≤ initial.work+expression.nodes+1 := by
    have bound := good.2.2.1
    simp only [NState.work,core.1]
    omega
  rw [← body] at ran
  have memory : callee.scalars.memory = initial.scalars.memory := core.2.2.2.1
  have fits : caller.scalars.memory.length ≤ callee.scalars.memory.length := by
    have lengths := congrArg List.length memoryPrefix
    rw [List.length_take] at lengths
    rw [memory]
    omega
  have types : (callee.scalars.memory.take caller.scalars.memory.length).map Proofs.CppState.Cell.type =
      caller.scalars.memory.map Proofs.CppState.Cell.type := by rw [memory,memoryPrefix]
  obtain ⟨out,actual,workEq,returned,storage,scalarPeak,heapPeak,totalPeak⟩ := call_of_body program 2 caller prepared initial ty retType
    arguments callee value scalar allowed contexts covered valid preparedRun compacted ran fits types valueValid
  have scalarBound : out.scalars.peak ≤ scalarBudget caller initial expression.nodes := by
    rw [scalarPeak]
    have bound := good.2.2.2.2.2.1
    simp only [scalarBudget,scalarLive]
    omega
  have heapEq : out.objects.heap.peak = heapBudget initial := by
    rw [heapPeak,core.1]
    rfl
  have calleeScalar : callee.scalars.peak ≤ scalarBudget caller initial expression.nodes := by
    have bound := good.2.2.2.2.2.1
    simp only [scalarBudget]
    omega
  have calleeHeap : callee.frame.state.storage.peak ≤ heapBudget initial := by
    rw [core.1]
    exact Nat.le_max_left _ _
  have calleePeak : callee.peak ≤ max initial.peak
      (scalarBudget caller initial expression.nodes+heapBudget initial) := by
    have bound := good.2.2.2.2.2.2.2
    omega
  have combined : out.peak ≤ totalBudget caller initial expression.nodes := by
    rw [totalPeak,heapEq]
    simp only [totalBudget]
    omega
  refine ⟨out,actual,?_,?_,?_,⟨scalarBound,heapEq,combined⟩⟩
  · rw [returned,memory,memoryPrefix]
  · intro owner
    rw [storage owner,core.1]
  · omega

theorem call_from_prepared (program : NProgram) (caller prepared : Context) (initial : NState)
    (ty retType : Ty) (arguments : List NArgument) (expression : NExpr) (rest : Command) (value : Int)
    (body : program.body = .sequence (.primitive (.ret expression)) rest)
    (scalar : program.result = .scalar retType)
    (onlyScalar : expression.scalarOnly = true)
    (allowed : Proofs.CppNoResizeScope.Allowed program.body = true)
    (contexts : ∀ owner scope, (project caller ty).frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (covered : OwnsAll caller.objects.heap)
    (valid : (project caller ty).frame.state.wellFormed = true)
    (preparedRun : prepareArguments caller ty program.parameters arguments = some prepared)
    (compacted : compact (project prepared ty) = some initial)
    (memoryPrefix : initial.scalars.memory.take caller.scalars.memory.length = caller.scalars.memory)
    (denotes : expression.denote (envOf initial) = some value)
    (valueValid : retType.valid value = true) :
    ∃ out, callFuel program 2 caller ty arguments = .finished (out,.scalar value) ∧
      out.scalars.memory = caller.scalars.memory ∧
      (∀ owner, (project out ty).frame.state.storage.lookup owner = initial.frame.state.storage.lookup owner) ∧
      work out ≤ initial.work+expression.nodes+2 := by
  obtain ⟨out,actual,memory,storage,cost,_resources⟩ := call_resources program caller prepared initial
    ty retType arguments expression rest value body scalar onlyScalar allowed contexts covered valid
    preparedRun compacted memoryPrefix denotes valueValid
  exact ⟨out,actual,memory,storage,cost⟩

end Proofs.CppScalarGetterCall
