import Proofs.UfObjectTrace
import Proofs.CppMoveArgumentWork

namespace Proofs.UfObjectTraceWork
open Proofs.UfObjectTrace Proofs.UfObjectState Proofs.CppMoveContext
open Proofs.CppConstructorFinish Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppMoveArgumentWork

def arity : Operation → Nat
  | .root _ | .size _ => 1
  | .same _ _ | .unite _ _ => 2
  | .groups => 0

theorem parameters_length (op : Operation) : op.program.parameters.length = 3 + arity op := by
  cases op <;> rfl

theorem arguments_pure (s : Context) (object : ObjectRef) (state : State s object) (op : Operation) :
    ∀ argument ∈ Proofs.UfObjectCall.arguments s object state.receiver op.expressions, argumentPure argument := by
  cases op <;> simp [Proofs.UfObjectCall.arguments,Operation.expressions,
    Proofs.CppMoveReceiverResolve.arguments,argumentPure,Proofs.CppNestedProgram.NExpr.scalarOnly]

theorem arguments_cost (s : Context) (object : ObjectRef) (state : State s object) (op : Operation) :
    argumentsWork (Proofs.UfObjectCall.arguments s object state.receiver op.expressions) = 3 + arity op := by
  cases op <;> rfl

theorem step_work (s out : Context) (object : ObjectRef) (state : State s object) (next : State out object)
    (op : Operation) (fuel : Nat) (result : Ret) (step : Step s object state op fuel out result next) :
    work out ≤ work s + (7+2*arity op) + bodyWork state.rank op := by
  obtain ⟨prepared,prep,cost⟩ := step.cost
  have setup := prepare_work s prepared Proofs.DoublingNested.i32 op.program.parameters
    (Proofs.UfObjectCall.arguments s object state.receiver op.expressions) (arguments_pure s object state op) prep
  rw [arguments_cost,parameters_length] at setup
  omega

-- Charge accounts for actual setup and the rank at each intermediate State.
inductive Charges (object : ObjectRef) : (s : Context) → State s object → List Operation →
    (out : Context) → List Ret → State out object → Nat → Prop where
  | nil (s : Context) (state : State s object) : Charges object s state [] s [] state 0
  | cons {s middle out : Context} {state : State s object} {next : State middle object}
      {last : State out object} {op : Operation} {tail : List Operation} {result : Ret} {results : List Ret}
      {fuel : Nat} (charge : Nat) (first : Step s object state op fuel middle result next)
      (rest : Charges object middle next tail out results last charge) :
      Charges object s state (op::tail) out (result::results) last
        ((7+2*arity op)+bodyWork state.rank op+charge)

theorem history_work (object : ObjectRef) (s out : Context) (state : State s object)
    (next : State out object) (ops : List Operation) (results : List Ret)
    (history : History object s state ops out results next) :
    ∃ charge, Charges object s state ops out results next charge ∧ work out ≤ work s + charge := by
  induction history with
  | nil original initial => exact ⟨0,.nil original initial,by simp⟩
  | @cons source middle final initial after last op tail result results ready fuel first rest ih =>
    obtain ⟨charge,charges,bound⟩ := ih
    have one := step_work source middle object initial after op fuel result first
    exact ⟨(7+2*arity op)+bodyWork initial.rank op+charge,.cons charge first charges,by omega⟩

theorem execute_work (s : Context) (object : ObjectRef) (state : State s object) (ops : List Operation)
    (ready : ∀ op ∈ ops, op.Valid state.data.items.length) :
    ∃ (script : List (Nat × Operation)) (out : Context) (results : List Ret) (next : State out object) (charge : Nat),
      script.map Prod.snd = ops ∧ run s object script = .finished (out,results) ∧
      results.length = ops.length ∧ next.receiver.size.value = state.receiver.size.value ∧
      History object s state ops out results next ∧ Charges object s state ops out results next charge ∧
      work out ≤ work s + charge := by
  obtain ⟨script,out,results,next,mapped,ran,count,size,history⟩ := execute s object state ops ready
  obtain ⟨charge,charges,bound⟩ := history_work object s out state next ops results history
  exact ⟨script,out,results,next,charge,mapped,ran,count,size,history,charges,bound⟩

end Proofs.UfObjectTraceWork
