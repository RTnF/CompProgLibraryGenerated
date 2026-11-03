import Proofs.CppMoveArgumentFacts
import Proofs.CppNestedEval

namespace Proofs.CppMoveArgumentWork
open Proofs.CppMoveContext Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.DynamicResultValid

def argumentWork : NArgument → Nat
  | .value expression => expression.nodes
  | .vectorReference _ | .scalarReference _ => 1

def argumentPure : NArgument → Prop
  | .value expression => expression.scalarOnly = true
  | .vectorReference _ | .scalarReference _ => True

def argumentsWork (arguments : List NArgument) : Nat := (arguments.map argumentWork).sum

theorem eval_work (s out : Context) (ty : Ty) (expression : NExpr) (value : Int)
    (pure : expression.scalarOnly = true) (run : evalExpression s ty expression = some (out,value)) :
    work s ≤ work out ∧ work out ≤ work s + expression.nodes := by
  unfold evalExpression at run
  obtain ⟨pair,actual,last⟩ := bind_some _ _ _ run
  rcases pair with ⟨after,result⟩
  have equal := Prod.mk.inj (Option.some.inj last)
  rw [← equal.1]
  have good := Proofs.CppNestedEval.eval_scalar expression (project s ty) after result pure actual
  have lower := good.2.1
  have upper := good.2.2.1
  change s.scalars.work ≤ after.scalars.work at lower
  change after.scalars.work ≤ s.scalars.work + expression.nodes at upper
  change s.scalars.work+s.objects.heap.work ≤ after.scalars.work+s.objects.heap.work ∧
    after.scalars.work+s.objects.heap.work ≤ s.scalars.work+s.objects.heap.work+expression.nodes
  omega

theorem charge_work (s : Context) (amount temporaries : Nat) :
    work (charge s amount temporaries) = work s + amount := by
  simp only [work,charge,Proofs.CppState.State.observe]
  omega

theorem resolve_argument_work (s out : Context) (ty : Ty) (parameter : Proofs.CppVectorBindings.Parameter)
    (argument : NArgument) (saved : SavedArgument) (pure : argumentPure argument)
    (run : resolveArgument s ty parameter argument = some (out,saved)) :
    work s ≤ work out ∧ work out ≤ work s + argumentWork argument := by
  cases argument with
  | value expression =>
    cases parameter with
    | nested element writable => simp [resolveArgument] at run
    | vector expected writable => simp [resolveArgument] at run
    | scalar expected reference writable =>
      cases reference with
      | true => simp [resolveArgument] at run
      | false =>
        simp only [resolveArgument] at run
        split at run
        · obtain ⟨pair,evaluated,last⟩ := bind_some _ _ _ run
          rcases pair with ⟨next,value⟩
          have equal := Prod.mk.inj (Option.some.inj last)
          rw [← equal.1]
          exact eval_work s next ty expression value pure evaluated
        · simp at run
  | scalarReference slot =>
    cases parameter with
    | nested element writable => simp [resolveArgument] at run
    | vector expected writable => simp [resolveArgument] at run
    | scalar expected reference writable =>
      cases reference with
      | false => simp [resolveArgument] at run
      | true =>
        simp only [resolveArgument] at run
        obtain ⟨argument,found,last⟩ := bind_some _ _ _ run
        have equal := Prod.mk.inj (Option.some.inj last)
        rw [← equal.1]
        rw [charge_work]
        change work s ≤ work s+1 ∧ work s+1 ≤ work s+1
        omega
  | vectorReference slot =>
    cases parameter with
    | nested element writable => simp [resolveArgument] at run
    | scalar expected reference writable => simp [resolveArgument] at run
    | vector expected writable =>
      simp only [resolveArgument] at run
      split at run
      · obtain ⟨argument,found,last⟩ := bind_some _ _ _ run
        have equal := Prod.mk.inj (Option.some.inj last)
        rw [← equal.1]
        rw [charge_work]
        change work s ≤ work s+1 ∧ work s+1 ≤ work s+1
        omega
      · simp at run

theorem resolve_arguments_work (s out : Context) (ty : Ty) (parameters : List Proofs.CppVectorBindings.Parameter)
    (arguments : List NArgument) (saved : List SavedArgument) (pure : ∀ argument ∈ arguments, argumentPure argument)
    (run : resolveArguments s ty parameters arguments = some (out,saved)) :
    work s ≤ work out ∧ work out ≤ work s + argumentsWork arguments := by
  induction parameters generalizing s out arguments saved with
  | nil =>
    cases arguments with
    | nil =>
      have equal := Prod.mk.inj (Option.some.inj run)
      rw [← equal.1]
      exact ⟨Nat.le_refl _,by simp [argumentsWork]⟩
    | cons argument tail => simp [resolveArguments] at run
  | cons parameter parameters ih =>
    cases arguments with
    | nil => simp [resolveArguments] at run
    | cons argument arguments =>
      unfold resolveArguments at run
      obtain ⟨pair,first,rest⟩ := bind_some _ _ _ run
      rcases pair with ⟨next,head⟩
      obtain ⟨pair,tail,last⟩ := bind_some _ _ _ rest
      rcases pair with ⟨final,savedTail⟩
      have equal := Prod.mk.inj (Option.some.inj last)
      rw [← equal.1]
      have one := resolve_argument_work s next ty parameter argument head (pure _ (by simp)) first
      have two := ih next final arguments savedTail (fun arg member => pure arg (by simp [member])) tail
      have sum : argumentsWork (argument::arguments) = argumentWork argument+argumentsWork arguments := by
        simp [argumentsWork]
      rw [sum]
      omega

theorem prepare_work (s out : Context) (ty : Ty) (parameters : List Proofs.CppVectorBindings.Parameter)
    (arguments : List NArgument) (pure : ∀ argument ∈ arguments, argumentPure argument)
    (run : prepareArguments s ty parameters arguments = some out) :
    work s ≤ work out ∧ work out ≤ work s + argumentsWork arguments + 1 + parameters.length := by
  unfold prepareArguments at run
  obtain ⟨pair,resolved,prepared⟩ := bind_some _ _ _ run
  rcases pair with ⟨last,saved⟩
  have cost := resolve_arguments_work s last ty parameters arguments saved pure resolved
  have length := Proofs.CppMoveArgumentFacts.resolveArguments_lengths s last ty parameters arguments saved resolved
  have bound := (prepareSaved_resources last out saved prepared).2.2.1
  rw [length.1] at bound
  omega

end Proofs.CppMoveArgumentWork
