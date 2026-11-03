import Proofs.CppMoveReceiverLayout

namespace Proofs.CppMoveReceiverResolve
open Proofs.CppMoveContext Proofs.CppMoveArgumentFacts Proofs.CppMoveReceiverLayout
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedEval
open Proofs.CppNestedCall

theorem stable_scalarCell (s out : Context) (vectorTy ty : Ty) (slot : Nat) (stable : Stable s out) :
    (project out vectorTy).scalarCell slot ty = (project s vectorTy).scalarCell slot ty := by
  simp only [project_scalarCell,scalarSlot,stable.slots,stable.bindings,stable.memory]

theorem stable_environment (s out : Context) (ty : Ty) (stable : Stable s out) :
    envOf (project out ty) = envOf (project s ty) := by
  funext slot expected
  simp only [envOf,stable_scalarCell s out ty expected slot stable]

def parameters (ty : Ty) (values : List (NExpr × Int)) : List Proofs.CppVectorBindings.Parameter :=
  values.map (fun _ => .scalar ty false true)
def arguments (values : List (NExpr × Int)) : List NArgument :=
  values.map (fun pair => .value pair.1)
def values (expressions : List (NExpr × Int)) : List Int := expressions.map Prod.snd

-- Pure typed scalar semantics is an input condition, not completed evaluation.
def Ready (s : Context) (ty : Ty) (expressions : List (NExpr × Int)) : Prop :=
  ∀ expression value, (expression,value) ∈ expressions →
    expression.resultType = ty ∧ expression.scalarOnly = true ∧
    expression.denote (envOf (project s ty)) = some value

theorem ready_stable (s out : Context) (ty : Ty) (expressions : List (NExpr × Int))
    (stable : Stable s out) (ready : Ready s ty expressions) : Ready out ty expressions := by
  intro expression value member
  obtain ⟨type,scalar,denotes⟩ := ready expression value member
  exact ⟨type,scalar,by rw [stable_environment s out ty stable]; exact denotes⟩

-- Construct actual left-to-right argument evaluation from scalar denotations.
theorem resolve_values (s : Context) (ty : Ty) (expressions : List (NExpr × Int))
    (ready : Ready s ty expressions) :
    ∃ last, resolveArguments s ty (parameters ty expressions) (arguments expressions) =
      some (last,valueArguments ty (values expressions)) := by
  induction expressions generalizing s with
  | nil => exact ⟨s,rfl⟩
  | cons head tail ih =>
    rcases head with ⟨expression,value⟩
    obtain ⟨typed,scalar,denotes⟩ := ready expression value (by simp)
    obtain ⟨out,run⟩ := denote_complete expression (project s ty) value scalar denotes
    let next := resumeExpression s out
    have evaluated : evalExpression s ty expression = some (next,value) := by simp [evalExpression,run,next]
    have stable := evalExpression_stable s next ty expression value evaluated
    have tailReady : Ready next ty tail := ready_stable s next ty tail stable
      (fun e v member => ready e v (by simp [member]))
    obtain ⟨last,rest⟩ := ih next tailReady
    have first := resolve_value_runs s next ty ty expression true value typed evaluated
    refine ⟨last,?_⟩
    change resolveArguments s ty (.scalar ty false true :: parameters ty tail)
      (.value expression :: arguments tail) =
      some (last,.scalar ⟨ty,false,true⟩ (.value value) :: valueArguments ty (values tail))
    simp only [resolveArguments,first,Bind.bind,Option.bind,rest]


theorem ready_values_valid (s : Context) (ty : Ty) (expressions : List (NExpr × Int))
    (ready : Ready s ty expressions) : ∀ value ∈ values expressions, ty.valid value = true := by
  intro value member
  obtain ⟨pair,member,equal⟩ := List.mem_map.mp member
  rcases pair with ⟨expression,actual⟩
  change actual = value at equal
  subst actual
  obtain ⟨typed,scalar,denotes⟩ := ready expression value member
  obtain ⟨out,run⟩ := denote_complete expression (project s ty) value scalar denotes
  have evaluated : evalExpression s ty expression = some (resumeExpression s out,value) := by
    simp [evalExpression,run]
  have valid := evalExpression_valid s _ ty expression value evaluated
  rw [typed] at valid
  exact valid

theorem resolve_receiver (s : Context) (ty : Ty) (vectorSlot counterSlot : Nat)
    (borrow : Borrow) (binding : Proofs.CppState.Binding) (count : Int)
    (captured : captureBorrow s vectorSlot borrow.writable = some borrow)
    (counter : (project s ty).scalarCell counterSlot ty = some (binding,⟨ty,count⟩))
    (permission : binding.writable = true) (expressions : List (NExpr × Int))
    (ready : Ready s ty expressions) :
    ∃ last, resolveArguments s ty
      (.vector ty borrow.writable :: .scalar ty true true :: parameters ty expressions)
      (.vectorReference vectorSlot :: .scalarReference counterSlot :: arguments expressions) =
      some (last,receiverArguments borrow ty binding.address true (values expressions)) := by
  let first := charge s 1 1
  have vectorRun := resolve_vector_runs s ty vectorSlot borrow.writable borrow captured
  have stable1 := resolveArgument_stable s first ty (.vector ty borrow.writable) (.vectorReference vectorSlot)
    (.vector borrow) vectorRun
  have cell : (project first ty).scalarCell counterSlot ty = some (binding,⟨ty,count⟩) := by
    rw [stable_scalarCell s first ty ty counterSlot stable1]
    exact counter
  have reference : captureScalarReference first ty counterSlot true =
      some (.scalar ⟨ty,true,true⟩ (.reference binding.address)) := by
    simp [captureScalarReference,cell,permission]
  let second := charge first 1 1
  have scalarRun : resolveArgument first ty (.scalar ty true true) (.scalarReference counterSlot) =
      some (second,.scalar ⟨ty,true,true⟩ (.reference binding.address)) := by
    simp [resolveArgument,reference,second]
  have stable2 := resolveArgument_stable first second ty (.scalar ty true true) (.scalarReference counterSlot)
    (.scalar ⟨ty,true,true⟩ (.reference binding.address)) scalarRun
  obtain ⟨last,rest⟩ := resolve_values second ty expressions
    (ready_stable s second ty expressions (stable1.trans stable2) ready)
  refine ⟨last,?_⟩
  dsimp only [first,second] at scalarRun rest
  simp only [resolveArguments,vectorRun,scalarRun,receiverArguments,Bind.bind,Option.bind,rest]


-- The readonly size field is read from its current caller cell, independently
-- of the vector payload (including the moved-from empty-vector case).
theorem ready_field (s : Context) (ty : Ty) (slot : Nat) (binding : Proofs.CppState.Binding)
    (value : Int) (cell : (project s ty).scalarCell slot ty = some (binding,⟨ty,value⟩))
    (expressions : List (NExpr × Int)) (ready : Ready s ty expressions) :
    Ready s ty ((.variable ty slot,value)::expressions) := by
  intro expression actual member
  rcases List.mem_cons.mp member with equal | member
  · rcases Prod.mk.inj equal with ⟨rfl,rfl⟩
    exact ⟨rfl,rfl,by simp [NExpr.denote,envOf,cell]⟩
  · exact ready expression actual member

theorem resolve_fields (s : Context) (ty : Ty) (vectorSlot counterSlot sizeSlot : Nat)
    (borrow : Borrow) (counterBinding sizeBinding : Proofs.CppState.Binding) (count size : Int)
    (captured : captureBorrow s vectorSlot borrow.writable = some borrow)
    (counter : (project s ty).scalarCell counterSlot ty = some (counterBinding,⟨ty,count⟩))
    (sizeCell : (project s ty).scalarCell sizeSlot ty = some (sizeBinding,⟨ty,size⟩))
    (permission : counterBinding.writable = true) (expressions : List (NExpr × Int))
    (ready : Ready s ty expressions) :
    ∃ last, resolveArguments s ty
      (.vector ty borrow.writable :: .scalar ty true true :: .scalar ty false true :: parameters ty expressions)
      (.vectorReference vectorSlot :: .scalarReference counterSlot ::
        .value (.variable ty sizeSlot) :: arguments expressions) =
      some (last,receiverArguments borrow ty counterBinding.address true (size::values expressions)) := by
  exact resolve_receiver s ty vectorSlot counterSlot borrow counterBinding count captured counter permission
    ((.variable ty sizeSlot,size)::expressions) (ready_field s ty sizeSlot sizeBinding size sizeCell expressions ready)

end Proofs.CppMoveReceiverResolve
