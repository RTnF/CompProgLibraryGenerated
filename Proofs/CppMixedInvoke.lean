import Proofs.CppReferenceInvoke
import Proofs.CppVectorBindings

namespace Proofs.CppMixedInvoke
open Proofs.CppScalar

inductive Location where | scalar (slot : Nat) | vector (slot : Nat)
deriving DecidableEq, Repr
structure State where
  scalars : CppState.State
  vectors : CppVectorBindings.Frame
  slots : List Location := []
  peak : Nat := 0
deriving DecidableEq, Repr
inductive Argument where
  | value (expression : Expr)
  | scalarReference (slot : Nat)
  | vectorReference (slot : Nat)
deriving DecidableEq, Repr
inductive Resolved where
  | scalar (parameter : CppState.Parameter) (argument : CppState.Argument)
  | vector (owner : Nat) (element : Ty) (writable : Bool)
deriving DecidableEq, Repr

def expressionType : Expr → Ty
  | .literal ty _ | .variable ty _ | .cast ty _ | .unary ty _ _
  | .binary ty _ _ _ | .divrem ty _ _ _ | .targetCast ty _ => ty

def State.work (s : State) : Nat := s.scalars.work+s.vectors.store.work
-- A conservative combination of the two component maxima. Slot maps are
-- ghost metadata; scalar/vector reference bindings are counted by each core.
def State.observe (s : State) : State :=
  {s with peak := max s.peak (s.scalars.peak+s.vectors.peak)}

def resolve (caller : State) (parameter : CppVectorBindings.Parameter) (argument : Argument) :
    Option (Resolved × Nat) := do
  match parameter,argument with
  | .scalar ty false writable,.value e =>
      if expressionType e = ty then
        let (value,work) ← CppReferenceInvoke.resolveArgument caller.scalars ⟨ty,false,writable⟩ (.value e)
        some (.scalar ⟨ty,false,writable⟩ value,work)
      else none
  | .scalar ty true writable,.scalarReference slot =>
      let (value,work) ← CppReferenceInvoke.resolveArgument caller.scalars ⟨ty,true,writable⟩ (.reference slot)
      some (.scalar ⟨ty,true,writable⟩ value,work)
  | .vector ty writable,.vectorReference slot =>
      let (binding,_) ← caller.vectors.resolve slot ty
      if writable = true → binding.writable = true then
        some (.vector binding.owner ty writable,1)
      else none
  | _,_ => none

def resolveAll (caller : State) : List CppVectorBindings.Parameter → List Argument →
    Option (List Resolved × Nat)
  | [],[] => some ([],0)
  | p::ps,a::args => do
      let (first,work) ← resolve caller p a
      let (rest,restWork) ← resolveAll caller ps args
      some (first::rest,work+restWork)
  | _,_ => none

def bindOne (s : State) : Resolved → Option State
  | .scalar p a => do
      let scalars ← CppState.bindArgument s.scalars p a
      some (({s with scalars := scalars,slots := s.slots ++ [.scalar s.scalars.bindings.length]} : State).observe)
  | .vector owner ty writable => do
      let vectors ← s.vectors.bind owner ty writable
      some (({s with vectors := vectors,slots := s.slots ++ [.vector s.vectors.bindings.length]} : State).observe)

def bindAll (s : State) : List Resolved → Option State
  | [] => some s
  | p::ps => do
      let next ← bindOne s p
      bindAll next ps

def Argument.nodes : Argument → Nat
  | .value e => e.nodes
  | .scalarReference _ | .vectorReference _ => 1

def argumentPeak (caller : State) (arguments : List Argument) : Nat :=
  arguments.foldl (fun peak a => max peak ((caller.scalars.observe (caller.vectors.bindings.length+arguments.length+a.nodes)).peak)) caller.scalars.peak

private theorem fold_max_lower (observed : Argument → Nat) (arguments : List Argument)
    (initial : Nat) : initial ≤ arguments.foldl (fun peak a => max peak (observed a)) initial := by
  induction arguments generalizing initial with
  | nil => exact Nat.le_refl _
  | cons a rest ih =>
      exact Nat.le_trans (Nat.le_max_left _ _) (ih (max initial (observed a)))

theorem argumentPeak_head_bounds (caller : State) (first : Argument) (rest : List Argument) :
    caller.scalars.memory.length-caller.scalars.baseMemory+caller.scalars.bindings.length+
      (caller.vectors.bindings.length+(first::rest).length+first.nodes) ≤
      argumentPeak caller (first::rest) := by
  unfold argumentPeak
  simp only [List.foldl_cons]
  exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_trans (Nat.le_max_right _ _)
    (fold_max_lower _ rest _))

-- Resolve every reference against the original caller before allocating
-- copies or reserving caller binding cells. Newly created cells cannot be
-- passed as references by manufacturing an address into the callee frame.
def prepare (caller : State) (parameters : List CppVectorBindings.Parameter) (arguments : List Argument) :
    Option State := do
  if caller.vectors.types.length = caller.vectors.store.objects.length then
    let (resolved,work) ← resolveAll caller parameters arguments
    let scalarInitial : CppState.State := {caller.scalars with
      memory := caller.scalars.memory ++ List.replicate
        (caller.scalars.bindings.length+caller.vectors.bindings.length) ⟨⟨1,false,true⟩,0⟩,
      bindings := [],work := caller.scalars.work+1+work+parameters.length,
      peak := argumentPeak caller arguments}
    let vectorInitial : CppVectorBindings.Frame := {caller.vectors with bindings := []}
    bindAll (⟨scalarInitial.observe 0,vectorInitial,[],caller.peak⟩ : State).observe resolved
  else none

def retiredObjects (objects : List (Option (CppVector.Buffer Int))) (callerCount : Nat) :
    List (Option (CppVector.Buffer Int)) :=
  objects.take callerCount ++ List.replicate (objects.length-callerCount) none

-- Restore a lexical scope without allocating a return-value binding. Values
-- computed before leaving the scope are carried separately by the Step.
def leaveScope (caller callee : State) : Option State := do
  if caller.vectors.types.length = caller.vectors.store.objects.length ∧
      caller.scalars.memory.length ≤ callee.scalars.memory.length ∧
      caller.vectors.store.objects.length ≤ callee.vectors.store.objects.length ∧
      callee.vectors.types.length = callee.vectors.store.objects.length ∧
      callee.vectors.types.take caller.vectors.types.length = caller.vectors.types ∧
      (callee.scalars.memory.take caller.scalars.memory.length).map CppState.Cell.type =
        caller.scalars.memory.map CppState.Cell.type ∧
      (callee.vectors.store.objects.take caller.vectors.store.objects.length).map (Option.map CppVector.Buffer.owner) =
        caller.vectors.store.objects.map (Option.map CppVector.Buffer.owner) then
    let scalars : CppState.State := {caller.scalars with
      memory := callee.scalars.memory.take caller.scalars.memory.length,
      work := callee.scalars.work+1,peak := max caller.scalars.peak callee.scalars.peak}
    let privateCount := (callee.vectors.store.objects.drop caller.vectors.store.objects.length).countP Option.isSome
    let store : CppVectorStore.Store Int := {callee.vectors.store with
      objects := retiredObjects callee.vectors.store.objects caller.vectors.store.objects.length,
      work := callee.vectors.store.work+privateCount}
    let vectors : CppVectorBindings.Frame := {caller.vectors with
      store := store,types := callee.vectors.types,peak := max caller.vectors.peak callee.vectors.peak}
    some ((⟨scalars.observe 0,vectors.observe 0,caller.slots,max caller.peak callee.peak⟩ : State).observe)
  else none

-- Scalar-valued calls cannot export private vector objects. Keep tombstones
-- rather than truncating the object store, so later calls never recycle IDs.
def finishScalar (caller callee : State) (resultType : Ty) (value : Int) : Option State := do
  if resultType.valid value ∧ caller.vectors.types.length = caller.vectors.store.objects.length ∧
      caller.scalars.memory.length ≤ callee.scalars.memory.length ∧
      caller.vectors.store.objects.length ≤ callee.vectors.store.objects.length ∧
      callee.vectors.types.length = callee.vectors.store.objects.length ∧
      callee.vectors.types.take caller.vectors.types.length = caller.vectors.types ∧
      (callee.scalars.memory.take caller.scalars.memory.length).map CppState.Cell.type =
        caller.scalars.memory.map CppState.Cell.type ∧
      (callee.vectors.store.objects.take caller.vectors.store.objects.length).map (Option.map CppVector.Buffer.owner) =
        caller.vectors.store.objects.map (Option.map CppVector.Buffer.owner) then
    let scalars : CppState.State := {caller.scalars with
      memory := callee.scalars.memory.take caller.scalars.memory.length ++ [⟨resultType,value⟩],
      bindings := caller.scalars.bindings ++ [⟨caller.scalars.memory.length,false⟩],
      work := callee.scalars.work+1,peak := max caller.scalars.peak callee.scalars.peak}
    let privateCount := (callee.vectors.store.objects.drop caller.vectors.store.objects.length).countP Option.isSome
    let store : CppVectorStore.Store Int := {callee.vectors.store with
      objects := retiredObjects callee.vectors.store.objects caller.vectors.store.objects.length,
      work := callee.vectors.store.work+privateCount}
    let vectors : CppVectorBindings.Frame := {caller.vectors with
      store := store,types := callee.vectors.types,peak := max caller.vectors.peak callee.vectors.peak}
    some ((⟨scalars.observe 0,vectors.observe 0,caller.slots ++ [.scalar caller.scalars.bindings.length],
      max caller.peak callee.peak⟩ : State).observe)
  else none

theorem resolve_value_wrong_type (caller : State) (ty : Ty) (writable : Bool) (expression : Expr)
    (wrong : expressionType expression ≠ ty) :
    resolve caller (.scalar ty false writable) (.value expression) = none := by simp [resolve,wrong]

theorem resolve_vector_readonly (caller : State) (ty : Ty) (slot : Nat)
    (binding : CppVectorBindings.Binding) (buffer : CppVector.Buffer Int)
    (found : caller.vectors.resolve slot ty = some (binding,buffer)) (readonly : binding.writable = false) :
    resolve caller (.vector ty true) (.vectorReference slot) = none := by simp [resolve,found,readonly]

theorem resolve_vector_runs (caller : State) (ty : Ty) (slot : Nat) (writable : Bool)
    (binding : CppVectorBindings.Binding) (buffer : CppVector.Buffer Int)
    (found : caller.vectors.resolve slot ty = some (binding,buffer))
    (permission : writable = true → binding.writable = true) :
    resolve caller (.vector ty writable) (.vectorReference slot) = some (.vector binding.owner ty writable,1) := by
  simp [resolve,found]
  exact permission

theorem resolveAll_nil (caller : State) : resolveAll caller [] [] = some ([],0) := rfl

theorem resolveAll_cons (caller : State) (p : CppVectorBindings.Parameter) (a : Argument)
    (ps : List CppVectorBindings.Parameter) (args : List Argument) (first : Resolved) (rest : List Resolved)
    (work restWork : Nat) (one : resolve caller p a = some (first,work))
    (tail : resolveAll caller ps args = some (rest,restWork)) :
    resolveAll caller (p::ps) (a::args) = some (first::rest,work+restWork) := by simp [resolveAll,one,tail]

theorem bindAll_nil (s : State) : bindAll s [] = some s := rfl

theorem bindAll_cons (s next result : State) (p : Resolved) (ps : List Resolved)
    (one : bindOne s p = some next) (tail : bindAll next ps = some result) :
    bindAll s (p::ps) = some result := by simp [bindAll,one,tail]

theorem prepare_bad_metadata (caller : State) (parameters : List CppVectorBindings.Parameter)
    (arguments : List Argument) (wrong : caller.vectors.types.length ≠ caller.vectors.store.objects.length) :
    prepare caller parameters arguments = none := by simp [prepare,wrong]

theorem prepare_resolution_failure (caller : State) (parameters : List CppVectorBindings.Parameter)
    (arguments : List Argument) (failure : resolveAll caller parameters arguments = none) :
    prepare caller parameters arguments = none := by simp [prepare,failure]

theorem finish_invalid_value (caller callee : State) (resultType : Ty) (value : Int)
    (invalid : resultType.valid value = false) : finishScalar caller callee resultType value = none := by
  simp [finishScalar,invalid]

theorem leaveScope_bad_metadata (caller callee : State)
    (wrong : caller.vectors.types.length ≠ caller.vectors.store.objects.length) :
    leaveScope caller callee = none := by simp [leaveScope,wrong]

theorem leaveScope_bindings (caller callee restored : State)
    (success : leaveScope caller callee = some restored) :
    restored.scalars.bindings = caller.scalars.bindings ∧
    restored.vectors.bindings = caller.vectors.bindings ∧ restored.slots = caller.slots := by
  unfold leaveScope at success
  split at success
  · cases success
    exact ⟨rfl,rfl,rfl⟩
  · contradiction

theorem leaveScope_object_count (caller callee restored : State)
    (success : leaveScope caller callee = some restored) :
    restored.vectors.store.objects.length = callee.vectors.store.objects.length := by
  unfold leaveScope at success
  split at success
  · rename_i compatible
    cases success
    change (retiredObjects callee.vectors.store.objects caller.vectors.store.objects.length).length = callee.vectors.store.objects.length
    simp [retiredObjects,List.length_take,Nat.min_eq_left compatible.2.2.1]
    omega
  · contradiction

theorem retired_length (objects : List (Option (CppVector.Buffer Int))) (count : Nat)
    (bounded : count ≤ objects.length) : (retiredObjects objects count).length = objects.length := by
  simp [retiredObjects,List.length_take,Nat.min_eq_left bounded]
  omega

theorem retired_old (objects : List (Option (CppVector.Buffer Int))) (count owner : Nat)
    (old : owner < count) (countBound : count ≤ objects.length) :
    (retiredObjects objects count)[owner]? = objects[owner]? := by
  have takeLength : (objects.take count).length = count := by
    simp [List.length_take,Nat.min_eq_left countBound]
  simp [retiredObjects,List.getElem?_append,takeLength,old]

theorem retired_private (objects : List (Option (CppVector.Buffer Int))) (count owner : Nat)
    (privateIndex : count ≤ owner) (bounded : owner < objects.length) (countBound : count ≤ objects.length) :
    (retiredObjects objects count)[owner]? = some none := by
  have takeLength : (objects.take count).length = count := by simp [List.length_take,Nat.min_eq_left countBound]
  have notOld : ¬ owner < count := by omega
  have remaining : owner-count < objects.length-count := by omega
  simp [retiredObjects,List.getElem?_append,takeLength,notOld,remaining]

theorem observe_bounds (s : State) : s.peak ≤ s.observe.peak ∧
    s.scalars.peak+s.vectors.peak ≤ s.observe.peak := by exact ⟨Nat.le_max_left _ _,Nat.le_max_right _ _⟩

theorem observe_preserves (s : State) : s.observe.scalars = s.scalars ∧
    s.observe.vectors = s.vectors ∧ s.observe.slots = s.slots := by exact ⟨rfl,rfl,rfl⟩

end Proofs.CppMixedInvoke
