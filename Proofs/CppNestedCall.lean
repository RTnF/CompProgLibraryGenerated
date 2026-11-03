import Proofs.CppNestedProgram

namespace Proofs.CppNestedCall
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppLoop

-- Arguments are scalar values or caller vector bindings. A vector parameter
-- borrows a caller root or a live row header. A scalar reference parameter binds the
-- address of a caller scalar cell, so callee writes are visible in the caller.
inductive NArgument where
  | value (expression : NExpr)
  | vectorReference (slot : Nat)
  | scalarReference (slot : Nat)

inductive ResultKind where
  | scalar (ty : Ty)
  | vector (element : Element)
  | unit
deriving DecidableEq, Repr

structure NProgram where
  parameters : List CppVectorBindings.Parameter
  result : ResultKind
  body : Command

def _root_.Proofs.CppNestedProgram.NExpr.resultType : NExpr → Ty
  | .literal ty _ | .variable ty _ | .cast ty _ | .targetCast ty _ | .unary ty _ _
  | .binary ty _ _ _ | .divrem ty _ _ _ | .read ty _ _ => ty
  | .logical _ _ _ => ⟨1,false,true⟩
  | .size _ _ => ⟨64,false,false⟩

inductive Resolved where
  | scalar (ty : Ty) (writable : Bool) (value : Int)
  | vector (owner scope : Nat) (ty : Ty) (writable : Bool)
  | scalarAddress (ty : Ty) (address : Nat) (writable : Bool)
  | nestedRoot (owner scope : Nat) (ty : Ty) (writable : Bool)
  | vectorChild (owner : Nat) (address : Proofs.CppVector.ElementRef) (ty : Ty) (writable : Bool)
deriving DecidableEq, Repr

-- Every argument is resolved against the caller before any callee binding
-- exists, so a callee binding can never be passed as a caller reference.
def resolve (caller : NState) (parameter : CppVectorBindings.Parameter) (argument : NArgument) :
    Option (NState × Resolved) := do
  match parameter,argument with
  | .scalar ty false writable,.value expression =>
      if expression.resultType = ty then
        let (next,value) ← expression.eval caller
        some (next,.scalar ty writable value)
      else none
  | .vector ty writable,.vectorReference slot =>
      let index ← caller.vectorSlot slot
      let binding ← caller.frame.bindings[index]?
      let (_,_) ← caller.frame.resolve index (.integer ty)
      match binding.header with
      | .root scope =>
          if binding.element = .integer ty ∧ (writable = true → binding.writable = true) then
            some (caller.charge 1 1,.vector binding.owner scope ty writable)
          else none
      | .child address =>
          if binding.element = .integer ty ∧ (writable = true → binding.writable = true) then
            some (caller.charge 1 1,.vectorChild binding.owner address ty writable)
          else none
  | .nested ty writable,.vectorReference slot =>
      let index ← caller.vectorSlot slot
      let binding ← caller.frame.bindings[index]?
      let (_,_) ← caller.frame.resolve index (.vector (.integer ty))
      match binding.header with
      | .root scope =>
          if binding.element = .vector (.integer ty) ∧ (writable = true → binding.writable = true) then
            some (caller.charge 1 1,.nestedRoot binding.owner scope ty writable)
          else none
      | .child _ => none
  | .scalar ty true writable,.scalarReference slot => do
      let (binding,_) ← caller.scalarCell slot ty
      if writable = true → binding.writable = true then
        some (caller.charge 1 1,.scalarAddress ty binding.address writable)
      else none
  | _,_ => none

def resolveAll (caller : NState) : List CppVectorBindings.Parameter → List NArgument →
    Option (NState × List Resolved)
  | [],[] => some (caller,[])
  | p::ps,a::args => do
      let (next,first) ← resolve caller p a
      let (last,rest) ← resolveAll next ps args
      some (last,first::rest)
  | _,_ => none

def bindOne (s : NState) : Resolved → Option NState
  | .scalar ty writable value => do
      let scalars ← CppState.bindArgument s.scalars ⟨ty,false,writable⟩ (.value value)
      some (({s with scalars := scalars,slots := s.slots ++ [.scalar s.scalars.bindings.length]} : NState).observe)
  | .vector owner scope ty writable => do
      let (frame,binding) ← s.frame.bindRoot owner (.integer ty) scope writable
      some (({s with frame := frame,slots := s.slots ++ [.vector binding]} : NState).observe)
  | .nestedRoot owner scope ty writable => do
      let (frame,binding) ← s.frame.bindRoot owner (.vector (.integer ty)) scope writable
      some (({s with frame := frame,slots := s.slots ++ [.vector binding]} : NState).observe)
  | .scalarAddress ty address writable => do
      let scalars ← CppState.bindArgument s.scalars ⟨ty,true,writable⟩ (.reference address)
      some (({s with scalars := scalars,slots := s.slots ++ [.scalar s.scalars.bindings.length]} : NState).observe)
  | .vectorChild owner address ty writable => do
      let (frame,binding) := s.frame.addBinding ⟨owner,.integer ty,writable,.child address⟩
      let _ ← frame.resolve binding (.integer ty)
      some (({s with frame := frame,slots := s.slots ++ [.vector binding]} : NState).observe)

def bindAll (s : NState) : List Resolved → Option NState
  | [] => some s
  | r::rs => do
      let next ← bindOne s r
      bindAll next rs

-- The callee frame starts without caller bindings; reserved scalar cells
-- keep the caller's live locals in the space account.
def prepare (caller : NState) (parameters : List CppVectorBindings.Parameter)
    (arguments : List NArgument) : Option NState := do
  if caller.frame.state.wellFormed then
    let (last,resolved) ← resolveAll caller parameters arguments
    let released := last.release caller
    let scalars : CppState.State := {released.scalars with
      memory := released.scalars.memory ++ List.replicate
        (released.scalars.bindings.length+released.frame.bindings.length) ⟨⟨1,false,true⟩,0⟩,
      bindings := [],work := released.scalars.work+1+parameters.length}
    let initial : NState := ⟨scalars,{released.frame with bindings := []},[],caller.scope+1,released.peak⟩
    bindAll initial.observe resolved
  else none

-- Leave the callee: transfer a returned vector root to the caller's scope,
-- retire the callee's remaining objects and restore the caller's metadata.
def finish (caller callee : NState) (result : ResultKind) (returned : Option Ret) :
    Option (NState × Ret) := do
  if caller.scalars.memory.length ≤ callee.scalars.memory.length ∧
      (callee.scalars.memory.take caller.scalars.memory.length).map CppState.Cell.type =
        caller.scalars.memory.map CppState.Cell.type then
    let finished ← match result,returned with
      | .scalar ty,some (.scalar value) =>
          if ty.valid value then some (callee.frame,Ret.scalar value) else none
      | .vector element,some (.vector owner returnedElement) =>
          if returnedElement = element then do
            let moved ← callee.frame.transferRoot owner element callee.scope caller.scope
            some (moved,Ret.vector owner element)
          else none
      | .unit,none => some (callee.frame,Ret.unit)
      | .unit,some .unit => some (callee.frame,Ret.unit)
      | _,_ => none
    let retired ← finished.1.retireScope callee.scope
    let scalars : CppState.State := {caller.scalars with
      memory := callee.scalars.memory.take caller.scalars.memory.length,
      work := callee.scalars.work+1,peak := max caller.scalars.peak callee.scalars.peak}
    let frame := {retired with bindings := caller.frame.bindings}
    some ((⟨scalars.observe 0,frame,caller.slots,caller.scope,max caller.peak callee.peak⟩ : NState).observe,
      finished.2)
  else none

def NProgram.callFuel (program : NProgram) (fuel : Nat) (caller : NState) (arguments : List NArgument) :
    Outcome (NState × Ret) := do
  let initial ← liftChecked (prepare caller program.parameters arguments)
  let step ← runFuel fuel program.body initial
  if step.breaking then .fault else
    liftChecked (finish caller step.state program.result step.returned)

def NProgram.Terminates (program : NProgram) (caller : NState) (arguments : List NArgument) : Prop :=
  ∃ fuel result, program.callFuel fuel caller arguments = .finished result

end Proofs.CppNestedCall
