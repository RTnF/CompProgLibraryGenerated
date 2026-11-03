import Proofs.DynamicPrepare

namespace Proofs.DynamicArguments
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.MultiVecDynamic Proofs.DynamicExpr

def root (params : List Parameter) (st : DynamicStmt.State) (slot : Nat) (expected : Element) (writable : Bool) : Option Parameter := do
  let p ← DynamicStmt.parameter params st.locals slot
  if p.element = expected ∧ (writable = true → p.writable = true) then some p else none

def resolve (params : List Parameter) (st : DynamicStmt.State) : Proofs.CppVectorBindings.Parameter → NArgument → Option Resolved
  | .scalar ty false wr,.value e =>
      if e.resultType = ty then (denote params st.locals st.contents e).map (.scalar ty wr) else none
  | .vector ty wr,.vectorReference slot =>
      (root params st slot (.integer ty) wr).map fun p => .vector p.owner p.scope ty wr
  | .nested ty wr,.vectorReference slot =>
      (root params st slot (.vector (.integer ty)) wr).map fun p => .nestedRoot p.owner p.scope ty wr
  | .scalar ty true wr,.scalarReference slot => do
      let (binding,_) ← DynamicStmt.scalarCell st.locals slot ty
      if wr = true → binding.writable = true then some (.scalarAddress ty binding.address wr) else none
  | _,_ => none

def resolveAll (params : List Parameter) (st : DynamicStmt.State) :
    List Proofs.CppVectorBindings.Parameter → List NArgument → Option (List Resolved)
  | [],[] => some []
  | p::ps,a::args => do
      let first ← resolve params st p a
      let rest ← resolveAll params st ps args
      some (first::rest)
  | _,_ => none

def work : Proofs.CppVectorBindings.Parameter → NArgument → Nat
  | .scalar _ false _,.value e => 2*e.nodes
  | _,_ => 1

def totalWork : List Proofs.CppVectorBindings.Parameter → List NArgument → Nat
  | p::ps,a::args => work p a+totalWork ps args
  | _,_ => 0

theorem root_found (params : List Parameter) (st : DynamicStmt.State) (slot : Nat)
    (expected : Element) (wr : Bool) (p : Parameter) (run : root params st slot expected wr = some p) :
    st.locals.slots[slot]? = some (.vector p.slot) ∧ params.find? (fun q => q.slot == p.slot) = some p ∧
      p.element = expected ∧ (wr = true → p.writable = true) := by
  unfold root at run
  cases found : DynamicStmt.parameter params st.locals slot with
  | none => simp [found] at run
  | some q =>
    simp only [found,Bind.bind,Option.bind] at run
    split at run
    · rename_i good
      have equal := Option.some.inj run
      subst q
      obtain ⟨loc,chosen⟩ := DynamicAppendSound.parameter_found params st.locals slot p found
      exact ⟨loc,chosen,good⟩
    · contradiction

end Proofs.DynamicArguments
