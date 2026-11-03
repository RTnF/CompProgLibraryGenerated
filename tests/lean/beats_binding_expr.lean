namespace BeatsBindingExprExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppMixedInvoke
open Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore
open Proofs.BeatsBindingCycle
open BeatsSlotEvalExamples

def expressions : List NExpr :=
  [compound,short,bad,.literal i32 7,.variable i32 16,
   .cast ⟨8,true,false⟩ (.literal i32 128),
   .targetCast i32 (.literal u64 4294967295),
   .unary i32 .neg (.literal i32 7),
   .divrem i32 false (.literal i32 20) (.literal i32 3),
   .divrem i32 true (.literal i32 20) (.literal i32 3),
   .divrem i32 false (.literal i32 20) (.literal i32 0),
   .logical false (.literal i32 1) bad]

#guard (compound.eval flat).map (·.2) == some 2
#guard expressions.all (fun e =>
  (e.eval flat).map (fun p => (view p.1,p.2)) == e.eval (view flat))
#guard (bad.eval (view flat)) == none
#guard (short.eval (view flat)).map (·.2) == some 0
#guard ((NExpr.cast ⟨8,true,false⟩ (.literal i32 128)).eval (view flat)) == none
#guard ((NExpr.divrem i32 false (.literal i32 20) (.literal i32 0)).eval (view flat)) == none

-- Row selection creates a new binding past the permuted prefix. It must
-- retain its index and inherit the parent's permission in both states.
def paddedRows : NState :=
  {rows with frame := {rows.frame with bindings := List.replicate 16 ⟨0,.vector atom,true,.root 0⟩}}
def constRows : NState :=
  {paddedRows with frame := {paddedRows.frame with bindings := List.replicate 16 ⟨0,.vector atom,false,.root 0⟩}}

#guard paddedRows.frame.state.wellFormed
#guard (row.eval (view paddedRows)).map (·.2) == some 16
#guard (row.eval paddedRows).map (fun p => (view p.1,Proofs.BeatsSlotCycle.uncycle p.2)) == row.eval (view paddedRows)
#guard (rowValue.eval paddedRows).map (fun p => (view p.1,p.2)) == rowValue.eval (view paddedRows)
#guard (rowSize.eval paddedRows).map (fun p => (view p.1,p.2)) == rowSize.eval (view paddedRows)
#guard (rowValue.eval (view paddedRows)).map (fun p => (p.2,p.1.frame.bindings.length)) == some (23,17)
#guard (rowValue.eval constRows).map (fun p => (view p.1,p.2)) == rowValue.eval (view constRows)
#guard (rowValue.eval (view constRows)).bind (fun p => (p.1.frame.bindings[16]?).map (·.writable)) == some false
def invalidRow : NExpr := .read i32 (.row (.local 0) atom (.literal i32 1)) (.literal u64 0)
#guard invalidRow.eval paddedRows == none
#guard invalidRow.eval (view paddedRows) == none

example (s : NState) (long : 16 ≤ s.frame.bindings.length) (e : NExpr) :
    (e.eval s).map (fun p => (view p.1,p.2)) = e.eval (view s) := expr_eval_view s long e

example (s : NState) (long : 16 ≤ s.frame.bindings.length) (e : NExpr) :
    e.eval s = none ↔ e.eval (view s) = none := expr_fault_view s long e

example (s t : NState) (e : NExpr) (value : Int) (ran : e.eval s = some (t,value)) :
    s.frame.bindings.length ≤ t.frame.bindings.length := expr_binding_growth s t e value ran

end BeatsBindingExprExamples
