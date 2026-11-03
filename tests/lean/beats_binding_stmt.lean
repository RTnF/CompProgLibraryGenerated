namespace BeatsBindingStmtExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.BeatsBindingCycle
open BeatsSlotEvalExamples BeatsBindingExprExamples

def declaration : NStmt := .declare i32 true compound
def declared : NState := ((declaration.run flat).getD ⟨flat,none,false⟩).state
#guard (declaration.run flat).map viewStep == declaration.run (view flat)
#guard (declared.scalarCell 17 i32).map (·.2.value) == some 2
#guard view (flat.declared i32 true 9) == (view flat).declared i32 true 9

def assignment : NStmt := .assign 16 i32 compound
def locked : NState := {flat with scalars := {flat.scalars with bindings := [⟨0,false⟩]}}
def overflow : NStmt := .assign 16 i32 (.literal u64 2147483648)
#guard (assignment.run flat).map viewStep == assignment.run (view flat)
#guard (assignment.run flat).bind (fun step => (step.state.scalarCell 16 i32).map (·.2.value)) == some 2
#guard assignment.run locked == none
#guard assignment.run (view locked) == none
#guard overflow.run flat == none
#guard (overflow.run flat).map viewStep == overflow.run (view flat)

def writing : NStmt := .write (.local 0) i32 index (.binary i32 .add value (.literal i32 10))
#guard (writing.run flat).map viewStep == writing.run (view flat)
#guard (writing.run (view flat)).bind (fun step => (step.state.frame.state.storage.lookup 0).map (·.items)) ==
  some [.integer 10,.integer 100]

-- The RHS selects a row before the target selects it again. Both temporary
-- bindings must survive evaluation and disappear after the full expression.
def rowWriting : NStmt := .write row i32 (.literal u64 1) (.binary i32 .add rowValue (.literal i32 1))
def rowWritten : NState := ((rowWriting.run paddedRows).getD ⟨paddedRows,none,false⟩).state
#guard (rowWriting.run paddedRows).isSome
#guard rowWritten.frame.bindings.length == 16
#guard (rowWritten.frame.state.storage.lookup 1).map (·.items) == some [.integer 17,.integer 24]
#guard (rowWriting.run paddedRows).map viewStep == rowWriting.run (view paddedRows)
#guard rowWriting.run constRows == none
#guard rowWriting.run (view constRows) == none

def inner : NState :=
  {declared with scope := 1,frame := {declared.frame with bindings := declared.frame.bindings++[⟨0,atom,true,.root 0⟩]}}
#guard (flat.leave inner none).isSome
#guard (flat.leave inner none).map (·.frame.bindings.length) == some 16
#guard (flat.leave inner none).map view == (view flat).leave (view inner) none
#guard (flat.leave inner (some (.scalar 9))).map view == (view flat).leave (view inner) (some (.scalar 9))
#guard (flat.leave inner (some .unit)).map view == (view flat).leave (view inner) (some .unit)
def broken : NState := {inner with scalars := {inner.scalars with memory := []}}
#guard flat.leave broken none == none
#guard (flat.leave broken none).map view == (view flat).leave (view broken) none

-- A returned vector really moves from the inner scope to the outer scope.
def ownedInner : NState :=
  {inner with frame := {inner.frame with state := {inner.frame.state with forest :=
    ⟨inner.frame.state.forest.objects.set 0 (some ⟨atom,none,some 1,[]⟩)⟩}}}
def vectorRet : Option Ret := some (.vector 0 atom)
#guard ownedInner.frame.state.wellFormed
#guard (flat.leave ownedInner vectorRet).isSome
#guard (flat.leave ownedInner vectorRet).bind (fun s => s.frame.state.forest.context 0) == some 0
#guard (flat.leave ownedInner vectorRet).map view == (view flat).leave (view ownedInner) vectorRet

example (outer inner : NState) (ret : Option Ret)
    (base : 16 ≤ outer.frame.bindings.length) (long : 16 ≤ inner.frame.bindings.length) :
    (outer.leave inner ret).map view = (view outer).leave (view inner) ret := leave_view outer inner ret base long

example (s : NState) (long : 16 ≤ s.frame.bindings.length) (c : Container) (ty : Ty) (i v : NExpr) :
    ((NStmt.write c ty i v).run s).map viewStep = (NStmt.write c ty i v).run (view s) := write_run_view s long c ty i v

end BeatsBindingStmtExamples
