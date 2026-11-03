namespace BeatsSlotStmtExamples
open Proofs.CppNestedProgram Proofs.CppMixedInvoke Proofs.CppScalar
open Proofs.BeatsSlotCycle Proofs.CppSlotRename
open BeatsSlotEvalExamples

def declaration : NStmt := .declare i32 true compound
def actualDeclaration : NStmt := .declare i32 true (expr cycle compound)
def declared : NState := ((actualDeclaration.run flat).getD ⟨flat,none,false⟩).state

#guard declared.slots.length == 18
#guard (declared.scalarCell 17 i32).map (·.2.value) == some 3
#guard ((actualDeclaration.run flat).map permuteStep) == declaration.run (permute flat)

def assignment : NStmt := .assign 16 i32 compound
def actualAssignment : NStmt := .assign 16 i32 (expr cycle compound)
#guard (actualAssignment.run flat).bind (fun p => (p.state.scalarCell 16 i32).map (·.2.value)) == some 3
#guard ((actualAssignment.run flat).map permuteStep) == assignment.run (permute flat)

def locked : NState := {flat with scalars := {flat.scalars with bindings := [⟨0,false⟩]}}
#guard actualAssignment.run locked == none
#guard ((actualAssignment.run locked).map permuteStep) == assignment.run (permute locked)
def narrow : NStmt := .assign 16 i32 (.literal ⟨64,true,false⟩ 2147483648)
#guard narrow.run flat == none
#guard (narrow.run flat).map permuteStep == narrow.run (permute flat)

def rhs : NExpr := .binary i32 .add value (.literal i32 10)
def write : NStmt := .write (.local 0) i32 index rhs
def actualWrite : NStmt := .write (.local 1) i32 (expr cycle index) (expr cycle rhs)
def written : NState := ((actualWrite.run flat).getD ⟨flat,none,false⟩).state
#guard (written.frame.state.storage.lookup 1).map (·.items) == some [.integer 11,.integer 101]
#guard (written.frame.state.storage.lookup 0).map (·.items) == some [.integer 0,.integer 100]
#guard (actualWrite.run flat).map permuteStep == write.run (permute flat)

def rowWrite : NStmt := .write row i32 (.literal u64 1) (.literal i32 88)
def actualRowWrite : NStmt := .write (container cycle row) i32 (.literal u64 1) (.literal i32 88)
def rowWritten : NState := ((actualRowWrite.run rows).getD ⟨rows,none,false⟩).state
#guard (rowWritten.frame.state.storage.lookup 1).map (·.items) == some [.integer 17,.integer 88]
#guard rowWritten.frame.bindings.length == rows.frame.bindings.length
#guard (actualRowWrite.run rows).map permuteStep == rowWrite.run (permute rows)

def inner : NState := {declared with scope := 1}
#guard (flat.leave inner none).isSome
#guard ((flat.leave inner none).map permute) == (permute flat).leave (permute inner) none
#guard (flat.leave inner none).map (·.slots) == some flat.slots
#guard (flat.leave inner none).map (·.scalars.memory.length) == some 1
def broken : NState := {inner with scalars := {inner.scalars with memory := []}}
#guard flat.leave broken none == none
#guard ((flat.leave broken none).map permute) == (permute flat).leave (permute broken) none

example (s : NState) (long : 16 ≤ s.slots.length) (c : Container) (ty : Ty) (i v : NExpr) :
    ((NStmt.write (container cycle c) ty (expr cycle i) (expr cycle v)).run s).map permuteStep =
      (NStmt.write c ty i v).run (permute s) := write_run_permute s long c ty i v

example (outer inner : NState) (ret : Option Ret) :
    (outer.leave inner ret).map permute = (permute outer).leave (permute inner) ret :=
  leave_permute outer inner ret

end BeatsSlotStmtExamples
