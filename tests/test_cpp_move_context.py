"""Caller state projection, argument binding and borrowed call exit checks."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'tools'),str(ROOT/'tests')]
from test_scalar_ir import lean_environment
from test_cpp_move_headers import CHECKS as HEADER_CHECKS
from test_cpp_move_frame import CHECKS as FRAME_CHECKS
from test_cpp_move_write import CHECKS as WRITE_CHECKS
from offline import disable_network

CHECKS = r'''
namespace ContextExamples
open Proofs.CppMoveContext ViewExamples FrameExamples
 def scalarState : Proofs.CppState.State := {memory := [⟨ty,7⟩],bindings := [⟨0,true⟩]}
def initialContext : Context := ⟨initial,scalarState,[.vector 0,.scalar 0,.vector 1,.vector 3],0,0⟩
def movedContext : Context := {initialContext with objects := transferred}
#guard (project initialContext ty).scalarSlot 1 == some 0
#guard (project movedContext ty).scalarCell 1 ty == some (⟨0,true⟩,⟨ty,7⟩)
#guard (project movedContext ty).vectorSlot 0 == some 2
#guard ((project movedContext ty).frame.resolve 2 (.integer ty)).map (fun pair => pair.2.items) == some []
#guard ((project movedContext ty).frame.resolve 5 (.integer ty)).map (fun pair => pair.2.items) == some [.integer 10,.integer 11]
example := project_work movedContext ty
example := project_scalarCell movedContext ty ty 1
example := project_charge movedContext ty 1 1
example := project_view_ready movedContext ty 3 3 ⟨1,true⟩ ⟨some 0,0,true,8⟩ rfl rfl (by decide)
  transferredUnique transferredCovered (by decide) transferredValid

def sourceArgument := (captureBorrow initialContext 0 true).getD ⟨999,false⟩
def targetArgument := (captureBorrow initialContext 3 true).getD ⟨999,false⟩
#guard sourceArgument.header == 0 && targetArgument.header == 1
#guard (captureBorrow initialContext 2 true).isNone
#guard (captureBorrow initialContext 2 false).map (fun arg => arg.header) == some 0
def boundSource := (installBorrow movedContext sourceArgument).getD (movedContext,0)
def boundTarget := (installBorrow movedContext targetArgument).getD (movedContext,0)
#guard boundSource.2 == 4 && boundTarget.2 == 4
#guard (project boundSource.1 ty).vectorSlot boundSource.2 == some 6
#guard ((project boundSource.1 ty).frame.resolve 6 (.integer ty)).map (fun pair => pair.2.items) == some []
#guard ((project boundTarget.1 ty).frame.resolve 6 (.integer ty)).map (fun pair => pair.2.items) == some [.integer 10,.integer 11]
example := captureBorrow_runs initialContext 0 0 true ⟨0,true⟩ ⟨some 0,1,true,8⟩ rfl rfl (by simp)
example := installBorrow_runs movedContext sourceArgument ⟨none,1,true,8⟩ rfl (by simp)

example := installBorrow_ready movedContext sourceArgument ⟨none,1,true,8⟩ ty rfl (by simp) (by decide)
  transferredUnique transferredCovered (by decide) transferredValid
example := installBorrow_ready movedContext targetArgument ⟨some 0,0,true,8⟩ ty rfl (by simp) (by decide)
  transferredUnique transferredCovered (by decide) transferredValid

-- Caller scope is newer than all existing object scopes; callee gets scope 3.
def callerContext : Context := {movedContext with scope := 2}
def scalarArgument := (captureScalarReference callerContext ty 1 true).getD (.scalar ⟨ty,false,false⟩ (.value 0))
def arguments : List SavedArgument := [.scalar ⟨ty,false,true⟩ (.value 3),scalarArgument,.vector sourceArgument,.vector targetArgument]
def prepared := (prepareSaved callerContext arguments).getD callerContext
#guard (prepareSaved callerContext arguments).isSome
#guard prepared.scope == 3 && prepared.slots.length == 4
#guard prepared.scalars.memory.length == 8 && prepared.scalars.bindings.length == 2
#guard (project prepared ty).scalarCell 0 ty == some (⟨5,true⟩,⟨ty,3⟩)
#guard (project prepared ty).scalarCell 1 ty == some (⟨0,true⟩,⟨ty,7⟩)
#guard (project prepared ty).vectorSlot 2 == some 6
#guard (project prepared ty).vectorSlot 3 == some 7
#guard ((project prepared ty).frame.resolve 6 (.integer ty)).map (fun pair => pair.2.items) == some []
#guard ((project prepared ty).frame.resolve 7 (.integer ty)).map (fun pair => pair.2.items) == some [.integer 10,.integer 11]
def assignedScalar := ((Proofs.CppState.Stmt.assign 1 (.literal ty 9)).run prepared.scalars).map (fun step => step.state)
def assignedValue := ((Proofs.CppState.Stmt.assign 0 (.literal ty 9)).run prepared.scalars).map (fun step => step.state)
#guard assignedScalar.bind (fun state => state.memory[0]?) == some ⟨ty,9⟩
#guard assignedValue.bind (fun state => state.memory[0]?) == some ⟨ty,7⟩
def calleeChanged : Context := {prepared with scalars := assignedScalar.getD prepared.scalars}
def finished := (finishBorrowed callerContext calleeChanged).getD callerContext
#guard (finishBorrowed callerContext calleeChanged).isSome
#guard finished.slots == callerContext.slots && finished.scope == callerContext.scope
#guard finished.scalars.memory.length == 1 && finished.scalars.bindings == callerContext.scalars.bindings
#guard (project finished ty).scalarCell 1 ty == some (⟨0,true⟩,⟨ty,9⟩)
def manyGhosts : Context := {callerContext with objects := ⟨{callerContext.objects.heap with grants := callerContext.objects.heap.grants++callerContext.objects.heap.grants},callerContext.objects.views++callerContext.objects.views⟩}
#guard (prepareBase manyGhosts 4).scalars.memory.length == (prepareBase callerContext 4).scalars.memory.length
#guard ((prepareSaved manyGhosts arguments).map (fun c => c.scalars.memory.length)) == some 8
#guard (prepareSaved callerContext [.scalar ⟨ty,false,true⟩ (.value (2^63))]).isNone
#guard (prepareSaved callerContext [.scalar ⟨ty,true,true⟩ (.value 3)]).isNone
def invalidExit : Context := {calleeChanged with scope := 1}
#guard (finishBorrowed callerContext invalidExit).isNone
example := prepareBase_memory callerContext 4
example := prepareBase_existing_cell callerContext 4 0 ⟨ty,7⟩ rfl

theorem preparedRun : prepareSaved callerContext arguments = some prepared := by
  have live : (prepareSaved callerContext arguments).isSome = true := by decide +kernel
  have nonempty : prepareSaved callerContext arguments ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty callerContext).symm
theorem finishedRun : finishBorrowed callerContext calleeChanged = some finished := by
  have live : (finishBorrowed callerContext calleeChanged).isSome = true := by decide +kernel
  have nonempty : finishBorrowed callerContext calleeChanged ≠ none := by intro missing; simp [missing] at live
  exact (Option.getD_of_ne_none nonempty callerContext).symm
example := prepareSaved_effects callerContext prepared arguments preparedRun
example := finishBorrowed_metadata callerContext calleeChanged finished finishedRun
def readonlyCaller : Context := {callerContext with scalars := {callerContext.scalars with bindings := [⟨0,false⟩]}}
#guard (captureScalarReference readonlyCaller ty 1 true).isNone
#guard (captureScalarReference readonlyCaller ty 1 false).isSome

example := finishBorrowed_aliases callerContext calleeChanged finished finishedRun
example := finishBorrowed_cell callerContext calleeChanged finished 0 ⟨ty,7⟩ ⟨ty,9⟩ finishedRun rfl (by decide +kernel)
example := finishBorrowed_scalarCell callerContext calleeChanged finished ty ty 1 0 ⟨0,true⟩ ⟨ty,7⟩ ⟨ty,9⟩
  finishedRun rfl rfl rfl (by decide +kernel) rfl (by decide)

def arithmetic : Proofs.CppNestedProgram.NExpr := .binary ty .add (.variable ty 1) (.read ty (.local 3) (.literal ty 0))
def sizeExpression : Proofs.CppNestedProgram.NExpr := .size (.integer ty) (.local 3)
def unsignedTy : Proofs.CppScalar.Ty := ⟨64,false,false⟩
def expressionParameters : List Proofs.CppVectorBindings.Parameter :=
  [.scalar ty false true,.scalar ty true true,.vector ty false,.vector ty true,.scalar unsignedTy false false]
def expressionArguments : List Proofs.CppNestedCall.NArgument :=
  [.value arithmetic,.scalarReference 1,.vectorReference 2,.vectorReference 3,.value sizeExpression]
def expressionPrepared := (prepareArguments callerContext ty expressionParameters expressionArguments).getD callerContext
#guard (evalExpression callerContext ty arithmetic).map Prod.snd == some 17
#guard (evalExpression callerContext ty sizeExpression).map Prod.snd == some 2
#guard (prepareArguments callerContext ty expressionParameters expressionArguments).isSome
#guard (project expressionPrepared ty).scalarCell 0 ty == some (⟨5,true⟩,⟨ty,17⟩)
#guard (project expressionPrepared ty).scalarCell 1 ty == some (⟨0,true⟩,⟨ty,7⟩)
#guard (project expressionPrepared ty).scalarCell 4 unsignedTy == some (⟨8,false⟩,⟨unsignedTy,2⟩)
#guard expressionPrepared.scalars.memory.length == 9 && expressionPrepared.slots.length == 5
#guard ((project expressionPrepared ty).frame.resolve 6 (.integer ty)).map (fun pair => (pair.1.writable,pair.2.items)) == some (false,[])
#guard ((project expressionPrepared ty).frame.resolve 7 (.integer ty)).map (fun pair => pair.2.items) == some [.integer 10,.integer 11]
#guard (prepareArguments callerContext ty expressionParameters []).isNone
#guard (prepareArguments callerContext ty [.scalar ty false true] [.value (.literal unsignedTy 3)]).isNone
#guard (prepareArguments callerContext ty [.vector ty true] [.vectorReference 2]).isNone
#guard (prepareArguments callerContext ty [.scalar ty false true] [.value (.read ty (.local 3) (.literal ty 99))]).isNone
example := evalExpression_correspondence callerContext ty arithmetic
example := evalExpression_correspondence callerContext ty sizeExpression

example := bindSaved_ready callerContext (.scalar ⟨ty,false,true⟩ (.value 3)) ⟨rfl,by decide⟩
example := bindSaved_ready callerContext (.scalar ⟨ty,true,true⟩ (.reference 0)) ⟨⟨ty,7⟩,rfl,rfl,rfl,by decide⟩
example := bindSaved_ready callerContext (.vector targetArgument) ⟨⟨some 0,0,true,8⟩,rfl,by simp⟩

theorem argumentsReady : ∀ argument ∈ arguments, SavedReady callerContext argument := by
  intro argument member
  simp only [arguments,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with eq | eq | eq | eq <;> subst argument
  · exact ⟨rfl,by decide⟩
  · have snapshot : scalarArgument = .scalar ⟨ty,true,true⟩ (.reference 0) := by decide +kernel
    rw [snapshot]
    exact ⟨⟨ty,7⟩,rfl,rfl,rfl,by decide⟩
  · exact ⟨⟨none,1,true,8⟩,rfl,by simp⟩
  · exact ⟨⟨some 0,0,true,8⟩,rfl,by simp⟩
example := prepareSaved_ready callerContext arguments argumentsReady
example := prepareSaved_resources callerContext prepared arguments preparedRun
#guard work prepared == work callerContext+1+arguments.length
#guard (prepareBase callerContext 0).scalars.peak >= callerContext.scalars.memory.length+callerContext.slots.length
#guard (prepareBase manyGhosts 0).scalars.peak == (prepareBase callerContext 0).scalars.peak

example := prepareSaved_peak callerContext prepared arguments preparedRun
example := prepareSaved_scalarLive callerContext prepared arguments preparedRun (by decide)
example := prepareSaved_peak_linear callerContext prepared arguments preparedRun (by decide)
#guard prepared.peak == 18
#guard (prepareSaved manyGhosts arguments).map (fun c => c.peak) == some 18
def baselineCaller : Context := {callerContext with scalars := {callerContext.scalars with baseMemory := 1}}
#guard (prepareSaved baselineCaller arguments).map (fun c => c.peak) == some 17
def historicalCaller : Context := {callerContext with scalars := {callerContext.scalars with peak := 400},peak := 200}
#guard (prepareSaved historicalCaller arguments).map (fun c => c.peak) == some 408
end ContextExamples
'''

class MoveContextTests(unittest.TestCase):
    def test_projection_arguments_references_preparation_and_exit(self):
        with tempfile.TemporaryDirectory(prefix='move-context-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.CppMoveContext\n'+HEADER_CHECKS+FRAME_CHECKS+WRITE_CHECKS+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)

if __name__=='__main__':
    disable_network()
    unittest.main()
