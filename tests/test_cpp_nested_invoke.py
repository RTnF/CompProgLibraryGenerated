"""Nested scalar calls: mixed real methods, early returns, result locals, cleanup."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'tests'),str(ROOT/'verifier'),str(ROOT/'tools')]
from test_scalar_ir import lean_environment
from test_union_find_construction import HEADER
from test_union_find_original_api import HEADER as CALLER_HEADER, SOURCE
from test_union_find_construction_footprint import CHECKS as STAGE
from test_union_find_constructed_receiver import CHECKS as RECEIVER
from test_union_find_receiver_trace import CHECKS as TRACE, OPS, EXPECTED
from offline import disable_network

CHECKS = r'''
open Proofs.CppNestedInvoke
example := Proofs.UfCallerTrace.invocations_preserve mixed built (layoutOf populated)
  (List.replicate 4 (-1)) 4 (fun _ => 0) builtRep (by simpa using mixedAllowed)
#guard (match Proofs.UfCallerTrace.runInvocations (List.replicate mixed.length 128) mixed
    built (layoutOf populated) with
  | .finished (s,answers) => answers == ([4,0,2,0,2,0,0,1,4,1,0,1] : List Int) &&
      s.slots.length == built.slots.length+mixed.length
  | _ => false)
def invokeTrace : List Operation → NState → Outcome (NState × List (Nat × Ty × Int))
  | [],s => .finished (s,[])
  | op::ops,s => do
    let .scalar ty := op.program.result | .fault
    let step ← invokeScalarFuel op.program 128 s (arguments (layoutOf populated) ++ op.extra)
    if step.returned.isSome || step.breaking then .fault else do
    let (_,cell) ← liftChecked (step.state.scalarCell s.slots.length ty)
    let (out,answers) ← invokeTrace ops step.state
    pure (out,(s.slots.length,ty,cell.value)::answers)
def invoked := invokeTrace mixed built
#guard (match invoked with
  | .finished (s,answers) =>
    answers.map (fun (_,_,v) => v) == ([4,0,2,0,2,0,0,1,4,1,0,1] : List Int) &&
    answers.all (fun (slot,ty,v) => match s.scalarCell slot ty with
      | some (b,c) => !b.writable && c.value == v
      | none => false) &&
    s.slots.length == built.slots.length+mixed.length &&
    s.scalars.memory.take built.scalars.memory.length ==
      [⟨i32,2⟩,⟨i32,9876⟩,⟨i32,1⟩,⟨i32,4⟩] &&
    (s.frame.state.storage.lookup 1).map (·.items) == some ([-4,0,0,0].map Value.integer) &&
    s.frame.state.storage.lookup 0 == populated.frame.state.storage.lookup 0 &&
    saved.bind s.frame.read == some (-1) &&
    -- The method's early return does not return from the enclosing caller.
    (match Proofs.CppNestedProgram.runFuel 2
      (.primitive (.ret (.variable i32 (s.slots.length-1)))) s with
      | .finished step => step.returned == some (.scalar 1)
      | _ => false) &&
    -- Hidden result locals cannot be assigned through an ordinary reference.
    (NStmt.assign built.slots.length i32 (.literal i32 99)).run s == none
  | _ => false)
#guard invokeScalarFuel (Operation.root 4).program 128 built
  (arguments (layoutOf populated) ++ (Operation.root 4).extra) == .fault
#guard invokeScalarFuel Operation.numGroups.program 0 built (arguments (layoutOf populated)) == .exhausted

-- A local vector allocated before an early return must die in the callee.
def allocating : NProgram := ⟨[],.scalar i32,
  .sequence (.primitive (.fillVector i32 true (.literal i32 3) (.literal i32 7)))
    (.sequence (.primitive (.ret (.literal i32 23)))
      (.primitive (.check (.literal i32 0))))⟩
#guard (match invokeScalarFuel allocating 8 built [] with
  | .finished step => step.returned == none && !step.breaking &&
    step.state.scalarCell built.slots.length i32 ==
      some (⟨built.scalars.memory.length,false⟩,⟨i32,23⟩) &&
    step.state.scope == built.scope &&
    step.state.frame.bindings == built.frame.bindings &&
    step.state.frame.state.storage.lookup 2 == none &&
    saved.bind step.state.frame.read == some (-1) &&
    step.state.frame.state.storage.lookup 1 == built.frame.state.storage.lookup 1
  | _ => false)

def traceCommand : List Operation → CallerCommand
  | [] => .nested (.primitive (.ret (.variable i32 (built.slots.length+mixed.length-1))))
  | op::ops => .sequence (.invoke op.program (arguments (layoutOf populated) ++ op.extra))
      (traceCommand ops)
#guard (match runCallerFuel 256 (traceCommand mixed) built with
  | .finished step => step.returned == some (.scalar 1) && !step.breaking &&
      (match invoked with
      | .finished (s,_) => step.state.scalars.memory == s.scalars.memory &&
          step.state.frame == s.frame
      | _ => false)
  | _ => false)
def scopedUnite : CallerCommand := .scope (.invoke (Operation.unite 0 1).program
  (arguments (layoutOf populated) ++ (Operation.unite 0 1).extra))
#guard (match runCallerFuel 256 scopedUnite built with
  | .finished step => step.returned == none && !step.breaking &&
      step.state.slots == built.slots && step.state.scalars.bindings == built.scalars.bindings &&
      step.state.scalars.memory.length == built.scalars.memory.length && step.state.scope == built.scope &&
      (step.state.frame.state.storage.lookup 1).map (·.items) == some ([-2,0,-1,-1].map Value.integer)
  | _ => false)
-- Results from each iteration are scoped; the counter alias is updated in place.
def loopCalls : CallerCommand := .whileLoop
  (.binary i32 .lt (.variable i32 3) (.literal i32 3))
  (.scope (.sequence
    (.invoke Operation.numGroups.program (arguments (layoutOf populated)))
    (.nested (.primitive (.assign 3 i32 (.binary i32 .add (.variable i32 3) (.literal i32 1)))))))
#guard (match (NStmt.assign 3 i32 (.literal i32 0)).run built with
  | some entry => match runCallerFuel 256 loopCalls entry.state with
    | .finished step => step.returned == none && !step.breaking && step.state.slots == built.slots &&
        (step.state.scalarCell 3 i32).map (fun (_,c) => c.value) == some (3 : Int) &&
        step.state.scalars.memory.length == built.scalars.memory.length
    | _ => false
  | _ => false)
#guard (match runCallerFuel 256
  (.whileLoop (.literal i32 1) (.branch (.literal i32 1) .breakLoop
    (.nested (.primitive (.check (.literal i32 0)))))) built with
  | .finished step => step.returned == none && !step.breaking
  | _ => false)
#guard (match runCallerFuel 256 (.sequence
    (.nested (.primitive (.ret (.literal i32 9)) ))
    (.nested (.primitive (.check (.literal i32 0))))) built with
  | .finished step => step.returned == some (.scalar 9)
  | _ => false)
def badReturn : NProgram := ⟨[],.scalar ⟨1,false,true⟩,
  .primitive (.ret (.literal i32 2))⟩
#guard invokeScalarFuel badReturn 4 built [] == .fault
example (p : NProgram) (f : Nat) (s t : NState) (args : List NArgument) (ty : Ty) (v : Int)
    (kind : p.result = .scalar ty) (ran : p.callFuel f s args = .finished (t,.scalar v)) :=
  invoke_result p f s t args ty v kind ran
'''

class NestedInvokeTests(unittest.TestCase):
    def test_mixed_calls_result_lifetimes_and_early_return(self):
        with tempfile.TemporaryDirectory(prefix='nested-invoke-') as directory:
            proof=Path(directory)/'checks.lean'
            proof.write_text('import Proofs.UfCallerTrace\n'+HEADER+CALLER_HEADER+STAGE+RECEIVER+TRACE+CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            native=Path(directory)/'native.cpp';binary=Path(directory)/'native'
            calls=''.join(f'std::cout << u.{name}({",".join(map(str,args))}) << " ";' for name,args in OPS)
            native.write_text(f'#include "{SOURCE}"\n#include <iostream>\nint main(){{cp::UnionFind u(4);'+calls+'}')
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',str(native),'-o',str(binary)],check=True)
            result=subprocess.run([str(binary)],check=True,capture_output=True,text=True)
            self.assertEqual(list(map(int,result.stdout.split())),EXPECTED)

if __name__ == '__main__':
    disable_network()
    unittest.main()
