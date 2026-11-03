"""Original UnionFind assertion domains, including the sentinel and both arguments."""
from pathlib import Path
import os
import resource
import signal
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from check_public import FLAGS, check_compiler
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
HEADER = '''import Proofs.UnionFindCall
import Proofs.UfBounds
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore Proofs.CppVectorOwnership
open Proofs.CppLoop Proofs.VecStraight Proofs.VecWrite Proofs.StraightLine Proofs.VecExpr
 def intTy : Ty := ⟨32,true,false⟩
 def atom : Element := .integer intTy
 def initial (n : Nat) (constructor : Bool) : List Int :=
   if constructor then List.replicate (n+1) (-1) else List.replicate n (-1) ++ [-1-(n : Int)]
 def caller (items : List Int) : NState :=
   let buffer : Proofs.CppVector.Buffer Value := ⟨0,items.map Value.integer,items.length+1,64,0⟩
   let heap : Proofs.CppNestedVectorStore.State :=
     ⟨⟨[some ⟨atom,none,some 0,[]⟩]⟩,⟨[some buffer],0,0,0⟩⟩
   { scalars := ⟨[],[],0,0,0⟩,frame := ⟨heap,[true],[⟨0,atom,true,.root 0⟩]⟩,slots := [.vector 0] }
 def answer (o : Outcome (NState × Ret)) : Option Int :=
   match o with | .finished (_, .scalar x) => some x | _ => none
 example (ps : PS) (vec : List Int) (j : Nat) (a : Int) (body : Command) (fuel : Nat)
   (value : penv1 ps j Proofs.DoublingNested.i32 = some a)
   (length : vec.length < 2147483648) (nonempty : 0 < vec.length)
   (invalid : a < 0 ∨ (vec.length : Int) ≤ a+1) :
   pexecW Proofs.DoublingNested.i32 fuel (Proofs.UfBounds.bounds j body) ps vec = none :=
   Proofs.UfBounds.reject_bounds ps vec j a body fuel value length nonempty invalid
'''


def cases():
    inputs = (ROOT/'tests/imports/union_find_bounds/in/cases.txt').read_text().splitlines()
    outputs = (ROOT/'tests/imports/union_find_bounds/out/cases.txt').read_text().splitlines()
    if len(inputs) != len(outputs):
        raise AssertionError('input/output case count mismatch')
    return [(line.split(), expected) for line, expected in zip(inputs, outputs)]


class UnionFindBoundsTests(unittest.TestCase):
    def test_assertions_match_generated_model_and_native(self):
        checks = [HEADER]
        entries = cases()
        for index, (args, expected) in enumerate(entries):
            method, n, a, b = args
            ctor = method == 'new'
            # Constructor models start after field initialization, as documented.
            items = '[]' if int(n) < 0 else f'(initial {n} {str(ctor).lower()})'
            values = [n] if ctor else [a,b] if method in ('same','unite') else [a]
            model = 'UnionFind_new1' if ctor else 'UnionFind_'+method
            actual_args = ','.join(['.vectorReference 0'] + [f'.value (.literal intTy ({v}))' for v in values])
            name = f'case{index}'
            checks.append(f'def {name} := Proofs.UnionFindInstance.{model}.callFuel 128 (caller {items}) [{actual_args}]')
            if expected == 'ABORT':
                checks.append(f'#guard {name} == .fault')
            elif ctor:
                checks.append(f'#guard (match {name} with | .finished (s,.unit) => (s.frame.state.storage.lookup 0).map (·.items) == some ((initial {n} false).map Value.integer) | _ => false)')
            else:
                checks.append(f'#guard answer {name} == some ({expected})')
        # Ignoring the guards exposes the sentinel as an ordinary root. This is
        # a valid vector access, so bounds checking on reads alone cannot replace assert.
        checks += ['def unchecked := {Proofs.UnionFindInstance.UnionFind_root with body := Proofs.UfFindCall.bodyF}',
                   '#guard answer (unchecked.callFuel 128 (caller (initial 0 false)) [.vectorReference 0,.value (.literal intTy 0)]) == some 0']
        with tempfile.TemporaryDirectory(prefix='union-find-bounds-') as directory:
            scratch = Path(directory)
            lean = scratch/'checks.lean'; lean.write_text('\n'.join(checks)+'\n')
            lake, env = lean_environment()
            result = subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler()
            exe = scratch/'bounds'
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-sanitize-recover=all',
                            '-fno-omit-frame-pointer','-fno-pie','-no-pie',
                            str(ROOT/'tests/imports/union_find_bounds.cpp'),'-o',str(exe)],cwd=ROOT,check=True)
            native_env = os.environ.copy()
            native_env['ASAN_OPTIONS'] = 'detect_leaks=0:halt_on_error=1'
            native_env['UBSAN_OPTIONS'] = 'halt_on_error=1:print_stacktrace=1'
            for args, expected in entries:
                with self.subTest(args=args):
                    result = subprocess.run([str(exe),*args],env=native_env,capture_output=True,text=True,
                                            preexec_fn=lambda: resource.setrlimit(resource.RLIMIT_CORE,(0,0)))
                    if expected == 'ABORT':
                        self.assertEqual(result.returncode,-signal.SIGABRT,result.stdout+result.stderr)
                        self.assertIn('Assertion',result.stderr)
                        self.assertNotIn('runtime error:',result.stderr)
                        self.assertNotIn('ERROR: AddressSanitizer',result.stderr)
                    else:
                        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
                        self.assertEqual(result.stdout.strip(),expected)
        print(f'UnionFind bounds: {len(entries)} generated Lean/native ASan/UBSan cases; general invalid-index rejection')


if __name__ == '__main__':
    disable_network(); unittest.main()
