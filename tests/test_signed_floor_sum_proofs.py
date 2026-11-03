"""Whole signed source, all-input call proofs, C++ comparisons and mutations."""
from pathlib import Path
import os
import re
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'verifier'))
sys.path.insert(0,str(ROOT/'tools'))
from state_ir import lower_source,emit_lean
from scalar_ir import SIGNED_CONVERSIONS
from test_scalar_ir import lean_environment
from offline import disable_network

SOURCE=ROOT/'experiments/library/cpp/number_theory/floor_sum.hpp'
INCLUDES=[ROOT/'experiments/library/cpp']
NAMESPACE='Proofs.FloorSumSignedInstance'
I64_MIN=-(1<<63);I64_MAX=(1<<63)-1


def generated(source):
    return emit_lean(lower_source(source,None,INCLUDES,SIGNED_CONVERSIONS[1]),NAMESPACE)


def cpp_literal(x):
    return '(-9223372036854775807LL-1)' if x==I64_MIN else f'({x}LL)'


class SignedFloorSumProofTests(unittest.TestCase):
    def test_whole_generated_call_proofs_and_cpp(self):
        model=generated(SOURCE)
        self.assertEqual(model,(ROOT/'Proofs/Generated/FloorSumSigned.lean').read_text())
        lake,env=lean_environment()
        proof='''import Proofs.FloorSumSignedSpecification
open Proofs.CppScalar Proofs.CppState Proofs.CppLoop Proofs.SafeModProofs
open Proofs.FloorSumSignedSpecification Proofs.FloorSumSignedArithmetic Proofs.FloorSumArithmetic
-- The caller may even contain invalid, unbound cells; the function cannot read them.
def callerCells : List Cell := [⟨signed64,-8⟩,⟨⟨64,false,false⟩,18446744073709551615⟩,⟨⟨1,false,true⟩,3⟩]
'''
        pairs=[(I64_MIN,I64_MIN),(I64_MIN,I64_MAX),(I64_MAX,I64_MIN),(I64_MAX,I64_MAX),(-7,11),(0,-1),(0,0)]
        cases=[(n,m,a,b,sum((a*i+b)//m for i in range(n))) for n in [0,1,2,3]
               for m in [1,2,4294967295] for a,b in pairs]
        cases += [(4294967295,1,a,b,a*4294967295*4294967294//2+b*4294967295) for a,b in pairs]
        native='#include <cassert>\n#include "number_theory/floor_sum.hpp"\nint main(){\n'
        for n,m,a,b,total in cases:
            residue=total%(1<<64);value=residue if residue<(1<<63) else residue-(1<<64)
            proof+=f'example : ∃ work peak, Proofs.FloorSumSignedInstance.floor_sum.callFuel 846 callerCells [.value {n},.value {m},.value ({a}),.value ({b})] = .finished ⟨({value}),callerCells,work,peak⟩ ∧ work ≤ 4378 ∧ peak ≤ 35 := by\n'
            proof+=f'  obtain ⟨w,p,done,hw,hp,_⟩ := call_correct {n} {m} ({a}) ({b}) callerCells (by decide) (by decide) (by decide) (by decide) (by decide)\n'
            formulas='signedSum_modulus_one,triangle,' if m==1 else 'signedSum,'
            proof+=f'  exact ⟨w,p,by simpa [{formulas}signedDecode64,wordLimit] using done,hw,hp⟩\n'
            proof+=f'#guard (match Proofs.FloorSumSignedInstance.floor_sum.callFuel 846 callerCells [.value {n},.value {m},.value ({a}),.value ({b})] with | .finished result => result.value == ({value}) && result.memory == callerCells && result.work ≤ 4378 && result.peak ≤ 35 | _ => false)\n'
            native+=f'assert(floor_sum({n}LL,{m}LL,{cpp_literal(a)},{cpp_literal(b)})=={cpp_literal(value)});\n'
        proof+='''example : ∃ work peak, Proofs.FloorSumSignedInstance.floor_sum.callFuel 846 callerCells
    [.value 3,.value 2,.value (-7),.value 11] = .finished ⟨5,callerCells,work,peak⟩ ∧ work ≤ 4378 ∧ peak ≤ 35 ∧ work ≤ 154+132*(Nat.log2 2+1) := by
  have exactSum : signedSum 2 (-7) 11 3 = 5 := by decide
  simpa [signedSum] using call_exact_if_representable 3 2 (-7) 11 callerCells
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
#guard Proofs.FloorSumSignedInstance.floor_sum.callFuel 0 callerCells [.value 1,.value 1,.value 0,.value 0] == .exhausted
#guard Proofs.FloorSumSignedInstance.floor_sum.callFuel 846 callerCells [.value (-1),.value 1,.value 0,.value 0] == .fault
#guard Proofs.FloorSumSignedInstance.floor_sum.callFuel 846 callerCells [.value 1,.value 0,.value 0,.value 0] == .fault
'''
        native+='}\n'
        with tempfile.TemporaryDirectory(prefix='signed-whole-call-') as directory:
            scratch=Path(directory);lean=scratch/'tests.lean';lean.write_text(proof)
            checked=subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(checked.returncode,0,checked.stdout+checked.stderr)
            cpp=scratch/'native.cpp';binary=scratch/'native';cpp.write_text(native)
            subprocess.run(['g++','-std=c++17','-O1','-g','-fsanitize=address,undefined','-fno-sanitize-recover=all',
                '-I',str(INCLUDES[0]),str(cpp),'-o',str(binary)],check=True)
            # LeakSanitizer cannot inspect processes in the sandbox; retain
            # address and undefined-behavior checks, as in check_public.py.
            native_env=os.environ.copy()
            native_env['ASAN_OPTIONS']='detect_leaks=0:halt_on_error=1'
            subprocess.run([str(binary)],check=True,env=native_env)

    def test_source_mutations_invalidate_whole_call_proofs(self):
        original=SOURCE.read_text()
        call_proof=re.sub(r'^import .*\n','',(ROOT/'Proofs/FloorSumSignedCall.lean').read_text(),flags=re.M)
        specification=re.sub(r'^import .*\n','',(ROOT/'Proofs/FloorSumSignedSpecification.lean').read_text(),flags=re.M)
        lake,env=lean_environment()
        changes=[None,('return ans + floor_sum_unsigned','return ans - floor_sum_unsigned'),
                 ('floor_sum_unsigned(n, m, a, b)','floor_sum_unsigned(n, m, b, a)'),
                 ('a * n + b','a * n - b'),('x %= m','x /= m')]
        with tempfile.TemporaryDirectory(prefix='signed-whole-mutations-') as directory:
            scratch=Path(directory);source=scratch/'changed.hpp';lean=scratch/'proofs.lean'
            for change in changes:
                with self.subTest(change=change):
                    modified=original if change is None else original.replace(*change)
                    if change is not None:self.assertNotEqual(modified,original)
                    source.write_text(modified)
                    # Reprove against the regenerated body in a new Lean file.
                    # Return imports the shared callee proofs, but not this generated signed module.
                    lean.write_text('import Proofs.FloorSumSignedReturn\n'+generated(source)+call_proof+specification)
                    checked=subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
                    if change is None:self.assertEqual(checked.returncode,0,checked.stdout+checked.stderr)
                    else:self.assertNotEqual(checked.returncode,0)


if __name__=='__main__':
    disable_network();lake,env=lean_environment()
    subprocess.run([lake,'build','Proofs.FloorSumSignedSpecification'],cwd=ROOT,env=env,check=True)
    unittest.main()
