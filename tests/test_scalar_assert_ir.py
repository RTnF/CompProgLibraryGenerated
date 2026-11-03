"""Standard assertions retain false failures, short circuiting and source guards."""

from pathlib import Path
import resource
import signal
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
sys.path.insert(0, str(ROOT / 'tools'))
from state_ir import lower_source, emit_lean
from scalar_ir import source_ast
from scalar_assert import verify_scalar_asserts
from scalar_stl import walk
from test_scalar_ir import lean_environment
from offline import disable_network


class AssertionTests(unittest.TestCase):
    def test_conditions_failures_short_circuit_and_source_mutation(self):
        source_text = '''#include <cassert>
namespace cp {
long long bounds(long long x) { assert(0 <= x && x < (1ll << 32)); return x; }
int disjunction(int x) { assert(x == 0 || 10 / x > 0); return x; }
int conjunction(int x) { assert(x != 0 && 10 / x > 0); return x; }
int loop(int x) { while (x > 0) { assert(x <= 3); x -= 1; } return x; }
}
'''
        with tempfile.TemporaryDirectory(prefix='scalar-assert-') as directory:
            scratch = Path(directory)
            source = scratch / 'source.cpp'
            source.write_text(source_text)
            ir = lower_source(source)
            generated = emit_lean(ir, 'AssertTest')
            self.assertIn('.check', generated)
            self.assertIn('(.literal ⟨64, true, false⟩ (4294967296))', generated)
            lake, env = lean_environment()
            checks = '''
#guard (AssertTest.bounds.call [] [.value 0]).map (·.value) == some 0
#guard (AssertTest.bounds.call [] [.value 4294967295]).map (·.value) == some 4294967295
#guard AssertTest.bounds.call [] [.value (-1)] == none
#guard AssertTest.bounds.call [] [.value 4294967296] == none
#guard (AssertTest.disjunction.call [] [.value 0]).map (·.value) == some 0
#guard (AssertTest.disjunction.call [] [.value 2]).map (·.value) == some 2
#guard AssertTest.disjunction.call [] [.value (-1)] == none
#guard AssertTest.conjunction.call [] [.value 0] == none
#guard (AssertTest.conjunction.call [] [.value 2]).map (·.value) == some 2
#guard (match AssertTest.loop.callFuel 30 [] [.value 3] with | .finished r => r.value == 0 | _ => false)
#guard AssertTest.loop.callFuel 20 [] [.value 4] == .fault
'''
            proof = scratch / 'test.lean'
            proof.write_text(generated + '\n' + checks)
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            source.write_text(source_text.replace('x < (1ll << 32)', 'x <= (1ll << 32)'))
            changed = emit_lean(lower_source(source),'AssertTest')
            self.assertNotEqual(changed, generated)
            proof.write_text(changed+'\n#guard AssertTest.bounds.call [] [.value 4294967296] == none\n')
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertNotEqual(result.returncode,0)
            self.assertIn('did not evaluate to `true`',result.stdout+result.stderr)
            source.write_text(source_text+'''int main(int argc,char**) {
if(argc == 1) { assert(cp::bounds(4294967295LL)==4294967295LL); assert(cp::disjunction(0)==0);
assert(cp::conjunction(2)==2); assert(cp::loop(3)==0); }
else { cp::conjunction(0); }
}''')
            binary = scratch/'test'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                            str(source),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)
            resource.setrlimit(resource.RLIMIT_CORE,(0,0))
            rejected = subprocess.run([str(binary),'false'],capture_output=True,text=True)
            self.assertEqual(rejected.returncode,-signal.SIGABRT)
            self.assertIn('Assertion',rejected.stderr)
            self.assertNotIn('runtime error',rejected.stderr)

    def test_user_assert_macros_shadowed_failures_and_disabled_asserts_are_rejected(self):
        sources = [
            '#include <cassert>\n#undef assert\n#define assert(x) ((x)?(void)0:__assert_fail("x","x",1,"x"))\nnamespace cp {int f(int x){assert(x);return x;}}',
            '#include <cassert>\nnamespace cp {void __assert_fail(const char*,const char*,unsigned int,const char*); int f(int x){assert(x);return x;}}',
            '#include <cassert>\nextern "C" void __assert_fail(const char*,const char*,unsigned int,const char*) noexcept {}\nnamespace cp {int f(int x){assert(x);return x;}}',
            '#define NDEBUG\n#include <cassert>\nnamespace cp {int f(int x){assert(x);return x;}}',
            '#include <cassert>\nnamespace cp {int f(int x){assert(x<<1);return x;}}',
        ]
        with tempfile.TemporaryDirectory() as directory:
            source=Path(directory)/'source.cpp'
            for text in sources:
                with self.subTest(source=text):
                    source.write_text(text)
                    with self.assertRaises(ValueError):lower_source(source)

    def test_original_signed_assertions_are_recognized_but_missing_callee_is_rejected(self):
        source=ROOT/'experiments/library/cpp/number_theory/floor_sum.hpp'
        includes=[ROOT/'experiments/library/cpp']
        nodes=source_ast(source,'floor_sum',includes)
        verify_scalar_asserts(source,nodes,includes)
        self.assertEqual(sum(bool(n.get('verifiedScalarAssert')) for root in nodes for n in walk(root)),2)
        with self.assertRaisesRegex(ValueError,'call requires a definition in the selected AST'):
            lower_source(source,'floor_sum',includes)


if __name__ == '__main__':
    disable_network()
    lake,env=lean_environment()
    subprocess.run([lake,'build','Proofs.CppLoop'],cwd=ROOT,env=env,check=True)
    unittest.main()
