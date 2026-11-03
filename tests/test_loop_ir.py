"""Generated loop semantics: scopes, return, fuel exhaustion and faults."""

from pathlib import Path
from math import gcd
import subprocess
import re
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verifier"))
sys.path.insert(0, str(ROOT / "tools"))
from state_ir import lower_source, emit_lean, statement
from test_scalar_ir import lean_environment
from offline import disable_network


class LoopTests(unittest.TestCase):
    def test_cpp_and_generated_loop_results_and_outcomes(self):
        text = '''namespace cp {
int count(int &a) { while(a < 5) { a++; } return a; }
int sum(int n) { int result=0; for(int i=0;i<n;++i) { int x=i; result=result+x; } return result; }
int nested(int n) { int count=0; for(int i=0;i<n;i++){for(int j=0;j<i;j++){++count;}} return count; }
int early(int &a) { for(;;a++){ if(a == 2){return a;} } }
int scope(int n) { for(int i=0;i<n;++i) int x=9; int i=7; return i; }
int overflow(int &a) { while(a > 0) { ++a; } return a; }
int infinite(int a) { while(true) { ; } return a; }
int euclid(int a, int b) { while(b != 0) { int r=a % b; a=b; b=r; } return a; }
int halving(int a) { int steps=0; while(a != 0) { a=a/2; ++steps; } return steps; }
}
'''
        with tempfile.TemporaryDirectory(prefix="loop-check-") as directory:
            scratch = Path(directory)
            source = scratch / "source.cpp"
            source.write_text(text)
            ir = lower_source(source)
            generated = emit_lean(ir, "LoopTest")
            self.assertIn("LoopProgram", generated)
            lean = generated + "\nopen LoopTest Proofs.CppLoop Proofs.CppState\n"
            for n in range(0, 11):
                total = sum(range(n))
                lean += f"#guard (sum.callFuel 100 [] [.value {n}]) matches .finished r => r.value == {total} && r.memory.isEmpty\n"
                lean += f"#guard (nested.callFuel 100 [] [.value {n}]) matches .finished r => r.value == {total} && r.memory.isEmpty\n"
                lean += f"#guard (scope.callFuel 100 [] [.value {n}]) matches .finished r => r.value == 7 && r.memory.isEmpty\n"
                lean += f"#guard (euclid.callFuel 100 [] [.value {n}, .value {n+5}]) matches .finished r => r.value == {gcd(n,n+5)}\n"
                lean += f"#guard (halving.callFuel 100 [] [.value ({-n})]) matches .finished r => r.value == {n.bit_length()}\n"
            for n in range(-3, 9):
                lean += f"#guard (count.callFuel 100 [⟨⟨32,true,false⟩,{n}⟩] [.reference 0]) matches .finished r => r.value == {max(n,5)} && r.memory.map (·.value) == [{max(n,5)}]\n"
            lean += "#guard sum.callFuel 100 [] [.value 10] == sum.callFuel 200 [] [.value 10]\n"
            lean += '''#guard (early.callFuel 100 [⟨⟨32,true,false⟩,0⟩] [.reference 0]) matches .finished r => r.value == 2 && r.memory.map (·.value) == [2]
#guard sum.callFuel 1 [] [.value 10] == .exhausted
#guard infinite.callFuel 100 [] [.value 0] == .exhausted
#guard overflow.callFuel 100 [⟨⟨32,true,false⟩,2147483647⟩] [.reference 0] == .fault
#guard count.callFuel 100 [] [.reference 0] == .fault
'''
            lean = "\n".join(re.sub(r"#guard (.*) matches \.finished r => (.*)",
                        r"#guard (match \1 with | .finished r => \2 | _ => false)", line)
                        for line in lean.splitlines())
            proof = scratch / "test.lean"
            proof.write_text(lean)
            lake, env = lean_environment()
            subprocess.run([lake, "env", "lean", str(proof)], cwd=ROOT, env=env, check=True)
            cpp = scratch / "test.cpp"
            cpp.write_text("#include <cassert>\n#include <numeric>\n" + text + '''
int main() {
 for(int n=0;n<=10;n++){int expected=n*(n-1)/2; assert(cp::sum(n)==expected); assert(cp::nested(n)==expected); assert(cp::scope(n)==7);}
 for(int n=0;n<=10;n++){assert(cp::euclid(n,n+5)==std::gcd(n,n+5)); int steps=0; for(int k=n;k;k/=2)++steps; assert(cp::halving(-n)==steps);}
 for(int n=-3;n<=8;n++){int a=n; assert(cp::count(a)==(n<5?5:n)); assert(a==(n<5?5:n));}
 int a=0; assert(cp::early(a)==2); assert(a==2);
}
''')
            binary = scratch / "test"
            subprocess.run(["g++", "-std=c++17", "-O1", "-fsanitize=undefined",
                            "-fno-sanitize-recover=all", str(cpp), "-o", str(binary)], check=True)
            subprocess.run([str(binary)], check=True)

    def test_loop_boundary_and_update_mutations_fail_guards(self):
        original = ('namespace cp { int sum(int n) { int result=0; '
                    'for(int i=0;i<n;++i){result=result+i;} return result; } }')
        variants = [original, original.replace('i<n', 'i<=n'),
                    original.replace('++i', '--i'),
                    original.replace('result=result+i', 'result=result+1')]
        lake, env = lean_environment()
        with tempfile.TemporaryDirectory(prefix="loop-mutation-") as directory:
            scratch = Path(directory)
            source, proof = scratch / "test.cpp", scratch / "test.lean"
            for index, text in enumerate(variants):
                with self.subTest(variant=index):
                    source.write_text(text)
                    proof.write_text(emit_lean(lower_source(source), "MutationTest") +
                        '\n#guard (match MutationTest.sum.callFuel 100 [] [.value 4] with '
                        '| .finished r => r.value == 6 | _ => false)\n')
                    result = subprocess.run([lake, "env", "lean", str(proof)],
                        cwd=ROOT, env=env, capture_output=True, text=True)
                    if index == 0:
                        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                    else:
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn("did not evaluate to `true`", result.stdout + result.stderr)

    def test_loop_control_and_increment_expressions_are_refused(self):
        with self.assertRaisesRegex(ValueError, 'enclosing supported loop'):
            statement({'kind':'BreakStmt'}, {}, [])
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "test.cpp"
            for body in ['switch(a){case 1:break;} return a;', 'while(a){continue;} return a;',
                         'do{a=0;}while(a); return a;', 'return ++a;']:
                source.write_text('namespace cp { int f(int a){'+body+'} }')
                with self.subTest(body=body), self.assertRaises(ValueError):
                    lower_source(source)

    def test_break_scope_nested_loops_skipped_updates_and_cost(self):
        text = '''namespace cp {
int stopped(int &a){while(a<4){if(a>=2)break;++a;}return a;}
int update_skipped(int &a){for(;;++a){if(a>=2)break;}return a;}
int nested_break(int n){int count=0;for(int i=0;i<n;++i){for(int j=0;j<n;++j){if(j==2)break;++count;}count+=10;}return count;}
int local_break(){while(true){int x=99;{int y=88;break;}return x;}int x=7;return x;}
int skipped_fault(int &a){while(true){break;a+=1;}return a;}
int returned_after_break(int &a){while(true){while(true){break;}a=9;return a;}return 0;}
int jump(){while(true){break;}return 7;}
}'''
        with tempfile.TemporaryDirectory(prefix='loop-break-') as directory:
            scratch = Path(directory)
            source, proof, binary = scratch/'test.cpp', scratch/'test.lean', scratch/'test'
            source.write_text(text)
            ir = lower_source(source)
            lean = emit_lean(ir,'BreakTest') + '\nopen BreakTest Proofs.CppState Proofs.CppLoop\n'
            for n in range(-2,7):
                for function in ['stopped','update_skipped']:
                    lean += f'#guard (match {function}.callFuel 100 [⟨⟨32,true,false⟩,{n}⟩] [.reference 0] with | .finished r => r.value == {max(n,2)} && r.memory.map (·.value) == [{max(n,2)}] | _ => false)\n'
            for n in range(0,6):
                lean += f'#guard (match nested_break.callFuel 100 [] [.value {n}] with | .finished r => r.value == {n*(10+min(n,2))} && r.memory.isEmpty | _ => false)\n'
            lean += '''#guard (match local_break.callFuel 30 [] [] with | .finished r => r.value == 7 && r.memory.isEmpty | _ => false)
#guard (match skipped_fault.callFuel 30 [⟨⟨32,true,false⟩,2147483647⟩] [.reference 0] with | .finished r => r.value == 2147483647 | _ => false)
#guard (match returned_after_break.callFuel 30 [⟨⟨32,true,false⟩,0⟩] [.reference 0] with | .finished r => r.value == 9 && r.memory.map (·.value) == [9] | _ => false)
#guard jump.callFuel 30 [] [] == .finished ⟨7,[],5,1⟩
#guard jump.callFuel 30 [] [] == jump.callFuel 60 [] []
#guard Proofs.CppLoop.runFuel 1 .breakLoop ⟨[],[],0,0,0⟩ == .finished ⟨⟨[],[],1,0,0⟩,none,true⟩
#guard (LoopProgram.mk [] ⟨32,true,false⟩ (.sequence .breakLoop (.ret (.literal ⟨32,true,false⟩ 7)))).callFuel 4 [] [] == .fault
'''
            proof.write_text(lean)
            lake, env = lean_environment()
            subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,check=True)
            source.write_text('#include <cassert>\n' + text + '''
int main(){for(int n=-2;n<=6;++n){int a=n;assert(cp::stopped(a)==(n<2?2:n));assert(a==(n<2?2:n));a=n;assert(cp::update_skipped(a)==(n<2?2:n));assert(a==(n<2?2:n));}
for(int n=0;n<6;++n)assert(cp::nested_break(n)==n*(10+(n<2?n:2)));
assert(cp::local_break()==7);int a=2147483647;assert(cp::skipped_fault(a)==2147483647);a=0;assert(cp::returned_after_break(a)==9);assert(a==9);assert(cp::jump()==7);}
''')
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',str(source),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)
            source.write_text('namespace cp {int jump(){while(true){;}return 7;}}')
            proof.write_text(emit_lean(lower_source(source),'ChangedBreak') +
                '\n#guard (match ChangedBreak.jump.callFuel 30 [] [] with | .finished r => r.value == 7 | _ => false)\n')
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertNotEqual(result.returncode,0)
            self.assertIn('did not evaluate to `true`',result.stdout+result.stderr)


if __name__ == "__main__":
    disable_network()
    lake, env = lean_environment()
    subprocess.run([lake, "build", "Proofs.CppLoop"], cwd=ROOT, env=env, check=True)
    unittest.main()
