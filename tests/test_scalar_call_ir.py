"""Direct-call identities, ANF temporaries, source changes and native agreement."""

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'verifier'))
sys.path.insert(0, str(ROOT / 'tools'))
from state_ir import lower_source, emit_lean
from offline import disable_network
from test_scalar_ir import lean_environment

SOURCE = '''namespace cp {
long long bump(long long x);
long long before(long long x) { return bump(x); }
long long bump(long long x) { x += 1ll; return x; }
long long bump(long long x);
long long add(long long x, long long y) { return x+y; }
long long constant() { return 8ll; }
long long down(long long n) { while(n>0ll) {n-=1ll;} return n; }
long long caller(long long &x) {
  const long long y=bump(x), z=constant();
  bump(y);
  x += bump(y);
  if(bump(x)>0ll) { const long long y=bump(x); return add(y,bump(bump(z))); }
  return bump(x);
}
long long alias(long long &x,long long &y) { x=add(bump(x),bump(y)); return y; }
long long branch(long long x) { if(bump(x)) {long long y=bump(x); return y;} return constant(); }
long long repeated(long long &x) { for(int i=0;i<4;++i) {x=bump(x);} return x; }
long long loops(long long x) { return down(x)+constant(); }
long long nested(long long x) { return add(bump(x),bump(bump(x))); }
unsigned long long wrap(unsigned long long x) { return x+1ull; }
unsigned long long converted(unsigned int x) { return wrap(x); }
long long constarg(const long long x) {return x;}
long long constcaller(long long x) {return constarg(x);}
long long multidecl(long long x) {const long long y=bump(x), z=bump(y);return z;}
long long count(long long n) {long long x=0ll;while(x<n) x=bump(x);return x;}
}'''


class CallIRTests(unittest.TestCase):
    def lean(self, scratch, generated, guards, succeeds=True):
        lake,env=lean_environment()
        proof=scratch/'test.lean'
        proof.write_text(generated+'\n'+guards)
        result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
        if succeeds:
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        else:
            self.assertNotEqual(result.returncode,0)
            self.assertIn('did not evaluate to `true`',result.stdout+result.stderr)

    def test_native_calls_temporaries_copies_and_loops(self):
        with tempfile.TemporaryDirectory(prefix='scalar-call-ir-') as directory:
            scratch=Path(directory); source=scratch/'source.cpp';source.write_text(SOURCE)
            generated=emit_lean(lower_source(source),'Calls')
            guards=''
            native=[]
            for x in range(-12,13):
                updated=2*x+2
                value=updated+11 if updated+1>0 else updated+1
                guards+=f'#guard (Calls.caller.call [⟨⟨64,true,false⟩,{x}⟩] [.reference 0]).map (fun r => (r.value,r.memory.map (·.value))) == some ({value},[{updated}])\n'
                guards+=f'#guard (Calls.alias.call [⟨⟨64,true,false⟩,{x}⟩] [.reference 0,.reference 0]).map (fun r => (r.value,r.memory.map (·.value))) == some ({2*x+2},[{2*x+2}])\n'
                expected={'before':x+1,'branch':x+1 if x!=-1 else 8,'nested':2*x+3,'constcaller':x,'multidecl':x+2}
                for name,result in expected.items():
                    guards+=f'#guard (Calls.{name}.call [] [.value ({x})]).map (·.value) == some ({result})\n'
                    native.append(f'assert(cp::{name}({x})==({result}));')
                guards+=f'#guard (match Calls.repeated.callFuel 130 [⟨⟨64,true,false⟩,{x}⟩] [.reference 0] with | .finished r => (r.value,r.memory.map (·.value)) == ({x+4},[{x+4}]) | _ => false)\n'
                guards+=f'#guard (match Calls.loops.callFuel 150 [] [.value ({x})] with | .finished r => r.value == ({min(x,0)+8}) | _ => false)\n'
                native.append(f'{{long long a={x};assert(cp::caller(a)==({value}));assert(a==({updated}));a={x};assert(cp::alias(a,a)==({2*x+2}));a={x};assert(cp::repeated(a)==({x+4}));assert(cp::loops({x})==({min(x,0)+8}));}}')
            for x in (0,1,2147483647,4294967295):
                guards+=f'#guard (Calls.converted.call [] [.value {x}]).map (·.value) == some {x+1}\n'
                native.append(f'assert(cp::converted({x}u)=={x+1}ull);')
            guards+='''#guard (Calls.wrap.call [] [.value 18446744073709551615]).map (·.value) == some 0
#guard Calls.before.call [] [.value 9223372036854775807] == none
#guard Calls.loops.callFuel 2 [] [.value 5] == .exhausted
#guard (match Calls.count.callFuel 500 [] [.value 20], Calls.count.callFuel 500 [] [.value 1] with
 | .finished a, .finished b => a.value == 20 && a.peak == b.peak
 | _, _ => false)
'''
            for x,y in ((-4,3),(2,-7),(0,0)):
                guards+=f'#guard (Calls.alias.call [⟨⟨64,true,false⟩,{x}⟩,⟨⟨64,true,false⟩,{y}⟩] [.reference 0,.reference 1]).map (fun r => (r.value,r.memory.map (·.value))) == some ({y},[{x+y+2},{y}])\n'
                native.append(f'{{long long x={x},y={y};assert(cp::alias(x,y)==({y}));assert(x==({x+y+2}));assert(y==({y}));}}')
            self.lean(scratch,generated,guards)
            source.write_text('#include <cassert>\n'+SOURCE+'\nint main(){'+''.join(native)+'assert(cp::wrap(18446744073709551615ull)==0);assert(cp::count(20)==20);}\n')
            binary=scratch/'test'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',str(source),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

    def test_renaming_and_changed_callee_change_generated_model(self):
        with tempfile.TemporaryDirectory() as directory:
            scratch=Path(directory); source=scratch/'source.cpp';source.write_text(SOURCE)
            ir=lower_source(source)
            # Rename a helper and its parameter only; declaration IDs are fresh.
            source.write_text(SOURCE.replace('bump','successor').replace('long long x) { x += 1ll; return x; }','long long renamed) { renamed += 1ll; return renamed; }'))
            renamed=lower_source(source)
            for f in renamed['functions']:
                if f['name']=='successor': f['name']='bump'
            self.assertEqual(ir,renamed)
            source.write_text(SOURCE.replace('x += 1ll','x += 2ll'))
            changed=emit_lean(lower_source(source),'Calls')
            self.lean(scratch,changed,'#guard (Calls.before.call [] [.value 0]).map (·.value) == some 1\n',False)
            self.lean(scratch,changed,'#guard (Calls.before.call [] [.value 0]).map (·.value) == some 2\n')

    def test_unsupported_calls_never_receive_a_contract(self):
        examples=[
            ('namespace cp {long f(long x);long g(long x){return f(x);}}','definition in the selected AST'),
            ('namespace cp {long f(long x){return f(x);}}','recursive calls'),
            ('namespace cp {long f(long x);long g(long x){return f(x);}long f(long x){return g(x);}}','recursive calls'),
            ('namespace cp {long f(const long &x){return x;}long g(long x){return f(x+1);}}','direct lvalue bindings|ExprWithCleanups'),
            ('long shared=1;namespace cp {long f(long x){return shared+x;}long g(long x){return f(x);}}','nonlocal declaration'),
            ('namespace cp {long f(long x){return x;}long g(long x){return f(x++);}}','unsupported expression'),
            ('namespace cp {long f(long x){return x;}long g(long x){while(long y=f(x)){--x;}return x;}}','unsupported state statement: WhileStmt'),
            ('namespace cp {long f(long x){return x;}bool g(long x){return false && f(x);}}','unsupported expression'),
            ('namespace cp {long f(long x){return x;}long g(long x){long (*p)(long)=f;return p(x);}}','unsupported scalar type'),
            ('namespace cp {long f(long x=1){return x;}long g(){return f();}}','unsupported function child'),
            ('namespace cp {long f(long x){return x;}int f(int x){return x+1;}long g(long x){return f(x);}}','uniquely named'),
        ]
        with tempfile.TemporaryDirectory() as directory:
            source=Path(directory)/'source.cpp'
            for text,message in examples:
                with self.subTest(source=text):
                    source.write_text(text)
                    with self.assertRaisesRegex(ValueError,message):lower_source(source)
            source.write_text(SOURCE)
            with self.assertRaisesRegex(ValueError,'definition in the selected AST'):
                lower_source(source,'cp::caller')


if __name__=='__main__':
    disable_network()
    unittest.main()
