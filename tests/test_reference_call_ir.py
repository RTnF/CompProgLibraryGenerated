"""Generate caller control flow containing nested lvalue-reference calls."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'verifier'));sys.path.insert(0,str(ROOT/'tools'))
from state_ir import lower_source,emit_lean
from test_scalar_ir import lean_environment
from offline import disable_network

SOURCE='''namespace cp {
long long bump(long long &x){x+=1ll;return x;}
long long read(const long long &x){return x;}
long long relay(long long &x){return bump(x);}
long long snapshot(long long &x){const long long y=relay(x);return x+y;}
long long branch(long long &x){if(relay(x)){bump(x);return x;}return x;}
long long copied(long long x){bump(x);return x*2ll;}
long long copied_call(long long &x){return copied(x);}
long long shadow(long long &x){ {long long y=x;bump(y);}return read(x);}
long long alias(long long &x,const long long &y){bump(x);return read(y);}
long long compound(long long &x){x+=bump(x);return x;}
long long repeated(long long &x,long long n){while(n>0ll){bump(x);--n;}return x;}
long long early(long long &x,long long n){while(n>0ll){bump(x);if(x>3ll)break;--n;}return x;}
}'''

class ReferenceCallIRTests(unittest.TestCase):
    def lean(self,scratch,source,checks,succeeds=True):
        path=scratch/'source.cpp';path.write_text(source)
        model=emit_lean(lower_source(path),'Calls')
        lake,env=lean_environment();proof=scratch/'test.lean';proof.write_text(model+'\n'+checks)
        result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
        if succeeds:self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        else:
            self.assertNotEqual(result.returncode,0)
            self.assertIn('did not evaluate to `true`',result.stdout+result.stderr)
        return model

    def test_generated_callers_and_native_cpp(self):
        checks='';native='#include <cassert>\n'+SOURCE+'\nint main(){\n';ty='⟨64,true,false⟩'
        for x in range(-4,5):
            values={'relay':(x+1,x+1),'snapshot':(2*x+2,x+1),
                    'branch':(x+1+(x!=-1),x+1+(x!=-1)),
                    'copied_call':(2*x+2,x),'shadow':(x,x),'alias':(x+1,x+1),'compound':(2*x+2,2*x+2)}
            for name,(returned,updated) in values.items():
                arguments='[.reference 0,.reference 0]' if name=='alias' else '[.reference 0]'
                checks+=f'#guard (Calls.{name}.call [⟨{ty},({x})⟩] {arguments}).map (fun r => (r.value,r.memory.map (·.value))) == some ({returned},[{updated}])\n'
                native+=f'{{long long x={x}LL;assert(cp::{name}(x{",x" if name=="alias" else ""})=={returned}LL);assert(x=={updated}LL);}}\n'
            for n in [0,1,4]:
                result=x+n
                early=x+min(n,max(1,4-x))
                for name,expected in [('repeated',result),('early',early)]:
                    checks+=f'#guard (match Calls.{name}.callFuel 400 [⟨{ty},({x})⟩] [.reference 0,.value {n}] with | .finished r => (r.value,r.memory.map (·.value)) == ({expected},[{expected}]) | _ => false)\n'
                    native+=f'{{long long x={x}LL;assert(cp::{name}(x,{n}LL)=={expected}LL);assert(x=={expected}LL);}}\n'
        checks+='''example (extra : Nat) : Calls.repeated.callFuel (400+extra) [⟨⟨64,true,false⟩,0⟩] [.reference 0,.value 4] = Calls.repeated.callFuel 400 [⟨⟨64,true,false⟩,0⟩] [.reference 0,.value 4] := by
  exact Proofs.CppReferenceCommands.Program.callFuel_success_mono Calls.repeated 400 extra _ _ _ rfl
#guard Calls.repeated.callFuel 1 [⟨⟨64,true,false⟩,0⟩] [.reference 0,.value 5] == .exhausted
#guard Calls.relay.call [⟨⟨64,true,false⟩,9223372036854775807⟩] [.reference 0] == none
'''
        native+='}\n'
        with tempfile.TemporaryDirectory(prefix='reference-call-ir-') as directory:
            scratch=Path(directory)
            model=self.lean(scratch,SOURCE,checks)
            self.assertIn('Proofs.CppReferenceCommands.Program',model)
            cpp=scratch/'native.cpp';cpp.write_text(native);binary=scratch/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',str(cpp),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

    def test_renaming_mutations_and_refusal_of_ambiguous_effects(self):
        with tempfile.TemporaryDirectory(prefix='reference-call-changes-') as directory:
            scratch=Path(directory);source=scratch/'source.cpp';source.write_text(SOURCE)
            original=lower_source(source)
            source.write_text(SOURCE.replace('bump','successor'))
            renamed=lower_source(source)
            for f in renamed['functions']:
                if f['name']=='successor':f['name']='bump'
            self.assertEqual(original,renamed)
            self.lean(scratch,SOURCE.replace('x+=1ll','x+=2ll'),
                '#guard (Calls.relay.call [⟨⟨64,true,false⟩,0⟩] [.reference 0]).map (·.value) == some 1\n',False)
            for text in [
                'namespace cp {long f(long &x){++x;return x;}long g(long &x){return f(x)+x;}}',
                'namespace cp {long f(long &x){++x;return x;}long g(long &x){return f(x)+1;}}',
                'namespace cp {long f(long &x){++x;return x;}long h(long &x,long y){return x+y;}long g(long &x){return h(x,f(x));}}',
                'namespace cp {long f(const long &x){return x;}long g(){return f(1l);}}',
            ]:
                source.write_text(text)
                with self.subTest(text=text),self.assertRaisesRegex(ValueError,'standalone expression|direct lvalue bindings|ExprWithCleanups'):
                    lower_source(source)

if __name__=='__main__':
    disable_network();lake,env=lean_environment()
    subprocess.run([lake,'build','Proofs.CppReferenceCommands'],cwd=ROOT,env=env,check=True)
    unittest.main()
