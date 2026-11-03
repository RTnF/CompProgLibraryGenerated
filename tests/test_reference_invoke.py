"""Reference-call primitives applied to source-generated scalar and loop bodies."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'verifier'))
sys.path.insert(0,str(ROOT/'tools'))
from state_ir import lower_source,emit_lean
from test_scalar_ir import lean_environment
from offline import disable_network

SOURCE='''namespace cp {
long long update(long long &a,const long long &b,long long delta) {a+=delta;return b;}
unsigned long long update_unsigned(unsigned long long &a,const unsigned long long &b,unsigned long long delta) {a+=delta;return b;}
long long copied(long long a,const long long &b) {a+=1ll;return b;}
long long local(long long &a,const long long &b) {long long z=a+b;a=z;return b;}
long long down_ref(long long &x,long long steps) {while(steps>0ll){x-=1ll;steps-=1ll;}return x;}
long long read(const long long &x) {return x;}
}'''

class ReferenceInvokeTests(unittest.TestCase):
    def lean(self,scratch,model,checks,success=True):
        lake,env=lean_environment();path=scratch/'test.lean'
        imports='import Proofs.CppReferenceInvoke\n'
        path.write_text(imports+model+'\nopen Proofs.CppScalar Proofs.CppState\n'+checks)
        result=subprocess.run([lake,'env','lean',str(path)],cwd=ROOT,env=env,capture_output=True,text=True)
        if success:self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        else:
            self.assertNotEqual(result.returncode,0)
            self.assertIn('did not evaluate to `true`',result.stdout+result.stderr)

    def test_aliases_copies_local_cells_and_cpp(self):
        native='#include <cassert>\n'+SOURCE+'\nint main(){\n'
        checks=''
        for unsigned,name,cpp_type,values,other,deltas in [
            (False,'update','long long',[-7,0,1,7],[-3,0,5],[-2,0,3]),
            (True,'update_unsigned','unsigned long long',[0,1,2**63,2**64-1],[0,1,2**64-1],[0,1,2**64-1])]:
            ty=f'⟨64,{str(not unsigned).lower()},false⟩'
            suffix='ULL' if unsigned else 'LL'
            cases=[(p,q,a,b,d) for p,q in [(0,3),(3,0)] for a in values for b in other for d in deltas]
            cases += [(2,2,a,a,d) for a in values for d in deltas]
            for p,q,a,b,d in cases:
                updated=(a+d)%(2**64) if unsigned else a+d
                returned=updated if p==q else b
                cells=['⟨⟨1,false,true⟩,9⟩']*4
                cells[p]=f'⟨{ty},({a})⟩';cells[q]=f'⟨{ty},({b})⟩'
                memory='['+','.join(cells)+']'
                final=cells.copy();final[p]=f'⟨{ty},({updated})⟩';final.append(f'⟨{ty},({returned})⟩')
                result='['+','.join(final)+']'
                caller=f'⟨{memory},[⟨{p},true⟩,⟨{q},false⟩],17,4,0⟩'
                args=f'[.reference 0,.reference 1,.value (.literal {ty} ({d}))]'
                invocation=f'Proofs.CppReferenceInvoke.run {caller} Helpers.{name}.parameters Helpers.{name}.resultType {args} Helpers.{name}.body'
                checks+=f'#guard ({invocation}).map (fun s => (s.state.memory,s.state.bindings,s.state.work,s.state.peak,s.returned,s.breaking)) == some ({result},[⟨{p},true⟩,⟨{q},false⟩,⟨4,false⟩],31,9,none,false)\n'
                # Both bindings survive with their original permissions. The
                # callee copies and reserved caller-frame cells do not escape.
                if p==q:
                    native+=f'{{{cpp_type} a={a}{suffix};assert(cp::{name}(a,a,{d}{suffix})=={returned}{suffix});assert(a=={updated}{suffix});}}\n'
                else:
                    native+=f'{{{cpp_type} a={a}{suffix},b={b}{suffix};assert(cp::{name}(a,b,{d}{suffix})=={returned}{suffix});assert(a=={updated}{suffix});assert(b=={b}{suffix});}}\n'
        for a in [-12,0,9,2147483647]:
            ty='⟨64,true,false⟩';memory=f'[⟨{ty},({a})⟩]'
            caller=f'⟨{memory},[⟨0,true⟩],11,1,100⟩'
            invocation=f'Proofs.CppReferenceInvoke.run {caller} Helpers.copied.parameters Helpers.copied.resultType [.value (.variable {ty} 0),.reference 0] Helpers.copied.body'
            checks+=f'#guard ({invocation}).map (fun s => (s.state.memory,s.state.work,s.state.peak)) == some ([⟨{ty},({a})⟩,⟨{ty},({a})⟩],23,100)\n'
            native+=f'{{long long a={a}LL;assert(cp::copied(a,a)=={a}LL);assert(a=={a}LL);}}\n'
            for alias in [False,True]:
                b=a if alias else 3;updated=a+b
                cells=[f'⟨{ty},({a})⟩'] if alias else [f'⟨{ty},({a})⟩',f'⟨{ty},({b})⟩']
                q=0 if alias else 1
                memory='['+','.join(cells)+']';count=len(cells);returned=updated if alias else b
                caller=f'⟨{memory},[⟨0,true⟩,⟨{q},false⟩],0,{count},0⟩'
                final=cells.copy();final[0]=f'⟨{ty},({updated})⟩';final.append(f'⟨{ty},({returned})⟩')
                result='['+','.join(final)+']'
                invocation=f'Proofs.CppReferenceInvoke.run {caller} Helpers.local.parameters Helpers.local.resultType [.reference 0,.reference 1] Helpers.local.body'
                checks+=f'#guard ({invocation}).map (fun s => (s.state.memory,s.state.work,s.state.peak)) == some ({result},14,9)\n'
                native+=f'{{long long a={a}LL,b={b}LL;assert(cp::local(a,{"a" if alias else "b"})=={returned}LL);assert(a=={updated}LL);assert(b=={b}LL);}}\n'
        native+='}\n'
        with tempfile.TemporaryDirectory(prefix='reference-invoke-') as directory:
            scratch=Path(directory);source=scratch/'helpers.cpp';source.write_text(SOURCE)
            model=emit_lean(lower_source(source),'Helpers')
            self.lean(scratch,model,checks)
            source.write_text(native);binary=scratch/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',str(source),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

    def test_rejections_loops_and_source_changes(self):
        checks='''
def ty : Ty := ⟨64,true,false⟩
def caller : State := ⟨[⟨ty,10⟩],[⟨0,true⟩],0,1,0⟩
#guard Proofs.CppReferenceInvoke.prepare caller Helpers.update.parameters [.reference 0,.reference 0] == none
#guard Proofs.CppReferenceInvoke.prepare caller Helpers.update.parameters [.reference 0,.reference 0,.value (.literal ty 3),.reference 0] == none
#guard Proofs.CppReferenceInvoke.prepare {caller with bindings := [⟨0,false⟩]} Helpers.update.parameters [.reference 0,.reference 0,.value (.literal ty 3)] == none
#guard Proofs.CppReferenceInvoke.prepare caller Helpers.read.parameters [.value (.literal ty 10)] == none
#guard Proofs.CppReferenceInvoke.prepare caller Helpers.read.parameters [.reference 7] == none
#guard Proofs.CppReferenceInvoke.prepare {caller with bindings := [⟨1,true⟩]} [⟨⟨1,false,true⟩,true,true⟩] [.reference 0] == none
#guard Proofs.CppReferenceInvoke.prepare {caller with bindings := [⟨2,true⟩]} [⟨ty,false,true⟩,⟨ty,true,true⟩] [.value (.literal ty 10),.reference 0] == none
#guard Proofs.CppReferenceInvoke.prepare {caller with memory := [⟨⟨64,false,false⟩,10⟩]} Helpers.read.parameters [.reference 0] == none
#guard Proofs.CppReferenceInvoke.prepare {caller with memory := [⟨ty,9223372036854775808⟩]} Helpers.read.parameters [.reference 0] == none
#guard (Proofs.CppReferenceInvoke.run {caller with bindings := [⟨0,false⟩]} Helpers.read.parameters ty [.reference 0] Helpers.read.body).map (fun s => s.state.memory) == some [⟨ty,10⟩,⟨ty,10⟩]
#guard Proofs.CppReferenceInvoke.run {caller with memory := [⟨ty,9223372036854775807⟩]} Helpers.update.parameters ty [.reference 0,.reference 0,.value (.literal ty 1)] Helpers.update.body == none
#guard Proofs.CppReferenceInvoke.finish caller ty ⟨caller,none,false⟩ == none
#guard Proofs.CppReferenceInvoke.finish caller ty ⟨caller,some 10,true⟩ == none
#guard Proofs.CppReferenceInvoke.finish caller ty ⟨{caller with memory := []},some 10,false⟩ == none
#guard Proofs.CppReferenceInvoke.finish caller ⟨1,false,true⟩ ⟨caller,some 3,false⟩ == none
#guard Proofs.CppReferenceInvoke.runFuel 1 caller Helpers.down_ref.parameters ty [.reference 0,.value (.literal ty 5)] Helpers.down_ref.body == .exhausted
#guard Proofs.CppReferenceInvoke.runFuel 100 {caller with memory := [⟨ty,(-9223372036854775808)⟩]} Helpers.down_ref.parameters ty [.reference 0,.value (.literal ty 1)] Helpers.down_ref.body == .fault
#guard (match Proofs.CppReferenceInvoke.runFuel 300 caller Helpers.down_ref.parameters ty [.reference 0,.value (.literal ty 5)] Helpers.down_ref.body with | .finished s => s.state.memory == [⟨ty,5⟩,⟨ty,5⟩] && s.returned == none | _ => false)
example (extra : Nat) :
    Proofs.CppReferenceInvoke.runFuel (300+extra) caller Helpers.down_ref.parameters ty [.reference 0,.value (.literal ty 5)] Helpers.down_ref.body =
      Proofs.CppReferenceInvoke.runFuel 300 caller Helpers.down_ref.parameters ty [.reference 0,.value (.literal ty 5)] Helpers.down_ref.body := by
  exact Proofs.CppReferenceInvoke.fuel_success_mono 300 extra caller Helpers.down_ref.parameters ty
    [.reference 0,.value (.literal ty 5)] Helpers.down_ref.body _ rfl
'''
        with tempfile.TemporaryDirectory(prefix='reference-invoke-invalid-') as directory:
            scratch=Path(directory);source=scratch/'helper.cpp';source.write_text(SOURCE)
            self.lean(scratch,emit_lean(lower_source(source),'Helpers'),checks)
            native=scratch/'native.cpp';binary=scratch/'native'
            native.write_text('#include <cassert>\n'+SOURCE+'\nint main(){long long a=10;assert(cp::down_ref(a,5)==5);assert(a==5);const long long b=12;assert(cp::read(b)==12);}\n')
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',str(native),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)
            original_guard='''#guard (Proofs.CppReferenceInvoke.run caller Helpers.update.parameters ty [.reference 0,.reference 0,.value (.literal ty 3)] Helpers.update.body).map (fun s => s.state.memory) == some [⟨ty,13⟩,⟨ty,13⟩]\n'''
            self.lean(scratch,emit_lean(lower_source(source),'Helpers'),checks[:checks.index('#guard')]+original_guard)
            for changed in [SOURCE.replace('a+=delta','a-=delta'),SOURCE.replace('return b;','return delta;',1)]:
                source.write_text(changed)
                self.lean(scratch,emit_lean(lower_source(source),'Helpers'),checks[:checks.index('#guard')]+original_guard,False)

if __name__=='__main__':
    disable_network();lake,env=lean_environment()
    subprocess.run([lake,'build','Proofs.CppReferenceInvoke'],cwd=ROOT,env=env,check=True)
    unittest.main()
