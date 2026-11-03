"""Arbitrary reference layouts, source-linked proofs and mutation rejection."""
from pathlib import Path
import re
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

HEADER=ROOT/'experiments/verification/template/update_extrema.hpp'
INSTANCE_SOURCE=ROOT/'tests/imports/update_extrema_instantiations.cpp'

class ReferenceTests(unittest.TestCase):
    def test_arbitrary_layouts_aliases_frames_and_cpp(self):
        lake,env=lean_environment()
        proof='import Proofs.ExtremaReferences\nopen Proofs.CppScalar Proofs.CppState Proofs.ExtremaReferences\n'
        native=f'#include "{HEADER}"\n#include <array>\n#include <cassert>\n#include <cstdint>\nint main(){{\n'
        case=0
        for signed,kind,cpp_type,values in [
            (True,'int','std::int32_t',[-2147483648,-1,0,1,2147483647]),
            (False,'unsigned_int','std::uint32_t',[0,1,2,2147483648,4294967295])]:
            ty=f'⟨32,{str(signed).lower()},false⟩'
            label='signed' if signed else 'unsigned'
            pairs=[(p,q,a,b) for p,q in [(0,1),(1,0),(2,4),(4,2)] for a in values for b in values]
            pairs += [(3,3,a,a) for a in values]
            for p,q,a,b in pairs:
                # Only the referenced cells must be typed and initialized. An
                # invalid, unbound caller cell is deliberately left unread.
                cells=['⟨⟨1,false,true⟩,9⟩']*7
                cells[p]=f'⟨{ty},({a})⟩';cells[q]=f'⟨{ty},({b})⟩'
                memory='['+','.join(cells)+']'
                proof+=f'def mem{case} : List Cell := {memory}\n'
                for direction,update in [('max',a<b),('min',b<a)]:
                    expected=cells.copy()
                    if update:expected[p]=f'⟨{ty},({b})⟩'
                    expected='['+','.join(expected)+']'
                    returned=int(update);work=9 if update else 7
                    function=f'Proofs.ExtremaInstances.ch{direction}__{kind}__{kind}'
                    proof+=f'example : {function}.call mem{case} [.reference {p},.reference {q}] = some ⟨{returned},{expected},{work},5⟩ := by\n'
                    proof+=f'  simpa [mem{case},List.set] using ch{direction}_{label} mem{case} {p} {q} ({a}) ({b}) (by decide) (by decide) (by decide) (by decide)\n'
                    proof+=f'#guard ({function}.call mem{case} [.reference {p},.reference {q}]) == some ⟨{returned},{expected},{work},5⟩\n'
                    proof+=f'example : (updatedMemory mem{case} {p} {ty} ({b}) {str(update).lower()}).length = mem{case}.length ∧ (updatedMemory mem{case} {p} {ty} ({b}) {str(update).lower()})[{p}]? = some ⟨{ty},({b if update else a})⟩ ∧ (updatedMemory mem{case} {p} {ty} ({b}) {str(update).lower()})[{q}]? = some ⟨{ty},({b})⟩ ∧ ∀ r, r ≠ {p} → (updatedMemory mem{case} {p} {ty} ({b}) {str(update).lower()})[r]? = mem{case}[r]? := by\n'
                    proof+=f'  simpa using update_frame {ty} mem{case} {p} {q} ({a}) ({b}) {str(update).lower()} (by decide) (by decide)\n'
                    native+=f'{{std::array<{cpp_type},7> x{{}};x[{p}]={a}LL;x[{q}]={b}LL;const auto before=x;assert(cp::ch{direction}(x[{p}],x[{q}])=={str(update).lower()});assert(x[{p}]=={b if update else a}LL);assert(x[{q}]=={b}LL);for(int r=0;r<7;++r)if(r!={p})assert(x[r]==before[r]);}}\n'
                case+=1
        proof+='''#guard Proofs.ExtremaInstances.chmax__int__int.call [⟨⟨32,true,false⟩,1⟩] [.reference 0,.reference 1] == none
#guard Proofs.ExtremaInstances.chmax__int__int.call [⟨⟨32,true,false⟩,2147483648⟩] [.reference 0,.reference 0] == none
#guard Proofs.ExtremaInstances.chmax__int__int.call [⟨⟨32,false,false⟩,1⟩] [.reference 0,.reference 0] == none
'''
        native+='}\n'
        with tempfile.TemporaryDirectory(prefix='extrema-references-') as directory:
            scratch=Path(directory);lean=scratch/'test.lean';cpp=scratch/'test.cpp';binary=scratch/'test'
            lean.write_text(proof)
            checked=subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(checked.returncode,0,checked.stdout+checked.stderr)
            cpp.write_text(native)
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',str(cpp),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

    def test_regenerated_source_proofs_reject_mutations(self):
        original=HEADER.read_text()
        source_text=INSTANCE_SOURCE.read_text()
        proofs=re.sub(r'^import .*\n','',(ROOT/'Proofs/ExtremaReferences.lean').read_text(),flags=re.M)
        lake,env=lean_environment()
        with tempfile.TemporaryDirectory(prefix='extrema-reference-mutations-') as directory:
            scratch=Path(directory);header=scratch/'helper.hpp';source=scratch/'instances.cpp';lean=scratch/'proof.lean'
            source.write_text(re.sub(r'#include .*',f'#include "{header}"',source_text,count=1))
            for change in [None,('a < b','a <= b'),('b < a','b <= a'),('a = b','a = a'),('return 1','return 0')]:
                with self.subTest(change=change):
                    changed=original if change is None else original.replace(*change)
                    if change is not None:self.assertNotEqual(changed,original)
                    header.write_text(changed)
                    lean.write_text(emit_lean(lower_source(source),'Proofs.ExtremaInstances')+'\n'+proofs)
                    checked=subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
                    if change is None:self.assertEqual(checked.returncode,0,checked.stdout+checked.stderr)
                    else:self.assertNotEqual(checked.returncode,0)

if __name__=='__main__':
    disable_network();lake,env=lean_environment()
    subprocess.run([lake,'build','Proofs.ExtremaReferences'],cwd=ROOT,env=env,check=True)
    unittest.main()
