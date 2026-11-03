"""Fresh vector-copy model and original/candidate UF special-member evidence."""
from pathlib import Path
import json
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT/'tools'))
sys.path.insert(0, str(ROOT/'verifier'))
from clang_ast import clang_command
from offline import disable_network
from check_public import check_compiler, FLAGS
from test_scalar_ir import lean_environment
from test_cpp_vector import buffer

class VectorCopyTests(unittest.TestCase):
    def test_copy_model_and_native_constructor(self):
        checks = ['import Proofs.CppVectorCopy\nopen Proofs.CppVector Proofs.CppVectorCopy Proofs.CppScalar\n',
                  'def accept : Int → Bool := (⟨32,true,false⟩ : Ty).valid\n']
        native = ['#include <cassert>\n#include <vector>\nint main(){']
        for case, (values, spare) in enumerate((v, s) for v in [[],[0],[-2147483648,0,2147483647],[-1,-1,-1,-1]] for s in [0,1,7]):
            source = buffer(values,len(values)+spare,epoch=3,owner=7)
            target = buffer(values,len(values),epoch=0,owner=8)
            checks += [f'def b{case} : Buffer Int := {source}\n',
                       f'#guard copyConstruct b{case} 8 accept == some ⟨{target},(),{len(values)+1},{len(values)+2}⟩\n',
                       f'example := copied_valid b{case} 8 accept (by decide +kernel)\n',
                       f'example := copy_runs b{case} 8 accept (by decide +kernel) (by decide)\n',
                       f'#guard (copyConstruct b{case} 7 accept).isNone\n']
            for index, value in enumerate(values):
                checks += [f'example := copy_read b{case} 8 {index} accept ({value}:Int) (by decide +kernel) (by decide +kernel)\n',
                           f'example := source_ref_separate b{case} 8 accept ⟨7,3,{index}⟩ (by decide) rfl\n',
                           f'example := copied_write b{case} 8 {index} accept 42 (by decide +kernel) (by decide) (by decide)\n']
            items = ','.join(map(str, values))
            native += [f'{{std::vector<int> source{{{items}}}; source.reserve({len(values)+spare});',
                       'const auto capacity=source.capacity(); std::vector<int> target(source);',
                       f'assert(target==source && target.capacity()=={len(values)} && source.capacity()==capacity);',
                       'if(!source.empty()){assert(target.data()!=source.data());int value=source[0];target[0]=42;assert(source[0]==value);}}']
        native.append('}')
        checks += ['#guard (copyConstruct (⟨7,[(2147483648:Int)],1,64,0⟩:Buffer Int) 8 accept).isNone\n',
                   'example (source : Buffer Int) (owner : Nat) (valid : source.Valid accept) (fresh : owner ≠ source.owner) := copy_runs source owner accept valid fresh\n']
        checks.append(r"""
open Proofs.CppVectorStore
 def origin : Buffer Int := ⟨0,[-1,-1,-1,-1],17,64,3⟩
 def zero : Store Int := ⟨[],11,99,2⟩
 def first := zero.allocate origin 5 18
 def second := first.allocate origin 5 18
 def retired : Store Int := {second with objects := second.objects.set 1 none}
 def prior := retired.allocate origin 5 18
 example : prior.Valid accept := by
   apply allocate_valid
   · apply destroy_valid
     · apply allocate_valid
       · exact allocate_valid zero origin accept 5 18 (empty_valid accept) (by decide +kernel)
       · decide +kernel
     · decide +kernel
   · decide +kernel
 example (ok : prior.Valid accept) := copy_store_runs prior 0 origin accept ok (by decide +kernel)
 example (ok : prior.Valid accept) := copy_store_valid prior 0 origin accept ok (by decide +kernel)
 #guard copyStore prior 0 accept == some (extended prior origin,3)
 #guard (copyStore prior 1 accept).isNone
 example := copy_store_new prior origin
 example := copy_store_old prior origin 0 (by decide +kernel)
 example := copy_store_old prior origin 1 (by decide +kernel)
 example := copy_store_reference prior origin accept ⟨0,3,2⟩ (by decide +kernel)
 example := copy_store_reference prior origin accept ⟨1,3,2⟩ (by decide +kernel)
 example := copy_store_reference prior origin accept ⟨2,3,2⟩ (by decide +kernel)
 example := copy_store_cost prior origin
 #guard (extended prior origin).liveSpace == prior.liveSpace+5
 #guard (extended prior origin).peak == 99
 #guard (extended prior origin).readReference accept ⟨3,0,2⟩ == some ⟨copied origin 3,-1,1,6⟩
 def changed := (extended prior origin).writeReference accept true ⟨3,0,2⟩ 42
 #guard changed.isSome
 #guard (changed.map fun pair => pair.1.lookup 0) == some (prior.lookup 0)
 #guard (changed.map fun pair => pair.1.lookup 2) == some (prior.lookup 2)
 example (s : Store Int) (owner : Nat) (source : Buffer Int) (ok : s.Valid accept)
   (found : s.lookup owner = some source) := copy_store_runs s owner source accept ok found
""")
        with tempfile.TemporaryDirectory(prefix='cpp-vector-copy-') as directory:
            scratch = Path(directory)
            proof = scratch/'checks.lean';proof.write_text(''.join(checks))
            lake, env = lean_environment()
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler()
            source = scratch/'checks.cpp';source.write_text('\n'.join(native))
            executable = scratch/'checks'
            compiled = subprocess.run(['g++',*FLAGS,'-fsanitize=undefined','-fno-sanitize-recover=all',str(source),'-o',str(executable)],cwd=ROOT,capture_output=True,text=True)
            self.assertEqual(compiled.returncode,0,compiled.stdout+compiled.stderr)
            subprocess.run([str(executable)],cwd=ROOT,check=True,capture_output=True,text=True)

    def test_original_and_candidate_special_members(self):
        check_compiler()
        harness = ROOT/'tests/imports/union_find_special_members.cpp'
        with tempfile.TemporaryDirectory(prefix='uf-special-members-') as directory:
            executable = Path(directory)/'checks'
            compiled = subprocess.run(['g++',*FLAGS,'-I',str(ROOT/'experiments/library/cpp'),'-fno-access-control','-fsanitize=undefined','-fno-sanitize-recover=all',str(harness),'-o',str(executable)],cwd=ROOT,capture_output=True,text=True)
            self.assertEqual(compiled.returncode,0,compiled.stdout+compiled.stderr)
            counts = [0,1,2,4,17]
            result = subprocess.run([str(executable)],input='\n'.join(map(str,counts))+'\n',cwd=ROOT,check=True,capture_output=True,text=True)
            # Observations of the pinned libstdc++ profile, not a portable moved-from postcondition.
            self.assertEqual(result.stdout.splitlines(),[f'{n} {int(n>0)} {int(n>0)} {int(n>0)}' for n in counts])
            result = subprocess.run([*clang_command(),'-I',str(ROOT/'experiments/library/cpp'),'-fno-access-control','-Xclang','-ast-dump=json','-Xclang','-ast-dump-filter=cp::UnionFind','-fsyntax-only',str(harness)],cwd=ROOT,check=True,capture_output=True,text=True)
            record = json.loads(result.stdout)
            self.assertEqual((record['kind'],record['name']),('CXXRecordDecl','UnionFind'))
            fields = [(item['name'],item['type']['qualType']) for item in record['inner'] if item['kind']=='FieldDecl']
            self.assertEqual(fields,[('_ps','std::vector<int>'),('_num_groups','int'),('_n','int')])
            special = [item for item in record['inner'] if item['kind'] in ('CXXConstructorDecl','CXXMethodDecl') and item.get('isImplicit') and item.get('isUsed') and item.get('name') in ('UnionFind','operator=')]
            self.assertEqual(len(special),4,[(item.get('name'),item.get('type')) for item in special])
            for item in special:
                self.assertEqual(item.get('explicitlyDefaulted'),'default')
                self.assertTrue(any(child['kind']=='CompoundStmt' for child in item.get('inner',[])),item['type'])

if __name__ == '__main__':
    disable_network()
    unittest.main()
