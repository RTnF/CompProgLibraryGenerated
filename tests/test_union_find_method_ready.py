"""Same/size/unite preserve the method frame; counter aliases track merges."""
from pathlib import Path
import re
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_union_find_original_api import HEADER
from test_union_find_fields_call import FIXTURE
from test_union_find_same_call import PROOF as SAME_PROOF
from test_union_find_size_call import PROOF as SIZE_PROOF
from test_union_find_unite_call import PROOF as UNITE_PROOF, MERGE_FIXTURE, PARENT_FIXTURE
from test_union_find_num_groups_call import PROOF as COUNTER_PROOF
from test_union_find_unite_call import CALLER_STRICT
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent
CHAIN = '''
 def afterMerge : NState := match swapCall with | .finished (s,_) => s | _ => secondCaller
 def getterAfter := Proofs.UnionFindCandidateInstance.UnionFind_num_groups.callFuel 128 afterMerge
   [.vectorReference 0,.scalarReference 1,.value ne]
 #guard observe getterAfter == some (1,1,finalParents)
 def sizeAfter := Proofs.UnionFindCandidateInstance.UnionFind_size.callFuel 128 afterMerge
   [.vectorReference 0,.scalarReference 1,.value ne,.value ae]
 #guard observe sizeAfter == some (4,1,finalParents)
 def sameAfter := Proofs.UnionFindCandidateInstance.UnionFind_same.callFuel 128 afterMerge args
 #guard observe sameAfter == some (1,1,finalParents)
 #guard afterMerge.scalarCell 2 intTy == some (⟨0,false⟩,⟨intTy,1⟩)
 #guard afterMerge.scalarCell 3 intTy == some (⟨1,true⟩,⟨intTy,9876⟩)
 example (caller out : NState) (counter : Nat) (count : Int) (r1 r2 slot : Nat) (ty : Ty)
   (binding : Proofs.CppState.Binding) (value : Proofs.CppState.Cell)
   (memory : out.scalars.memory = Proofs.UfFieldsUnite.updatedMemory caller.scalars.memory counter count r1 r2)
   (bindings : out.scalars.bindings = caller.scalars.bindings) (slots : out.slots = caller.slots)
   (found : caller.scalarCell slot ty = some (binding,value)) (different : binding.address ≠ counter) :=
   Proofs.UfUniteReady.updated_other caller out counter count r1 r2 memory bindings slots slot ty binding value found different
'''
class UnionFindMethodReadyTests(unittest.TestCase):
    def test_new_method_postconditions_and_merge_continuations(self):
        header=HEADER.replace('ps.length+1,64,0','ps.length+1,Proofs.CppVectorBindings.sizeLimit intTy,0')
        with tempfile.TemporaryDirectory(prefix='uf-method-ready-') as directory:
            lake,env=lean_environment()
            for part,proof,fixture in [('Same',SAME_PROOF,FIXTURE),('Size',SIZE_PROOF,FIXTURE),
                ('Unite',UNITE_PROOF,FIXTURE+MERGE_FIXTURE+PARENT_FIXTURE),
                ('Counter',COUNTER_PROOF,FIXTURE+'\nopen Proofs.UfClassInvariant\n'+PARENT_FIXTURE+CALLER_STRICT)]:
                name=part.lower()
                proof=re.sub(r'(?<![\w.])'+name+r'_call\b',f'Proofs.Uf{part}Ready.{name}_call_ready',proof)
                if part == 'Counter':
                    proof=re.sub(r'(?<![\w.])num_groups_call\b','Proofs.UfCounterReady.num_groups_call_ready',proof)
                path=Path(directory)/(name+'.lean')
                path.write_text(f'import Proofs.Uf{part}Ready\n'+header+fixture+proof+(CHAIN if part=='Unite' else ''))
                result=subprocess.run([lake,'env','lean',str(path)],cwd=ROOT,env=env,capture_output=True,text=True)
                self.assertEqual(result.returncode,0,part+'\n'+result.stdout+result.stderr)
if __name__ == '__main__':
    disable_network()
    unittest.main()
