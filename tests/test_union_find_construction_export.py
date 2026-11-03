"""Persistent constructor fields, actual subsequent methods, and temporary retirement."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from nested_ir import lower_source,emit_lean
from test_union_find_construction import HEADER
from test_union_find_original_api import HEADER as CALLER_HEADER
from offline import disable_network
ROOT=Path(__file__).resolve().parent.parent
BUNDLE='''#include <vector>
namespace cp {struct Bundle {
 std::vector<int> data; int count; bool ready; unsigned long long token;
 Bundle(int n):data(n,-1),count(7),ready(true),token(18446744073709551615ULL) {
   std::vector<int> temporary(3,9);
 }
};}
'''
CHECKS='''
open Proofs.UfConstructionExport Proofs.CppConstructorFinish Proofs.CppRootModel
 def noHeap : Heap := fun _ => none
 theorem noModels (s : NState) : HeapModels s.frame.state noHeap := by
   intro owner view found
   simp [noHeap] at found
 example := construct_default empty noHeap (by decide +kernel) (noModels empty) (by decide +kernel)
 example := construct_sized empty noHeap (by decide +kernel) (noModels empty) (by decide +kernel)
   (.literal i32 0) 0 (by decide) rfl rfl (by decide +kernel)
 def populated := caller [-1,-1] 2
 def nAlias : NExpr := .variable i32 2
 example := construct_sized populated noHeap (by decide +kernel) (noModels populated) (by decide +kernel)
   nAlias 2 (by decide) rfl rfl (by decide +kernel)
 def built := UnionFind_construct1.constructFuel 8 populated [.value nAlias] (vectorField true) (.integer i32) (fields true)
 def receiver := (match built with | .finished pair => pair | _ => (empty,reference empty 0))
 #guard (match built with | .finished _ => true | _ => false)
 #guard receiver.2 == reference populated 2
 #guard receiver.1.scalars.memory == [⟨i32,2⟩,⟨i32,9876⟩,⟨i32,2⟩,⟨i32,2⟩]
 #guard receiver.1.scalars.bindings == populated.scalars.bindings ++ [⟨2,true⟩,⟨3,true⟩]
 #guard receiver.1.frame.bindings == populated.frame.bindings ++ [⟨1,.integer i32,true,.root 0⟩]
 #guard receiver.1.frame.state.storage.lookup 0 == populated.frame.state.storage.lookup 0
 #guard receiver.1.scope == populated.scope
 def args (obj : ObjectRef) : List NArgument :=
   [.vectorReference obj.vectorSlot,.scalarReference obj.scalarSlots[0]!,
     .value (.variable i32 obj.scalarSlots[1]!)]
 def countCall := Proofs.UnionFindCandidateInstance.UnionFind_num_groups.callFuel 64 receiver.1 (args receiver.2)
 #guard (match countCall with | .finished (_, .scalar n) => n == 2 | _ => false)
 def united := Proofs.UnionFindCandidateInstance.UnionFind_unite.callFuel 64 receiver.1
   (args receiver.2 ++ [.value (.literal i32 0),.value (.literal i32 1)])
 #guard (match united with
   | .finished (s,.scalar r) => r == 0 &&
       s.scalars.memory == [⟨i32,2⟩,⟨i32,9876⟩,⟨i32,1⟩,⟨i32,2⟩] &&
       s.frame.state.storage.lookup 0 == populated.frame.state.storage.lookup 0 &&
       (s.frame.state.storage.lookup 1 |>.map (·.items)) == some [.integer (-2),.integer 0] &&
       s.slots == receiver.1.slots && s.scalars.bindings == receiver.1.scalars.bindings
   | _ => false)
 #guard (match UnionFind_construct0.constructFuel 8 populated [] (vectorField false) (.integer i32) (fields false) with
   | .finished (s,obj) => s.scalarCell obj.scalarSlots[0]! i32 == some (⟨2,true⟩,⟨i32,0⟩) &&
       s.scalarCell obj.scalarSlots[1]! i32 == some (⟨3,true⟩,⟨i32,0⟩) &&
       (s.frame.state.storage.lookup 1 |>.map (·.items)) == some [] &&
       s.frame.state.storage.lookup 0 == populated.frame.state.storage.lookup 0
   | _ => false)
 #guard UnionFind_construct1.constructFuel 0 populated [.value nAlias] (vectorField true) (.integer i32) (fields true) == .exhausted
 #guard UnionFind_construct1.constructFuel 8 populated [.value nAlias] (vectorField true) (.integer i32) [⟨2,⟨64,false,false⟩⟩] == .fault
 example (c : NState) (heap : Heap) (valid : c.frame.state.wellFormed = true)
   (models : HeapModels c.frame.state heap) (lengths : c.frame.rootWritable.length = c.frame.state.forest.objects.length)
   (en : NExpr) (n : Nat) (endpoint : n = 2147483647) (scalar : en.scalarOnly = true)
   (type : en.resultType = i32) (value : en.denote (Proofs.CppNestedEval.envOf c) = some (n : Int)) :=
   construct_sized c heap valid models lengths en n (by omega) scalar type value
'''
BUNDLE_CHECKS='''
 def bT : Ty := ⟨1,false,true⟩
 def u64 : Ty := ⟨64,false,false⟩
 def bundle := BundleModel.Bundle_construct0.constructFuel 16 empty [.value (.literal i32 2)] 1 (.integer i32)
   [⟨2,i32⟩,⟨3,bT⟩,⟨4,u64⟩]
 #guard (match bundle with
   | .finished (s,obj) => obj == reference empty 3 &&
       s.scalars.memory == [⟨i32,7⟩,⟨bT,1⟩,⟨u64,18446744073709551615⟩] &&
       (s.frame.state.storage.lookup 0 |>.map (·.items)) == some [.integer (-1),.integer (-1)] &&
       s.frame.state.storage.lookup 1 == none && s.frame.state.storage.objects.length == 2 &&
       s.frame.state.storage.work == 8 && s.frame.bindings == [⟨0,.integer i32,true,.root 0⟩]
   | _ => false)
 def readonlyProgram : NProgram := ⟨[],.unit,
   .sequence (.primitive (.declareVector i32 true))
     (.sequence (.primitive (.declare bT false (.literal bT 1))) (.primitive .skip))⟩
 #guard (match readonlyProgram.constructFuel 8 empty [] 0 (.integer i32) [⟨1,bT⟩] with
   | .finished (s,_) => s.scalarCell 1 bT == some (⟨0,false⟩,⟨bT,1⟩) &&
       (NStmt.assign 1 bT (.literal bT 0)).run s == none
   | _ => false)
'''
class UnionFindConstructionExportTests(unittest.TestCase):
    def test_persistent_receiver_and_generic_field_payloads(self):
        with tempfile.TemporaryDirectory(prefix='uf-construction-export-') as directory:
            root=Path(directory);source=root/'bundle.hpp';source.write_text(BUNDLE)
            generated=emit_lean(lower_source(source,[root],construction_stages=True),'BundleModel')
            generated='\n'.join(line for line in generated.splitlines() if not line.startswith('import '))
            proof=root/'checks.lean'
            proof.write_text('import Proofs.UfConstructionExport\n'+HEADER+CALLER_HEADER+generated+CHECKS+BUNDLE_CHECKS)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            native=root/'native.cpp';binary=root/'native'
            native.write_text('#include "bundle.hpp"\n#include <cassert>\nint main(){'
                'for(int n : {0,1,2,17}) { cp::Bundle b(n);'
                'assert(b.data==std::vector<int>(n,-1));'
                'assert(b.count==7 && b.ready && b.token==18446744073709551615ULL);}}')
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                str(native),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)
if __name__=='__main__':disable_network();unittest.main()
