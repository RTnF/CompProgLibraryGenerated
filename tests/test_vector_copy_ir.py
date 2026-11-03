"""Audited C++ vector copies execute through NStmt and retire local ownership."""
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'verifier'))
sys.path.insert(0,str(ROOT/'tools'))
import nested_ir
from test_scalar_ir import lean_environment
from test_cpp_nested_copy import HEADER, CHECKS as FIXTURE
from test_append_row import initial
from check_public import FLAGS, check_compiler
from offline import disable_network

SOURCE = r'''
#include <vector>
namespace cp {
int mutable_copy(const std::vector<int>& source) {
  std::vector<int> target(source); target[1]=42; return target[1];
}
int const_copy(const std::vector<std::vector<int>>& source, unsigned long index) {
  const std::vector<int> target(source[index]); return target[1];
}
int borrowed_write(std::vector<int>& source) { source[1]=33; return source[1]; }
int scoped_copy(const std::vector<int>& source) {
  int result=0;
  { std::vector<int> target(source); target[1]=23; result=target[1]; }
  return result;
}
}
'''
CHECKS = r'''
namespace CopyIRChecks
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppMixedInvoke Proofs.CppLoop
 def caller : NState := ⟨⟨[],[],0,0,0⟩,before,(List.range before.bindings.length).map Location.vector,9,100000000⟩
 def correct (expected : Int) : Outcome (NState × Ret) → Bool
  | .finished (state,.scalar value) => value == expected && state.frame.state.wellFormed &&
      state.frame.bindings == before.bindings && state.frame.read saved == some (-1) &&
      state.frame.state.storage.lookup 2 == before.state.storage.lookup 2 &&
      state.frame.state.storage.lookup 6 == none && state.slots == caller.slots &&
      state.scalars.memory == caller.scalars.memory && state.scope == caller.scope
  | _ => false
 #guard correct 42 (CopyIR.mutable_copy.callFuel 128 caller [.vectorReference 4])
 def rootBuffer : Buffer Value := ⟨4,[.integer 77,.integer (-9)],2,64,0⟩
 def rootCaller : NState := {caller with
   frame := {before with
     state := {before.state with
       storage := {before.state.storage with objects := before.state.storage.objects.set 4 (some rootBuffer)}}}}
 #guard rootCaller.frame.state.wellFormed
 #guard correct 42 (CopyIR.mutable_copy.callFuel 128 rootCaller [.vectorReference 2])
 #guard correct 23 (CopyIR.scoped_copy.callFuel 128 rootCaller [.vectorReference 2])
 #guard (match CopyIR.mutable_copy.callFuel 128 rootCaller [.vectorReference 2] with
   | .finished (state,_) => state.frame.state.storage.lookup 4 == some rootBuffer
   | _ => false)
 #guard correct (-1) (CopyIR.const_copy.callFuel 128 caller [.vectorReference 1,.value (.literal ⟨64,false,false⟩ 1)])
 #guard correct 23 (CopyIR.scoped_copy.callFuel 128 caller [.vectorReference 4])
 #guard (match CopyIR.borrowed_write.callFuel 128 caller [.vectorReference 3] with
   | .finished (state,.scalar value) => value == 33 && state.frame.read saved == some 33 &&
       state.frame.bindings == before.bindings && state.slots == caller.slots &&
       state.scope == caller.scope
   | _ => false)
 #guard (match CopyIR.borrowed_write.callFuel 128 caller [.vectorReference 4] with
   | .fault => true | _ => false)
 def stale : NState := {caller with
   frame := {before with
     bindings := before.bindings.set 4 ⟨2,atom,false,.child ⟨0,99,1⟩⟩}}
 #guard (match CopyIR.mutable_copy.callFuel 128 stale [.vectorReference 4] with
   | .fault => true | _ => false)
 #guard (bindOne caller (.vectorChild 3 ⟨0,0,1⟩ i32 false)).isNone
 #guard (bindOne caller (.vectorChild 2 ⟨0,99,1⟩ i32 false)).isNone
 example (s : NState) (source : Container) (ty : Ty) (writable : Bool) :
   (NStmt.copyVector source ty writable).run s = Proofs.CppCopyStatement.run s source ty writable := rfl
end CopyIRChecks
'''

class VectorCopyIRTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.directory = tempfile.TemporaryDirectory(prefix='vector-copy-ir-')
        cls.path = Path(cls.directory.name)/'source.hpp'
        cls.path.write_text(SOURCE)
        cls.ir = nested_ir.lower_source(cls.path)
        cls.emitted = nested_ir.emit_lean(cls.ir,'CopyIR')

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def test_ast_identity_types_permissions_and_renaming(self):
        functions = {f['name']:f for f in self.ir['functions']}
        first = functions['mutable_copy']['body'][0]
        self.assertEqual((first['kind'],first['writable'],first['source']['kind']),('copy_vector',True,'local'))
        second = functions['const_copy']['body'][0]
        self.assertEqual((second['kind'],second['writable'],second['source']['kind']),('copy_vector',False,'row'))
        self.assertIn('.copyVector',self.emitted)
        renamed = re.sub(r'\btarget\b','unrelated',SOURCE)
        renamed = re.sub(r'\bmutable_copy\b','other_copy',renamed)
        path=Path(self.directory.name)/'renamed.hpp';path.write_text(renamed)
        other={f['name']:f for f in nested_ir.lower_source(path)['functions']}
        self.assertEqual(other['other_copy']['body'],functions['mutable_copy']['body'])

    def test_generated_execution_scope_retirement_and_old_references(self):
        proof = ('import Proofs.CppCopyStatementFacts\n'+self.emitted+
                 HEADER.replace('import Proofs.CppFrameCopy\n','')+
                 f'\ndef initial := {initial(3,8)}\n'+FIXTURE+CHECKS)
        path=Path(self.directory.name)/'checks.lean';path.write_text(proof)
        lake,env=lean_environment()
        result=subprocess.run([lake,'env','lean',str(path)],cwd=ROOT,env=env,capture_output=True,text=True)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_native_same_functions(self):
        check_compiler()
        path=Path(self.directory.name)/'checks.cpp'
        path.write_text(SOURCE+r'''
#include <cassert>
int main(){std::vector<std::vector<int>> source{{10,0},{11,-1},{12,-2}};
source[1].reserve(17); auto old=source;
assert(cp::mutable_copy(source[1])==42); assert(cp::const_copy(source,1)==-1);
assert(cp::scoped_copy(source[1])==23); assert(source==old && source[1].capacity()==17);
assert(cp::borrowed_write(source[1])==33 && source[1][1]==33);
std::vector<int> root{77,-9}; auto oldRoot=root;
assert(cp::mutable_copy(root)==42 && cp::scoped_copy(root)==23 && root==oldRoot);}
''')
        binary=Path(self.directory.name)/'checks'
        result=subprocess.run(['g++',*FLAGS,'-fsanitize=undefined','-fno-sanitize-recover=all',str(path),'-o',str(binary)],
                              cwd=ROOT,capture_output=True,text=True)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)
        result=subprocess.run([str(binary)],cwd=ROOT,capture_output=True,text=True)
        self.assertEqual(result.returncode,0,result.stdout+result.stderr)

    def test_unsupported_nested_copy_and_allocator_overload_remain_rejected(self):
        cases=[
            'unsigned long f(const std::vector<std::vector<int>>& v){std::vector<std::vector<int>> c(v);return c.size();}',
            'unsigned long f(const std::vector<int>& v){std::vector<int> c(v,std::allocator<int>());return c.size();}',
            'unsigned long f(const std::vector<bool>& v){std::vector<bool> c(v);return c.size();}',
            'unsigned long f(){std::vector<int> c(c);return c.size();}',
        ]
        for index,body in enumerate(cases):
            with self.subTest(case=index):
                path=Path(self.directory.name)/f'bad{index}.hpp';path.write_text('#include <vector>\n'+body+'\n')
                with self.assertRaises(ValueError):
                    nested_ir.lower_source(path)

if __name__ == '__main__':
    disable_network()
    unittest.main()
