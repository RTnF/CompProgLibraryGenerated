"""Constructor export permissions, immutable values, resources and native calls."""
from pathlib import Path
import sys,tempfile,unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'tests'),str(ROOT/'verifier'),str(ROOT/'tools')]
import test_class_call_ir as helpers
from class_copy_layout import emit_class_layout
from class_call_ir import emit_class_callers
from offline import disable_network
SOURCE='''#include <vector>
struct Counter {
 std::vector<int> data; int count; mutable int touches; mutable bool ready;
 Counter(int n):data(n,0),count(n),touches(0),ready(false){}
 int peek() const {++touches;ready=true;return count;}
};
int use(const Counter &p){int a=p.peek();int b=p.peek();return a*10+b;}
'''
CHECKS=r'''
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorFinish Proofs.CppLoop
open Proofs.CppConstructorView
 def i32 : Ty := ⟨32,true,false⟩
 def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
 def make (constant : Bool) := Constructors.Counter_construct0_exportViewFuel 32 empty
   [.value (.literal i32 3)] constant
 #guard make false == Constructors.Counter_construct0_exportFuel 32 empty [.value (.literal i32 3)]
 #guard (match make false,make true with
   | .finished (before,obj),.finished (after,view) => obj == view &&
       before.scalars.memory == after.scalars.memory && before.work == after.work &&
       before.scalars.peak == after.scalars.peak && before.peak == after.peak &&
       before.frame.state.storage.peak == after.frame.state.storage.peak &&
       before.frame.rootWritable == after.frame.rootWritable &&
       (before.scalarCell 1 i32).map (fun (b,_) => b.writable) == some true &&
       (after.scalarCell 1 i32).map (fun (b,_) => b.writable) == some false &&
       (after.scalarCell 2 i32).map (fun (b,_) => b.writable) == some true &&
       (after.frame.bindings[0]?).map (·.writable) == some false &&
       (NStmt.assign 1 i32 (.literal i32 9)).run after == none &&
       (NStmt.write (.local view.vectorSlot) i32 (.literal i32 0) (.literal i32 9)).run after == none
   | _,_ => false)
 #guard (match make true with
   | .finished (s,obj) => match Methods.use_arguments obj with
     | some args => match Methods.use.callFuel 256 s args with
       | .finished (out,.scalar value) => value == 33 &&
           out.scalars.memory.map (·.value) == ([3,2,1] : List Int)
       | _ => false
     | _ => false
   | _ => false)
 #guard constructProfileFuel Constructors.Counter_construct0 32 empty [.value (.literal i32 3)]
   Constructors.Counter_construct0_vectorSlot Constructors.Counter_construct0_scalarFields
   ⟨i32,false,[(⟨64,true,false⟩,false),(i32,true),(⟨1,false,true⟩,true)]⟩ == .fault
'''

class ConstructorViewTests(unittest.TestCase):
 def test_qualified_export_values_resources_mutable_and_invalid_type(self):
  with tempfile.TemporaryDirectory(prefix='constructor-view-') as directory:
   source=Path(directory)/'source.hpp';source.write_text(SOURCE)
   proof_import='import Proofs.CppConstructorView\n'
   generated=emit_class_layout(source,'Counter','Constructors')
   methods=emit_class_callers(source,'Counter','Methods')
   helpers.ClassCallerTests.check_lean(self,proof_import+generated+methods+CHECKS,directory)
   self.assertEqual(helpers.ClassCallerTests.native(self,source,
     'const Counter p(3);std::cout << use(p) << " " << p.touches << " " << p.ready;',directory),'33 2 1')

 def test_declared_const_fields_cannot_gain_mutable_grants(self):
  with tempfile.TemporaryDirectory(prefix='constructor-view-declared-const-') as directory:
   source=Path(directory)/'source.hpp'
   source.write_text("""#include <vector>
struct ReadOnly { const std::vector<int> data; const int count;
 ReadOnly(int n):data(n,0),count(n){} int peek()const{return count;} };
int use(const ReadOnly &p){return p.peek();}
""")
   proof_import='import Proofs.CppConstructorView\n'
   generated=emit_class_layout(source,'ReadOnly','Constructors')
   checks=r"""
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorFinish Proofs.CppLoop
open Proofs.CppConstructorView
 def i32 : Ty := ⟨32,true,false⟩
 def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
 def make (profile : Proofs.CppClassCopy.Profile) := constructProfileFuel Constructors.ReadOnly_construct0
   32 empty [.value (.literal i32 3)] Constructors.ReadOnly_construct0_vectorSlot
   Constructors.ReadOnly_construct0_scalarFields profile
 #guard make Constructors.constProfile == Constructors.ReadOnly_construct0_exportFuel 32 empty [.value (.literal i32 3)]
 #guard make ⟨i32,true,[(i32,false)]⟩ == .fault
 #guard make ⟨i32,false,[(i32,true)]⟩ == .fault
 #guard make ⟨i32,false,[]⟩ == .fault
"""
   helpers.ClassCallerTests.check_lean(self,proof_import+generated+checks,directory)
   self.assertEqual(helpers.ClassCallerTests.native(self,source,
     'const ReadOnly p(3);std::cout << use(p);',directory),'3')

if __name__=='__main__':
 disable_network();unittest.main()
