"""Class-local constructors, field views, scalar/void calls and lifetime."""
from pathlib import Path
import sys,tempfile,unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'tests'),str(ROOT/'verifier'),str(ROOT/'tools')]
import test_class_call_ir as helpers
from test_union_find_original_api import SOURCE
from test_class_copy_layout import PACKET
from offline import disable_network
import class_call_ir as calls

class ClassConstructTests(unittest.TestCase):
 def check_models(self,source,qualified,checks,directory):
  generated=calls.emit_class_callers(source,qualified,'Generated')
  helpers.ClassCallerTests.check_lean(self,generated+checks,directory)

 def test_default_sized_const_construct_copy_all_methods_and_cleanup(self):
  with tempfile.TemporaryDirectory(prefix='class-construct-uf-') as directory:
   source=Path(directory)/'source.hpp'
   source.write_text(SOURCE.read_text()+r'''
int use(int n){cp::UnionFind d;int zero=d.num_groups();cp::UnionFind u(n);u.unite(0,1);
 int count=u.num_groups();int same=u.same(0,1);int root=u.root(1);int size=u.size(1);
 const cp::UnionFind c(4);cp::UnionFind v(c);v.unite(2,3);int vc=v.num_groups();
 return zero+count*100+same*10+root+size+vc;}
int cleanup(int n){int r=0;for(int i=0;i<3;++i){cp::UnionFind u(n);u.unite(0,1);
 int g=u.num_groups();r=r+g;if(i==1)break;}return r;}
int unused(int n){cp::UnionFind u(n);return 9;}
''')
   checks=r'''
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
 def i32 : Ty := ⟨32,true,false⟩
 def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
 #guard (match Generated.use.callFuel 4096 empty [.value (.literal i32 4)] with
   | .finished (out,.scalar value) => value == 315 && out.scalars.memory == [] && out.slots == [] &&
       [0,1,2,3].all (fun owner => (out.frame.state.storage.lookup owner).isNone)
   | _ => false)
 #guard (match Generated.cleanup.callFuel 4096 empty [.value (.literal i32 4)] with
   | .finished (out,.scalar value) => value == 6 && out.scalars.memory == [] && out.slots == [] &&
       [0,1].all (fun owner => (out.frame.state.storage.lookup owner).isNone)
   | _ => false)
 #guard (match Generated.unused.callFuel 128 empty [.value (.literal i32 4)] with
   | .finished (out,.scalar value) => value == 9 && out.scalars.memory == [] &&
       (out.frame.state.storage.lookup 0).isNone
   | _ => false)
'''
   self.check_models(source,'cp::UnionFind',checks,directory)
   self.assertEqual(helpers.ClassCallerTests.native(self,source,
     'std::cout << use(4) << " " << cleanup(4) << " " << unused(4);',directory),'315 6 9')

 def test_const_mutable_ctor_internal_method_and_scalar_reference(self):
  with tempfile.TemporaryDirectory(prefix='class-construct-counter-') as directory:
   source=Path(directory)/'source.hpp'
   source.write_text(r'''#include <vector>
struct Counter {
 std::vector<int> data; const int stamp; mutable int count; mutable bool ready;
 Counter(int n,int &observed):data(n,0),stamp(n),count(0),ready(false){touch();observed=count;}
 void touch()const{++count;ready=true;}
 int bump()const{touch();return count;}
};
int use(int &seen){const Counter p(2,seen);p.touch();int x=p.bump();Counter q=p;q.touch();int y=q.bump();
 int z=p.bump();return x*100+y*10+z;}
''')
   checks=r'''
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
 def i32 : Ty := ⟨32,true,false⟩
 def state : NState := ⟨⟨[⟨i32,0⟩],[⟨0,true⟩],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[.scalar 0],0,0⟩
 #guard (match Generated.use.callFuel 1024 state [.scalarReference 0] with
   | .finished (out,.scalar value) => value == 354 && out.scalars.memory == [⟨i32,1⟩] &&
       out.slots == state.slots && (out.frame.state.storage.lookup 0).isNone &&
       (out.frame.state.storage.lookup 1).isNone
   | _ => false)
'''
   self.check_models(source,'Counter',checks,directory)
   self.assertEqual(helpers.ClassCallerTests.native(self,source,
      'int seen=0;std::cout << use(seen) << " " << seen;',directory),'354 1')

 def test_previously_unsupported_local_now_has_a_generated_body(self):
  with tempfile.TemporaryDirectory(prefix='class-construct-packet-') as directory:
   source=Path(directory)/'source.hpp'
   source.write_text(PACKET+'unsigned int bad(){other::Packet p(2,7);return p.bump();}')
   checks=r"""
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
 def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
 #guard (match Generated.bad.callFuel 512 empty [] with
   | .finished (out,.scalar value) => value == 4 && out.scalars.memory == [] &&
       out.slots == [] && (out.frame.state.storage.lookup 0).isNone
   | _ => false)
"""
   self.check_models(source,'other::Packet',checks,directory)
   self.assertEqual(helpers.ClassCallerTests.native(self,source,'std::cout << bad();',directory),'4')

 def test_same_arity_constructor_overloads(self):
  with tempfile.TemporaryDirectory(prefix='class-construct-overload-') as directory:
   source=Path(directory)/'source.hpp'
   source.write_text("""#include <vector>
struct Number {
 std::vector<int> data;int tag;
 Number(int n):data(1,n),tag(10){} Number(unsigned int n):data(1,n),tag(20){}
 int get()const{return tag;}
};
int use(){Number a(1);const Number b(1u);int x=a.get();int y=b.get();return x*100+y;}
""")
   checks=r"""
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
 def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
 #guard (match Generated.use.callFuel 512 empty [] with
   | .finished (out,.scalar value) => value == 1020 && out.scalars.memory == [] &&
       (out.frame.state.storage.lookup 0).isNone && (out.frame.state.storage.lookup 1).isNone
   | _ => false)
"""
   self.check_models(source,'Number',checks,directory)
   self.assertEqual(helpers.ClassCallerTests.native(self,source,'std::cout << use();',directory),'1020')

 def test_unsupported_implicit_default_and_early_return_callee_rejected(self):
  with tempfile.TemporaryDirectory(prefix='class-construct-reject-') as directory:
   source=Path(directory)/'source.hpp'
   source.write_text("""#include <vector>
struct Implicit {std::vector<int> data;int count=7;int get()const{return count;}};
int use(){Implicit p;return p.get();}
""")
   with self.assertRaisesRegex(ValueError,'defined constructor stage'):
    calls.lower_class_callers(source,'Implicit')
   source.write_text("""#include <vector>
struct Early {std::vector<int> data;int count;
 Early(int n):data(n,0),count(0){int x=pick(n);count=x;}
 int pick(int n){if(n==0)return 1;return 2;}
};
int use(){Early p(2);return p.pick(2);}
""")
   with self.assertRaisesRegex(ValueError,'early returns cannot be inlined'):
    calls.lower_class_callers(source,'Early')

if __name__=='__main__':
 disable_network();unittest.main()
