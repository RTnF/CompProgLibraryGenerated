"""Implicit class-local copy: source identity, method updates and lifetime."""
from pathlib import Path
import sys
import tempfile
import unittest
from unittest import mock
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'tests'),str(ROOT/'verifier'),str(ROOT/'tools')]
import test_class_call_ir as helpers
from test_class_copy_layout import PACKET
from test_union_find_original_api import SOURCE
from class_copy_layout import emit_class_layout
from offline import disable_network
import class_call_ir as calls

class ClassLocalCopyTests(unittest.TestCase):
    def check_models(self,source,qualified,checks,directory):
        generated=calls.emit_class_callers(source,qualified,'CopyCalls')
        constructors=emit_class_layout(source,qualified,'Constructors')
        helpers.ClassCallerTests.check_lean(self,generated+constructors+checks,directory)

    def test_mutated_source_copy_methods_scope_and_old_reference(self):
        with tempfile.TemporaryDirectory(prefix='class-local-copy-uf-') as directory:
            source=Path(directory)/'source.hpp'
            source.write_text(SOURCE.read_text()+r"""
int use(cp::UnionFind &u){
  u.unite(0,1);int result=0;
  {cp::UnionFind v=u;v.unite(2,3);int r=v.root(3);int s=v.size(2);int b=v.same(0,3);
   int n=v.num_groups();result=n+r+s+b;}
  int original=u.num_groups();return result*10+original;
}
int fromConst(const cp::UnionFind &u){cp::UnionFind v(u);v.unite(0,1);int n=v.num_groups();return n;}
int shadows(cp::UnionFind &u){int result=0;{cp::UnionFind v=u;v.unite(0,1);int n=v.num_groups();result=n;}
 u.unite(0,1);{cp::UnionFind v=u;v.unite(2,3);int n=v.num_groups();result=result*10+n;}return result;}
""")
            checks=r"""
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorFinish Proofs.CppLoop
 def i32 : Ty := ⟨32,true,false⟩
 def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
 def built : Option (NState × ObjectRef) := match Constructors.UnionFind_construct1_exportFuel 16 empty
     [.value (.literal i32 4)] with | .finished pair => some pair | _ => none
 #guard (match built with
   | some (s,obj) => match CopyCalls.use_arguments obj with
     | some args => match CopyCalls.use.callFuel 4096 s args with
       | .finished (out,.scalar value) => value == 63 && out.slots == s.slots &&
           out.scalars.memory.map (·.value) == ([3,4] : List Int) &&
           (out.frame.state.storage.lookup 0).map (·.items) == some ([-2,0,-1,-1].map Proofs.CppNestedVectorStore.Value.integer) &&
           out.frame.state.storage.lookup 1 == none &&
           (s.frame.elementRef 0 i32 3).bind out.frame.read == some (-1)
       | _ => false
     | _ => false
   | _ => false)
 #guard (match built with
   | some (s,obj) => match CopyCalls.fromConst_arguments obj with
     | some args => match CopyCalls.fromConst.callFuel 1024 s args with
       | .finished (out,.scalar value) => value == 3 && out.scalars.memory == s.scalars.memory &&
           out.frame.state.storage.lookup 0 == s.frame.state.storage.lookup 0 &&
           out.frame.state.storage.lookup 1 == none && out.slots == s.slots
       | _ => false
     | _ => false
   | _ => false)
"""
            checks+=r"""
 #guard (match built with
   | some (s,obj) => match CopyCalls.shadows_arguments obj with
     | some args => match CopyCalls.shadows.callFuel 4096 s args with
       | .finished (out,.scalar value) => value == 32 && out.slots == s.slots &&
           out.scalars.memory.map (·.value) == ([3,4] : List Int) &&
           out.frame.state.storage.lookup 1 == none && out.frame.state.storage.lookup 2 == none &&
           (s.frame.elementRef 0 i32 3).bind out.frame.read == some (-1)
       | _ => false
     | _ => false
   | _ => false)
"""
            self.check_models(source,'cp::UnionFind',checks,directory)
            self.assertEqual(helpers.ClassCallerTests.native(self,source,
                'cp::UnionFind u(4);std::cout << use(u) << " " << u.num_groups();cp::UnionFind v(4);std::cout << " " << fromConst(v) << " " << v.num_groups();cp::UnionFind w(4);std::cout << " " << shadows(w) << " " << w.num_groups();',directory),'63 3 3 4 32 3')

    def test_const_copy_mutable_fields_and_independent_values(self):
        with tempfile.TemporaryDirectory(prefix='class-local-copy-const-') as directory:
            source=Path(directory)/'source.hpp'
            source.write_text(PACKET+r"""
unsigned int use(const other::Packet &p){const other::Packet q=p;
  unsigned int a=q.bump();unsigned int b=p.bump();return b*10+a;}
""")
            checks=r"""
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorFinish Proofs.CppLoop
 def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
 #guard (match Constructors.Packet_construct0_exportFuel 64 empty
      [.value (.literal ⟨64,false,false⟩ 2),.value (.literal ⟨64,true,false⟩ 7)] with
   | .finished (s,obj) => match CopyCalls.use_arguments obj with
     | some args => match CopyCalls.use.callFuel 1024 s args with
       | .finished (out,.scalar value) => value == 44 && out.slots == s.slots &&
           out.scalars.memory.map (·.value) == ([8,4,1] : List Int) &&
           out.frame.state.storage.lookup 0 == s.frame.state.storage.lookup 0 &&
           out.frame.state.storage.lookup 1 == none
       | _ => false
     | _ => false
   | _ => false)
"""
            self.check_models(source,'other::Packet',checks,directory)
            self.assertEqual(helpers.ClassCallerTests.native(self,source,'const other::Packet p(2,7);std::cout << use(p);',directory),'44')

    def test_copy_source_and_constructor_identity_rejected(self):
        with tempfile.TemporaryDirectory(prefix='class-local-copy-identity-') as directory:
            source=Path(directory)/'source.hpp'
            source.write_text(PACKET+'unsigned int use(const other::Packet &p){other::Packet q=p;return q.bump();}')
            real=calls.translation_unit
            def wrong_constructor(*args,**kwargs):
                result=real(*args,**kwargs)
                for caller in kwargs['class_callers']:
                    for node in calls.walk(caller):
                        if node.get('kind')=='CXXConstructExpr':node['ctorType']={'qualType':'void (int)'}
                return result
            with mock.patch.object(calls,'translation_unit',side_effect=wrong_constructor):
                with self.assertRaisesRegex(ValueError,'audited implicit copy'):
                    calls.lower_class_callers(source,'other::Packet')
            source.write_text(PACKET+'unsigned int use(const other::Packet &p){other::Packet q=q;return q.bump();}')
            with self.assertRaisesRegex(ValueError,'source identity is not in scope'):
                calls.lower_class_callers(source,'other::Packet')
            for declaration in ('static other::Packet q=p;', 'thread_local other::Packet q=p;',
                                'thread_local unsigned int n=0;'):
                source.write_text(PACKET+'unsigned int use(const other::Packet &p){'+declaration+'return p.bump();}')
                with self.subTest(declaration=declaration):
                    with self.assertRaisesRegex(ValueError,'automatic storage'):
                        calls.lower_class_callers(source,'other::Packet')

    def test_unsupported_class_local_is_not_silently_omitted(self):
        with tempfile.TemporaryDirectory(prefix='class-local-copy-reject-') as directory:
            source=Path(directory)/'source.hpp'
            source.write_text('#include <vector>\nstruct Implicit {std::vector<int> data;int count=7;int get()const{return count;}};'
                              'int bad(){Implicit p;return p.get();}')
            with self.assertRaisesRegex(ValueError,'defined constructor stage'):
                calls.lower_class_callers(source,'Implicit')

if __name__=='__main__':
    disable_network()
    unittest.main()
