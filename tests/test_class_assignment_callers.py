"""Actual same-TU assignment callers, destination identity and C++17 order."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'verifier'), str(ROOT/'tests'), str(ROOT/'tools')]
import class_call_ir as calls
from class_copy_layout import emit_class_layout
import test_class_call_ir as helpers
from test_union_find_original_api import SOURCE
from offline import disable_network

CALLERS = '''
int assign_only(cp::UnionFind&a,const cp::UnionFind&b){a=b;return a.num_groups();}
int assigned_size(cp::UnionFind&a,const cp::UnionFind&b){return (a=b).size(0);}
int chained(cp::UnionFind&a,cp::UnionFind&b,const cp::UnionFind&c){a=b=c;return a.num_groups();}
int notation_order(cp::UnionFind&a,cp::UnionFind&b){(a=b)=(b=a);return a.num_groups();}
int explicit_order(cp::UnionFind&a,cp::UnionFind&b){(a=b).operator=(b=a);return a.num_groups();}
void assign_void(cp::UnionFind&a,const cp::UnionFind&b){a=b;return;}
int copy_result(cp::UnionFind&a,const cp::UnionFind&b){cp::UnionFind c=(a=b);return c.num_groups();}
'''

CHECKS = r'''
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppConstructorFinish Proofs.CppLoop
open Proofs.CppNestedInvoke
def i32 : Ty := ⟨32,true,false⟩
def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
def construct (s : NState) (n : Int) : Option (NState × ObjectRef) :=
  match Constructors.UnionFind_construct1_exportFuel 32 s [.value (.literal i32 n)] with
  | .finished pair => some pair | _ => none
def initial : Option (NState × ObjectRef × ObjectRef × ObjectRef) := do
  let (s,a) ← construct empty 4
  let (s,b) ← construct s 2
  let (s,c) ← construct s 3
  pure (s,a,b,c)
#guard initial.isSome
-- Each case starts from independently constructed receivers; their group counts differ.
def execute (p : CallerProgram) (args : ObjectRef → ObjectRef → Option (List NArgument))
    (alias : Bool := false) : Option (NState × Int) := do
  let (s,a,b,_) ← initial
  let actuals ← args a (if alias then a else b)
  match p.callFuel 2048 s actuals with
  | .finished (out,.scalar value) => pure (out,value) | _ => none
#guard (execute AC.assign_only AC.assign_only_arguments).map (·.2) == some 2
#guard (execute AC.assigned_size AC.assigned_size_arguments).map (·.2) == some 1
#guard (execute AC.notation_order AC.notation_order_arguments).map (·.2) == some 4
#guard (execute AC.explicit_order AC.explicit_order_arguments).map (·.2) == some 2
#guard (execute AC.assign_only AC.assign_only_arguments true).map (·.2) == some 4
#guard (execute AC.copy_result AC.copy_result_arguments).map (·.2) == some 2
#guard (match execute AC.assign_only AC.assign_only_arguments with
  | some (s,_) => s.scalars.memory.map (·.value) == ([2,2,2,2,3,3] : List Int) &&
      s.slots.length == 9 && s.scope == 0 &&
      (s.frame.state.storage.lookup 0).map (·.items) ==
        some ([-1,-1].map Proofs.CppNestedVectorStore.Value.integer)
  | _ => false)
#guard (do
  let (s,a,b,c) ← initial
  let args ← AC.chained_arguments a b c
  match AC.chained.callFuel 2048 s args with
  | .finished (out,.scalar value) => some (value == 3 &&
      out.scalars.memory.map (·.value) == ([3,3,3,3,3,3] : List Int))
  | _ => none) == some true
#guard (do
  let (s,a,b,_) ← initial
  let args ← AC.assign_void_arguments a b
  match AC.assign_void.callFuel 2048 s args with
  | .finished (out,_) => some (out.scalars.memory.map (·.value) == ([2,2,2,2,3,3] : List Int))
  | _ => none) == some true
'''

class AssignmentCallerTests(unittest.TestCase):
    def test_callee_and_object_identity_rejected(self):
        with tempfile.TemporaryDirectory(prefix='assignment-caller-reject-') as directory:
            source = Path(directory)/'source.hpp'
            source.write_text(SOURCE.read_text()+'\nvoid use(cp::UnionFind&a,const cp::UnionFind&b){a=b;}')
            real = calls.translation_unit
            for mutation in ('callee','source','const'):
                def changed(*args, **kwargs):
                    result = real(*args, **kwargs)
                    caller = kwargs['class_callers'][0]
                    expression = next(n for n in calls.walk(caller) if n.get('kind') == 'CXXOperatorCallExpr')
                    if mutation == 'callee':
                        expression['inner'][0]['inner'][0]['referencedDecl']['id'] = 'foreign'
                    elif mutation == 'source':
                        node = expression['inner'][2]
                        while node.get('kind') == 'ImplicitCastExpr':node = node['inner'][0]
                        node['referencedDecl']['id'] = 'foreign'
                    else:
                        parameter = next(n for n in caller['inner'] if n.get('kind') == 'ParmVarDecl')
                        parameter['type']['qualType'] = 'const cp::UnionFind &'
                    return result
                with self.subTest(mutation=mutation), mock.patch.object(calls,'translation_unit',side_effect=changed):
                    with self.assertRaises(ValueError):
                        calls.lower_class_callers(source,'cp::UnionFind',assignment=True)

    def test_assignment_does_not_require_copy_construction(self):
        with tempfile.TemporaryDirectory(prefix='assignment-no-copy-') as directory:
            source = Path(directory)/'source.hpp'
            source.write_text('''#include <vector>
namespace test {struct Packet {
std::vector<int> values;int n;
Packet():values(2,0),n(2){} Packet(const Packet&)=delete;
int size() const{return n;}
};}
int use(test::Packet&a,const test::Packet&b){a=b;return a.size();}
''')
            generated = calls.emit_class_callers(source,'test::Packet','NoCopy',assignment=True)
            helpers.ClassCallerTests.check_lean(self,generated,directory)
            with self.assertRaises((ValueError,subprocess.CalledProcessError)):
                calls.lower_class_callers(source,'test::Packet')

    def test_generated_and_native(self):
        with tempfile.TemporaryDirectory(prefix='class-assignment-callers-') as directory:
            source = Path(directory)/'source.hpp'
            source.write_text(SOURCE.read_text()+CALLERS)
            generated = calls.emit_class_callers(source,'cp::UnionFind','AC',assignment=True)
            constructors = emit_class_layout(source,'cp::UnionFind','Constructors')
            helpers.ClassCallerTests.check_lean(self,generated+constructors+CHECKS,directory)
            main = '''
cp::UnionFind a(4),b(2),c(3);
std::cout<<assign_only(a,b)<<' ';
cp::UnionFind d(4),e(2);std::cout<<assigned_size(d,e)<<' ';
cp::UnionFind f(4),g(2);std::cout<<notation_order(f,g)<<' ';
cp::UnionFind h(4),i(2);std::cout<<explicit_order(h,i)<<' ';
cp::UnionFind j(4);std::cout<<assign_only(j,j)<<' ';
cp::UnionFind k(4),l(2);std::cout<<copy_result(k,l)<<' ';
std::cout<<chained(a,b,c)<<' ';assign_void(a,c);std::cout<<a.num_groups();
'''
            self.assertEqual(helpers.ClassCallerTests.native(self,source,main,directory),'2 1 4 2 4 2 3 3')

if __name__ == '__main__':
    disable_network()
    unittest.main()
