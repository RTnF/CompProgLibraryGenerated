"""Partial method coverage, declaration-order mapping, dependencies and aliasing."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'verifier'),str(ROOT/'tools'),str(ROOT/'tests')]
from context_method_ir import emit_context_methods,lower_context_methods
from class_copy import audit_class_copy
from check_public import check_compiler
from offline import disable_network
import test_context_method_ir as base

LEGACY=ROOT/'experiments/library3/cpp/Graph/UnionFind.hpp'
NAMESPACE='Proofs.Generated.DisjointSetMethods'

# The unselected default-argument and recursive methods must not be executed/lowered.
PROBE=r'''
#include <vector>
struct Probe {
  int stamp;
  std::vector<int> data;
  int count;
  int touch(int& value){value=9;return count;}
  int outer(int& value){return touch(value);}
  int view()const{return count;}
  int recursive(int x){return x ? recursive(x-1) : count;}
  int unused(int delta=1){return count+delta;}
};
'''

PROBE_CHECKS=r'''
namespace SelectionChecks
open Proofs.CppMoveContext Proofs.CppNestedProgram
abbrev ty : Proofs.CppScalar.Ty := ⟨32,true,false⟩
abbrev limit := Proofs.CppVectorBindings.sizeLimit ty
def initial : Context := ⟨⟨⟨[some ⟨some 0,0,true,limit⟩],
  [some ⟨⟨0,[7],1,limit,0⟩,fun _ => 0⟩],[],0,0,0⟩,[⟨0,true⟩]⟩,
  ⟨[⟨ty,17⟩,⟨ty,4⟩],[⟨0,true⟩,⟨1,true⟩],0,0,0⟩,
  [.vector 0,.scalar 0,.scalar 1],0,0⟩
example : SelectedProbe.coverage = "selected_context_method_receivers" := rfl
example : SelectedProbe.declaredFieldNames = ["stamp","data","count"] := rfl
example : SelectedProbe.fieldPermutation = [1,0,2] := rfl
example : SelectedProbe.selectedMethods = ["outer","view"] := rfl
example : SelectedProbe.dependencyMethods = ["touch"] := rfl
example : SelectedProbe.«Probe_outer_arguments» ⟨0,[1,2]⟩ [.scalarReference 2] =
  some [.vectorReference 0,.scalarReference 1,.scalarReference 2,.scalarReference 2] := rfl
#guard (match SelectedProbe.«Probe_outer_callFuel» 32 initial ⟨0,[1,2]⟩ [.scalarReference 2] with
  | .finished (out,result) => result == .scalar 9 && out.scalars.memory.map (·.value) == [17,9]
    && (out.objects.heap.allocation 0).map (fun a => a.buffer.items) == some [7]
  | _ => false)
example : SelectedProbe.Methods.Probe_view.parameters =
  [.vector ty false,.scalar ty true false,.scalar ty true false] := rfl
#guard (match SelectedProbe.«Probe_view_callFuel» 16 initial ⟨0,[1,2]⟩ [] with
  | .finished (out,result) => result == .scalar 4 && out.scalars.memory.map (·.value) == [17,4]
  | _ => false)
end SelectionChecks
'''

class ContextMethodSelectionTests(unittest.TestCase):
    check_lean=base.ContextMethodIRTests.check_lean

    def test_original_legacy_getter_regeneration_body_and_native(self):
        original=LEGACY.read_bytes()
        generated=emit_context_methods(LEGACY,'DisjointSet',NAMESPACE,
            [str(ROOT/'experiments/library3/cpp')],method_names=['getNum'])
        self.assertEqual(generated,(ROOT/'Proofs/Generated/DisjointSetMethods.lean').read_text())
        self.assertIn('def availableMethods : List String := ["unite", "same", "root", "size", "getNum"]',generated)
        self.assertIn('def fieldPermutation : List Nat := [1, 0, 2]',generated)
        checks=(ROOT/'tests/lean/disjoint_set_getter.lean').read_text()
        self.check_lean('import Proofs.DisjointSetGetter\n'+checks)
        check_compiler()
        with tempfile.TemporaryDirectory(prefix='legacy-getnum-native-') as directory:
            binary=Path(directory)/'native'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',
                '-I'+str(ROOT),'-I'+str(ROOT/'experiments/library3/cpp'),
                str(ROOT/'tests/imports/disjoint_set_getter.cpp'),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)
        self.assertEqual(LEGACY.read_bytes(),original)

    def test_dependency_inlining_field_order_and_global_alias_audit(self):
        with tempfile.TemporaryDirectory(prefix='method-selection-probe-') as directory:
            source=Path(directory)/'source.hpp';source.write_text(PROBE)
            generated=emit_context_methods(source,'Probe','SelectedProbe',method_names=['outer','view'])
            self.check_lean(generated+PROBE_CHECKS)
            # Unselected mutable-reference parameters must still prevent value capture.
            ir=lower_context_methods(source,'Probe',method_names=['view'])
            self.assertTrue(all(f['reference'] for f in ir['methods'][0]['fields'][1:]))
            self.assertTrue(all(not f['writable'] for f in ir['methods'][0]['fields']))
            self.assertEqual(ir['dependency_methods'],[])
            # The existing copy emitter/profile requires vector-first layout.
            with self.assertRaises(ValueError):audit_class_copy(source,'Probe')
            check_compiler()
            cpp=Path(directory)/'native.cpp';binary=Path(directory)/'native'
            cpp.write_text(PROBE+'#include <cassert>\nint main(){Probe p{17,{7},4};assert(p.view()==4);assert(p.outer(p.count)==9);assert(p.stamp==17 && p.count==9 && p.data[0]==7);}\n')
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all',str(cpp),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

    def test_full_methods_with_vector_last(self):
        with tempfile.TemporaryDirectory(prefix='method-vector-last-') as directory:
            source=Path(directory)/'source.hpp'
            source.write_text('#include <vector>\nstruct Tail {int stamp;int count;std::vector<int> data;int get(){return count;}};\n')
            generated=emit_context_methods(source,'Tail','FullTail')
            checks=PROBE_CHECKS[:PROBE_CHECKS.index('example : SelectedProbe.coverage')]+r"""
example : FullTail.coverage = "context_method_receivers" := rfl
example : FullTail.declaredFieldNames = ["stamp","count","data"] := rfl
example : FullTail.fieldNames = ["data","stamp","count"] := rfl
example : FullTail.fieldPermutation = [2,0,1] := rfl
#guard (match FullTail.«Tail_get_callFuel» 16 initial ⟨0,[1,2]⟩ [] with
  | .finished (out,result) => result == .scalar 4 && out.scalars.memory.map (·.value) == [17,4]
  | _ => false)
end SelectionChecks
"""
            self.check_lean(generated+checks)

    def test_selection_validation_and_reachable_unsupported_method(self):
        for names in [[],['getNum','getNum'],'getNum',[None]]:
            with self.subTest(names=names),self.assertRaisesRegex(ValueError,'method_names'):
                lower_context_methods(LEGACY,'DisjointSet',method_names=names)
        with tempfile.TemporaryDirectory(prefix='method-selection-reject-') as directory:
            source=Path(directory)/'source.hpp';source.write_text(PROBE)
            with self.assertRaisesRegex(ValueError,'selected methods'):
                lower_context_methods(source,'Probe',method_names=['missing'])
            with self.assertRaises(ValueError):
                lower_context_methods(source,'Probe',method_names=['recursive'])
            with self.assertRaisesRegex(ValueError,'default argument'):
                lower_context_methods(source,'Probe',method_names=['unused'])

if __name__=='__main__':
    disable_network()
    unittest.main()
