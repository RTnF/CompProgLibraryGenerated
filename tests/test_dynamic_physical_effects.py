"""Row allocation preserves flags and absent scopes, including deep roots."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest

from test_dynamic_expr import fixture_checks, HEADER
from test_scalar_ir import lean_environment
from nested_ir import lower_source, emit_lean
from check_public import FLAGS, check_compiler
from offline import disable_network

ROOT=Path(__file__).resolve().parent.parent
SOURCE='''#include <vector>
namespace cp {int grow(std::vector<std::vector<int>>&g){g.emplace_back();g.emplace_back();return g.size();}}
'''

class DynamicPhysicalEffectsTests(unittest.TestCase):
    def test_authority_and_scope_absence(self):
        checks=fixture_checks()
        checks += ['open Proofs.DynamicForestEffects Proofs.DynamicPhysicalEffects',
          'example (f : Forest) (parent : Nat) (tag : Tag) (element : Element) (valid : f.wellFormed = true) (found : f.lookup parent = some tag) (scope : Nat) (absent : NoScope f scope) : NoScope (f.appendChild parent tag element) scope := append_preserves f parent tag element valid found scope absent',
          'example (s : NState) (slot : Nat) (ty : Ty) (out : NStep) (ran : (NStmt.appendRow (.local slot) ty).run s = some out) : Change s out.state := appendRoot_stmt s slot ty out ran',
          'def deepForest : Forest := ⟨state.frame.state.forest.objects.set 2 (some ⟨atom,none,some 99,[]⟩)⟩',
          'def deep : NState := {state with frame := {state.frame with state := {state.frame.state with forest := deepForest}}}',
          '#guard deep.frame.state.wellFormed',
          '#guard deep.frame.state.forest.context 2 == some 99',
          'theorem absent : NoScope deep.frame.state.forest 3 := NoScope.of_tags _ _ (by decide +kernel)',
          '#guard !(deep.frame.state.forest.objects.all (fun entry => entry.all (fun tag => tag.scope.all (fun sc => decide (sc ≤ 2)))))',
          'def stmt : NStmt := .appendRow (.local 0) i32',
          'def first : NStep := (stmt.run deep).getD ⟨deep,none,false⟩',
          'theorem firstRun : stmt.run deep = some first := by decide +kernel',
          'theorem firstEffect : Change deep first.state := appendRoot_stmt deep 0 i32 first firstRun',
          'def second : NStep := (stmt.run first.state).getD first',
          'theorem secondRun : stmt.run first.state = some second := by decide +kernel',
          'theorem secondEffect : Change first.state second.state := appendRoot_stmt first.state 0 i32 second secondRun',
          'theorem composedEffect : Change deep second.state := firstEffect.trans secondEffect',
          'example : NoScope second.state.frame.state.forest 3 := composedEffect.1.absent 3 absent',
          'example : second.state.frame.rootWritable[0]? = some true := composedEffect.1.flag 0 true (by decide +kernel)',
          'example : second.state.frame.rootWritable[2]? = some true := composedEffect.1.flag 2 true (by decide +kernel)',
          '#guard second.state.frame.rootWritable == deep.frame.rootWritable ++ [false,false]',
          '#guard second.state.scope == deep.scope',
          '#guard second.state.frame.state.forest.context 7 == some 0',
          '#guard second.state.frame.state.forest.context 8 == some 0',
          '#guard second.state.frame.state.forest.context 3 == none',
          '#guard second.state.frame.state.forest.context 200 == none',
          '#guard second.state.frame.state.forest.context 2 == some 99',
          '#guard second.state.frame.state.storage.lookup 2 == deep.frame.state.storage.lookup 2',
          'example : ¬ NoScope second.state.frame.state.forest 0 := by intro bad; exact bad 7 (by decide +kernel)',
          'example : ¬ NoScope second.state.frame.state.forest 99 := by intro bad; exact bad 2 (by decide +kernel)',
          'example := charge second.state 7 11',
          'example := release second.state deep',
          'example := declared second.state i32 true 7',
          'example (s : NState) (sc : Proofs.CppState.State) : Change s {s with scalars := sc} := scalars s sc',
          'example (f : Frame) (owner : Nat) (old : Proofs.CppVector.Buffer Value) (r : Proofs.CppVector.Result Value Unit) : Authority f (f.updated owner old r) := updated f owner old r',
          'example := restored composedEffect.1',
          'def readonly : NState := {deep with frame := {deep.frame with bindings := deep.frame.bindings.set 0 ⟨0,row,false,.root 0⟩}}',
          '#guard (stmt.run readonly).isNone',
          '#guard (readonly.frame.appendRow 0 i32).isNone',
          'example : ¬ Authority deep.frame {deep.frame with rootWritable := deep.frame.rootWritable.set 0 false} := by',
          '  intro effect; have flag := effect.flag 0 true (by decide +kernel)',
          '  have bad : ({deep.frame with rootWritable := deep.frame.rootWritable.set 0 false} : Frame).rootWritable[0]? = some false := by decide +kernel',
          '  have impossible : (true : Bool) = false := Option.some.inj (flag.symm.trans bad); contradiction']
        with tempfile.TemporaryDirectory(prefix='dynamic-physical-') as directory:
            scratch=Path(directory);source=scratch/'source.hpp';source.write_text(SOURCE)
            generated=emit_lean(lower_source(source),'PhysicalSource')
            checks[0]='import Proofs.DynamicCallEffects\nimport Proofs.DynamicReadSound\n'+generated+HEADER.replace('import Proofs.DynamicReadSound\n','')
            checks += ['def call := PhysicalSource.grow.callFuel 300 deep [.vectorReference 0]',
              '#guard (match call with | .finished (s,.scalar x) => x == 6 && s.scope == deep.scope && s.frame.bindings == deep.frame.bindings && s.frame.rootWritable == deep.frame.rootWritable ++ [false,false] && s.frame.state.forest.context 2 == some 99 && s.frame.state.wellFormed | _ => false)']
            proof=scratch/'checks.lean';proof.write_text('\n'.join(checks));lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler();source=scratch/'native.cpp';exe=scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>> g{{10,0},{17,-3},{},{}};int r=cp::grow(g);std::cout<<r<<" "<<g.size()<<" "<<g[4].size()<<" "<<g[5].size()<<std::endl;}')
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env=os.environ.copy();env['ASAN_OPTIONS']='detect_leaks=0'
            result=subprocess.run([str(exe)],cwd=ROOT,env=env,capture_output=True,text=True,check=True)
            self.assertEqual(result.stdout.splitlines(),['6 6 0 0'])

if __name__=='__main__':
    disable_network();unittest.main()
