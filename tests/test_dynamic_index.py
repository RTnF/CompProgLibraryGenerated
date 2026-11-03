"""Read-dependent indices preserve temporary references and expression bounds."""
from pathlib import Path
import os
import subprocess
import tempfile
import unittest

from test_dynamic_expr import fixture_checks
from test_scalar_ir import lean_environment
from nested_ir import lower_source, emit_lean
from check_public import FLAGS, check_compiler
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent


def index_checks():
    checks = fixture_checks()
    checks[0] = 'import Proofs.DynamicIndexAtoms\n'+checks[0]
    checks += ['open Proofs.DynamicExprCertified Proofs.DynamicExprDerive',
               'theorem rootReady : Ready params (snapshot state) logical rootSize := known (by decide +kernel) (Proofs.DynamicExprAtoms.root_size params _ _ 1 p1 (by decide +kernel) (by decide +kernel) i32 0 values (by decide +kernel) (by decide +kernel))',
               'theorem readReady : Ready params (snapshot state) logical rowRead := known (by decide +kernel) (Proofs.DynamicExprAtoms.row_read params _ _ 1 p1 (by decide +kernel) (by decide +kernel) i32 0 1 1 values [17,-3] idx pos (-3) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel))',
               'theorem combinedReady : Ready params (snapshot state) logical combined := Ready.binary _ _ _ _ (Ready.cast _ _ rootReady) readReady',
               'def nestedRead : NExpr := .read i32 (.row (.local 1) atom combined) combined',
               'theorem nestedAtomic : Atomic params (snapshot state) logical nestedRead (-3) :=',
               '  Proofs.DynamicIndexAtoms.row_read params _ _ 1 p1 (by decide +kernel) (by decide +kernel) i32 0 1 1 values [17,-3] combined combined (-3) (by decide +kernel) combinedReady (by decide +kernel) (by decide +kernel) combinedReady (by decide +kernel) (by decide +kernel)',
               'theorem nestedReady : Ready params (snapshot state) logical nestedRead := known (by decide +kernel) nestedAtomic',
               'def mutableRead : NExpr := .read i32 (.row (.local 0) atom combined) combined',
               'theorem mutableAtomic : Atomic params (snapshot state) logical mutableRead (-3) :=',
               '  Proofs.DynamicIndexAtoms.row_read params _ _ 0 p0 (by decide +kernel) (by decide +kernel) i32 0 1 1 values [17,-3] combined combined (-3) (by decide +kernel) combinedReady (by decide +kernel) (by decide +kernel) combinedReady (by decide +kernel) (by decide +kernel)',
               '#guard ((mutableRead.eval state).getD (state,0)).1.frame.bindings[state.frame.bindings.length+1]?.map (·.writable) == some true',
               'def zeroIdx : NExpr := .binary i32 .add rowRead (.literal i32 3)',
               'theorem zeroReady : Ready params (snapshot state) logical zeroIdx := Ready.binary _ _ _ _ readReady (Ready.scalar _ rfl)',
               'def flatRead : NExpr := .read i32 (.local 2) zeroIdx',
               'theorem flatAtomic : Atomic params (snapshot state) logical flatRead 77 :=',
               '  Proofs.DynamicIndexAtoms.flat_read params _ _ 2 p2 (by decide +kernel) (by decide +kernel) i32 1 0 [77] zeroIdx 77 (by decide +kernel) zeroReady (by decide +kernel) (by decide +kernel)',
               'theorem flatReady : Ready params (snapshot state) logical flatRead := known (by decide +kernel) flatAtomic',
               'def nestedSize : NExpr := .size atom (.row (.local 1) atom combined)',
               'theorem sizeAtomic : Atomic params (snapshot state) logical nestedSize 2 :=',
               '  Proofs.DynamicIndexAtoms.row_size params _ _ 1 p1 (by decide +kernel) (by decide +kernel) i32 0 1 values [17,-3] combined (by decide +kernel) combinedReady (by decide +kernel) (by decide +kernel) (by decide +kernel)',
               'theorem sizeReady : Ready params (snapshot state) logical nestedSize := known (by decide +kernel) sizeAtomic',
               'def full : NExpr := .binary i32 .add (.binary i32 .add nestedRead flatRead) (.cast i32 nestedSize)',
               'theorem fullReady : Ready params (snapshot state) logical full := Ready.binary _ _ _ _ (Ready.binary _ _ _ _ nestedReady flatReady) (Ready.cast _ _ sizeReady)',
               'theorem fullCert : Evaluation params (snapshot state) logical full 76 := derive fullReady 76 (by decide +kernel)',
               'def deepIdx : NExpr := .binary i32 .add nestedRead (.literal i32 3)',
               'def deep : NExpr := .read i32 (.local 2) deepIdx',
               'theorem deepAtomic : Atomic params (snapshot state) logical deep 77 :=',
               '  Proofs.DynamicIndexAtoms.flat_read params _ _ 2 p2 (by decide +kernel) (by decide +kernel) i32 1 0 [77] deepIdx 77 (by decide +kernel) (Ready.binary _ _ _ _ nestedReady (Ready.scalar _ rfl)) (by decide +kernel) (by decide +kernel)',
               'theorem deepCert : Evaluation params (snapshot state) logical deep 77 := .atom _ _ deepAtomic',
               'example (s : NState) (r : Realizes params (snapshot state) logical s) : Proofs.DynamicExpr.denote params (snapshot state) logical full = some 76 ∧ ∃ t, full.eval s = some (t,76) ∧ Realizes params (snapshot state) logical ((t.release s).charge 1 0) ∧ ((t.release s).charge 1 0).work ≤ s.work+2*full.nodes+1 ∧ ((t.release s).charge 1 0).peak ≤ max s.peak (max s.scalars.peak (Proofs.CppNestedEval.liveS s+2*full.nodes)+s.frame.state.storage.peak) := released fullCert s r',
               'example := released deepCert state realizes',
               '#guard !combined.scalarOnly',
               'def nestedResult := (nestedRead.eval state).getD (state,0)',
               '#guard nestedResult.2 == -3',
               '#guard nestedResult.1.frame.bindings.length == state.frame.bindings.length+3',
               '#guard nestedResult.1.frame.bindings[state.frame.bindings.length+1]?.map (·.owner) == some 4',
               '#guard (nestedResult.1.frame.bindings.drop state.frame.bindings.length).all (fun b => !b.writable)',
               '#guard (nestedResult.1.release state).frame.bindings == state.frame.bindings',
               '#guard (full.eval state).map Prod.snd == some 76',
               '#guard (deep.eval state).map Prod.snd == some 77',
               'def invalidIndices : List NExpr := [.read i32 (.row (.local 1) atom rowRead) combined,.size atom (.row (.local 1) atom (.cast i32 rootSize)),.read i32 (.local 2) (.cast i32 nestedSize),.read ⟨64,false,false⟩ (.local 2) zeroIdx]',
               '#guard invalidIndices.all (fun e => (Proofs.DynamicExpr.denote params (snapshot state) logical e).isNone && (e.eval state).isNone)',
               'def wrong : NExpr := .read i32 (.row (.local 1) atom rowRead) combined',
               'example (v : Int) : ¬ Evaluation params (snapshot state) logical wrong v := by',
               '  intro cert; have pure := (sound cert state realizes).1',
               '  have failed : Proofs.DynamicExpr.denote params (snapshot state) logical wrong = none := by decide +kernel',
               '  rw [failed] at pure; contradiction',
               'def short : NExpr := .logical false (.literal i32 1) wrong',
               'theorem shortCert : Evaluation params (snapshot state) logical short 1 := Evaluation.logicalShort false _ _ 1 (Evaluation.scalar _ 1 rfl (by decide +kernel)) (by decide +kernel)',
               'example := released shortCert state realizes']
    return checks


class DynamicIndexTests(unittest.TestCase):
    def test_general_indices_and_native_source(self):
        checks = index_checks()
        source_text = '''#include <vector>
namespace cp {
int inspect(const std::vector<std::vector<int>>& g,const std::vector<int>& other,int k,int j){return g[(int)g.size()+g[k][j]][(int)g.size()+g[k][j]]+other[g[k][j]+3]+(int)g[(int)g.size()+g[k][j]].size();}
int deep(const std::vector<std::vector<int>>& g,const std::vector<int>& other,int k,int j){return other[g[(int)g.size()+g[k][j]][(int)g.size()+g[k][j]]+3];}
}
'''
        with tempfile.TemporaryDirectory(prefix='dynamic-index-') as directory:
            scratch=Path(directory); fixture=scratch/'source.hpp'; fixture.write_text(source_text)
            generated=emit_lean(lower_source(fixture),'IndexSource')
            checks[0]='import Proofs.DynamicIndexAtoms\nimport Proofs.DynamicReadSound\n'+generated+checks[0].replace('import Proofs.DynamicIndexAtoms\n','').replace('import Proofs.DynamicReadSound\n','')
            for name,value in [('inspect',76),('deep',77)]:
                checks += [f'def call_{name} := IndexSource.{name}.callFuel 500 state [.vectorReference 1,.vectorReference 2,.value (.literal i32 1),.value (.literal i32 1)]',
                           f'#guard (match call_{name} with | .finished (s,.scalar x) => x == {value} && s.frame.bindings == base.bindings && s.frame.state.wellFormed && s.scalars.memory == state.scalars.memory && (s.frame.state.storage.lookup 4).map (·.items) == some [.integer 17,.integer (-3)] | _ => false)']
            proof=scratch/'checks.lean'; proof.write_text('\n'.join(checks)); lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler(); source=scratch/'native.cpp'; exe=scratch/'native'
            source.write_text('#include "experiments/library/cpp/template/small_template.hpp"\n#include "source.hpp"\n#include <iostream>\nint main(){std::vector<std::vector<int>> g{{10,0},{17,-3},{},{}};std::vector<int> other{77};std::cout<<cp::inspect(g,other,1,1)<<std::endl;std::cout<<cp::deep(g,other,1,1)<<std::endl;}')
            subprocess.run(['g++',*FLAGS,'-fsanitize=address,undefined','-fno-omit-frame-pointer','-I',str(ROOT),str(source),'-o',str(exe)],cwd=ROOT,check=True)
            env=os.environ.copy(); env['ASAN_OPTIONS']='detect_leaks=0'
            result=subprocess.run([str(exe)],cwd=ROOT,env=env,check=True,capture_output=True,text=True)
            self.assertEqual(result.stdout.splitlines(),['76','77'])


if __name__ == '__main__':
    disable_network(); unittest.main()
