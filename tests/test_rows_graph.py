"""Row evaluation after growth uses actual owner IDs and the current epoch."""
from pathlib import Path
import subprocess
import tempfile
import unittest

from test_append_row import initial
from test_scalar_ir import lean_environment
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent


class RowsGraphTests(unittest.TestCase):
    def test_noncontiguous_owners_epochs_and_permissions(self):
        checks = ['import Proofs.CppRowsStmt', 'import Proofs.CppRowsContents',
                  'open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppNestedVectorStore',
                  'open Proofs.CppNestedVectorBindings Proofs.CppNestedProgram Proofs.CppRowsGraph',
                  'def i32 : Ty := ⟨32,true,false⟩',
                  'def atom : Element := .integer i32', 'def row : Element := .vector atom']
        for case, (n, capacity) in enumerate([(0, 0), (1, 1), (3, 6)]):
            name = f'f{case}'
            checks.append(f'def {name}_0 := {initial(n, capacity)}')
            ids = list(range(1, n+1))
            epoch = 0
            for step in range(3):
                size = n+step
                if size == capacity:
                    capacity = max(1, 2*size)
                    epoch += 1
                ids.append(n+3+step)
                checks.append(f'def {name}_{step+1} := ({name}_{step}.appendRow 0 i32).getD {name}_{step}')
            checks.append(f'def {name} := {name}_3')
            literal = '['+','.join(map(str, ids))+']'
            checks += [f'def ids{case} : List Nat := {literal}',
                       f'def parent{case} := ({name}.state.storage.lookup 0).getD ⟨0,[],0,64,0⟩',
                       f'theorem rows{case} : Rows {name}.state 0 i32 0 ids{case} {epoch} :=',
                       f'  ⟨by decide +kernel,by decide +kernel,parent{case},by decide +kernel,by decide +kernel,by decide +kernel⟩',
                       f'#guard {name}.resolve 2 atom |>.isSome',
                       f'#guard {name}.child 0 atom {len(ids)} == none',
                       f'#guard {name}.child 0 atom (-1) == none']
            values = '['+','.join(f'[{10+i},({-i})]' for i in range(n))+(',' if n else '')+'[],[],[]]'
            checks += [f'def values{case} : List (List Int) := {values}',
                       f'theorem data{case} : Proofs.CppRowsContents.Data {name}.state 0 i32 0 ids{case} {epoch} values{case} := by',
                       f'  refine ⟨rows{case},by decide +kernel,?_⟩',
                       '  intro k owner lookup',
                       f'  refine ⟨({name}.state.storage.lookup owner).getD ⟨0,[],0,64,0⟩,?_,?_⟩',
                       f'  all_goals have bound : k < {len(ids)} := (List.getElem?_eq_some_iff.mp lookup).1',
                       f'  all_goals have positions : {" ∨ ".join(f"k = {j}" for j in range(len(ids)))} := by omega',
                       f'  all_goals rcases positions with {" | ".join("h" for _ in ids)} <;> subst k <;> simp [ids{case}] at lookup <;> subst owner',
                       '  all_goals decide +kernel',
                       f'example : ∃ r, {name}.state.appendRow 0 i32 = some (Proofs.CppAppendRow.added {name}.state 0 (tag i32 0 ids{case}) i32 parent{case} r) ∧ Proofs.CppRowsContents.Data (Proofs.CppAppendRow.added {name}.state 0 (tag i32 0 ids{case}) i32 parent{case} r) 0 i32 0 (ids{case} ++ [{name}.state.storage.objects.length]) r.buffer.epoch (values{case} ++ [[]]) :=',
                       f'  Proofs.CppRowsContents.appendRow_data {name}.state 0 i32 0 ids{case} {epoch} values{case} data{case} parent{case} (by decide +kernel) (by decide +kernel)',
                       f'def old{case} := ({name}.state.storage.lookup {ids[-1]}).getD ⟨0,[],0,64,0⟩',
                       f'def result{case} := (Proofs.CppVectorGrowth.append old{case} (accepts atom) true (.integer 9)).getD ⟨old{case},(),0,0⟩',
                       f'#guard (Proofs.CppVectorGrowth.append old{case} (accepts atom) true (.integer 9)).isSome',
                       f'example : Proofs.CppRowsContents.Data ({name}.updated {ids[-1]} old{case} result{case}).state 0 i32 0 ids{case} {epoch} (values{case}.set {len(ids)-1} [9]) :=',
                       f'  Proofs.CppRowsContents.updated_data {name} 0 i32 0 ids{case} {epoch} values{case} data{case} {len(ids)-1} {ids[-1]} (by decide +kernel) old{case} result{case} [9] (by decide +kernel) (by decide +kernel)']
            for k in [0, len(ids)-1]:
                owner = ids[k]
                checks += [
                    f'example : {name}.child 0 atom {k} = some ({name}.addBinding (binding 0 i32 {epoch} {k} {owner} true)) :=',
                    f'  child_row {name} 0 0 i32 0 ids{case} {epoch} {k} {owner} rows{case} (by decide +kernel) true true (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun h => h)',
                    f'example : {name}.child 1 atom {k} = some ({name}.addBinding (binding 0 i32 {epoch} {k} {owner} false)) :=',
                    f'  child_row {name} 1 0 i32 0 ids{case} {epoch} {k} {owner} rows{case} (by decide +kernel) false true (by decide +kernel) (by decide +kernel) (by decide +kernel) (by simp)',
                    f'def bound{case}_{k} := ({name}.addBinding (binding 0 i32 {epoch} {k} {owner} true)).1',
                    f'example : ∃ b, bound{case}_{k}.resolve 3 atom = some (binding 0 i32 {epoch} {k} {owner} true,b) ∧ bound{case}_{k}.state.storage.lookup {owner} = some b :=',
                    f'  resolve_row bound{case}_{k} 3 0 i32 0 ids{case} {epoch} {k} {owner} rows{case} (by decide +kernel) true true (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun h => h)',
                    f'#guard (bound{case}_{k}.resolve 3 atom).isSome',
                    f'#guard (({name}.addBinding (binding 0 i32 {epoch+1} {k} {owner} true)).1.resolve 3 atom) == none',
                    f'#guard (({name}.addBinding (binding 0 i32 {epoch} {k} {n+1} true)).1.resolve 3 atom) == none',
                    f'#guard (({name}.addBinding (binding 0 i32 {epoch} {k} {owner} false)).1.appendGrowing 3 i32 9) == none',
                ]
            checks += [f'def ns{case} : NState := {{scalars := ⟨[],[],0,0,0⟩,frame := {name},slots := [.vector 0],scope := 0,peak := 0}}',
                       f'example : ∃ t, (Container.row (.local 0) atom (.literal i32 {len(ids)-1})).eval ns{case} = some (t,{name}.bindings.length) ∧ Proofs.CppNestedStmt.GoodF ns{case} t 3 3 ∧ t.frame.bindings = {name}.bindings ++ [binding 0 i32 {epoch} {len(ids)-1} {ids[-1]} true] :=',
                       f'  Proofs.CppRowsStmt.eval_row ns{case} 0 0 (.literal i32 {len(ids)-1}) {len(ids)-1} 0 0 {epoch} {ids[-1]} ids{case} i32 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) rows{case} (by decide +kernel) (by decide +kernel) (by decide +kernel)']
        with tempfile.TemporaryDirectory(prefix='rows-graph-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text('\n'.join(checks))
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)


if __name__ == '__main__':
    disable_network()
    unittest.main()
