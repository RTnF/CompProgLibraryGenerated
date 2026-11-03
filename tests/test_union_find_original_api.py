"""Full legacy UnionFind API candidate: recursive/state oracle and generated calls."""
from pathlib import Path
import itertools
import os
import resource
import signal
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from nested_ir import lower_source, emit_lean
from check_public import FLAGS, check_compiler
from offline import disable_network
ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT/'experiments/verification/data_structure/union_find.hpp'
HEADER = '''
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall
open Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore Proofs.CppVectorOwnership Proofs.CppLoop
 def intTy : Ty := ⟨32,true,false⟩
 def caller (ps : List Int) (groups : Int) : NState :=
   let buffer : Proofs.CppVector.Buffer Value := ⟨0,ps.map Value.integer,ps.length+1,64,0⟩
   let heap : Proofs.CppNestedVectorStore.State :=
     ⟨⟨[some ⟨.integer intTy,none,some 0,[]⟩]⟩,⟨[some buffer],0,0,0⟩⟩
   {scalars := ⟨[⟨intTy,groups⟩,⟨intTy,9876⟩],[⟨0,true⟩,⟨0,false⟩,⟨1,true⟩],0,0,0⟩,
    frame := ⟨heap,[true],[⟨0,.integer intTy,true,.root 0⟩]⟩,
    slots := [.vector 0,.scalar 0,.scalar 1,.scalar 2]}
 def observe (outcome : Outcome (NState × Ret)) : Option (Int × Int × List Int) := do
   let (s,r) ← match outcome with | .finished pair => some pair | _ => none
   let x ← match r with | .scalar x => some x | _ => none
   let count ← s.scalars.memory[0]?
   let buffer ← s.frame.state.storage.lookup 0
   let values ← buffer.items.mapM fun v => match v with | .integer y => some y | _ => none
   if s.scalars.bindings == [⟨0,true⟩,⟨0,false⟩,⟨1,true⟩] &&
      s.scalars.memory == [⟨intTy,count.value⟩,⟨intTy,9876⟩] &&
      s.slots == [.vector 0,.scalar 0,.scalar 1,.scalar 2] && s.scope == 0 &&
      s.frame.bindings == [⟨0,.integer intTy,true,.root 0⟩] then some (x,count.value,values) else none
'''


def forests():
    yield [], 0, []
    for n in range(1,4):
        for parents in itertools.product(range(-1,n),repeat=n):
            roots=[]
            for a in range(n):
                seen=set()
                while parents[a] >= 0 and a not in seen:
                    seen.add(a); a=parents[a]
                if a in seen: break
                roots.append(a)
            if len(roots)!=n: continue
            ps=[-roots.count(i) if parents[i]<0 else parents[i] for i in range(n)]
            yield ps,len(set(roots)),list(range(n))
    balanced=[-8,0,0,2,0,4,4,6]
    yield balanced,1,list(range(8))
    yield balanced+[x if x<0 else x+8 for x in balanced],2,[0,2,3,7,11,15]
    yield [-32]+list(range(31)),1,[0,1,3,7,15,31]


def reference(ps,groups,method,a,b):
    ps=list(ps)
    def root(v):
        if ps[v]<0: return v
        ps[v]=root(ps[v]); return ps[v]
    if method=='root': result=root(a)
    elif method=='size': result=-ps[root(a)]
    elif method=='same': result=int(root(a)==root(b))
    elif method=='num_groups': result=groups
    else:
        x,y=root(a),root(b)
        if x!=y:
            if -ps[x] < -ps[y]: x,y=y,x
            ps[x]+=ps[y]; ps[y]=x; groups-=1
        result=x
    return result,groups,ps


def lean_list(values):return '['+','.join(f'({x})' for x in values)+']'


class UnionFindOriginalApiTests(unittest.TestCase):
    def test_candidate_keeps_all_original_operations_and_state(self):
        checks=["import Proofs.UfCompression\n"+emit_lean(lower_source(SOURCE,[SOURCE.parent]),'UnionFindOriginalApi'),HEADER]
        native=[];expected=[];index=0
        for ps,groups,indices in forests():
            n=len(ps)
            calls=[('num_groups',0,0)]
            calls += [(method,a,0) for method in ['root','size'] for a in indices]
            calls += [(method,a,b) for method in ['same','unite'] for a in indices for b in indices]
            for method,a,b in calls:
                result,count,vec=reference(ps,groups,method,a,b)
                native.append(' '.join(map(str,[method,n,groups,a,b,*ps])))
                expected.append(' '.join(map(str,[result,count,n,*vec])))
                args=['.vectorReference 0','.scalarReference 1',f'.value (.literal intTy {n})']
                if method!='num_groups':args.append(f'.value (.literal intTy {a})')
                if method in ('same','unite'):args.append(f'.value (.literal intTy {b})')
                checks += [f'def call{index} := UnionFindOriginalApi.UnionFind_{method}.callFuel 256 (caller {lean_list(ps)} {groups}) [{",".join(args)}]',
                           f'#guard observe call{index} == some ({result},{count},{lean_list(vec)})']
                index+=1
        invalid_cases=[]
        for method in ['root','size','same','unite']:
            for n in [0,3]:
                for bad in [-2147483648,-1,n,2147483647]:
                    invalid_cases.append((method,n,bad,0))
                    args=['.vectorReference 0','.scalarReference 1',f'.value (.literal intTy {n})',f'.value (.literal intTy ({bad}))']
                    if method in ('same','unite'):args.append('.value (.literal intTy 0)')
                    checks.append(f'#guard UnionFindOriginalApi.UnionFind_{method}.callFuel 256 (caller (List.replicate {n} (-1)) {n}) [{",".join(args)}] == .fault')
        for method in ['same','unite']:
            for bad in [-2147483648,-1,3,2147483647]:
                invalid_cases.append((method,3,0,bad))
                checks.append(f'#guard UnionFindOriginalApi.UnionFind_{method}.callFuel 256 (caller [-1,-1,-1] 3) [.vectorReference 0,.scalarReference 1,.value (.literal intTy 3),.value (.literal intTy 0),.value (.literal intTy ({bad}))] == .fault')
        checks += ['#guard Proofs.UfCompression.recursive 4 [-8,0,0,2,0,4,4,6] 7 == some ([-8,0,0,2,0,4,0,0],0)',
                   '#guard Proofs.UfCompression.recursive 1 [-8,0,0,2,0,4,4,6] 7 == none']
        with tempfile.TemporaryDirectory(prefix='union-find-original-api-') as directory:
            scratch=Path(directory);lean=scratch/'checks.lean';lean.write_text('\n'.join(checks))
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            check_compiler()
            exe=scratch/'native'
            subprocess.run(['g++',*FLAGS,'-fno-access-control','-fsanitize=address,undefined','-fno-sanitize-recover=all',
                '-fno-omit-frame-pointer','-fno-pie','-no-pie','-I',str(ROOT/'experiments/library/cpp'),
                str(ROOT/'tests/imports/union_find_original_api.cpp'),'-o',str(exe)],cwd=ROOT,check=True)
            native_env=os.environ.copy();native_env['ASAN_OPTIONS']='detect_leaks=0:halt_on_error=1'
            native_env['UBSAN_OPTIONS']='halt_on_error=1:print_stacktrace=1'
            result=subprocess.run([str(exe)],input='\n'.join(native)+'\n',capture_output=True,text=True,env=native_env)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            self.assertEqual(result.stdout.splitlines(),expected)
            # Both originals and the candidate reject the same invalid endpoints.
            for method,n,a,b in invalid_cases:
                for kind in ['old','candidate']:
                    result=subprocess.run([str(exe),kind,method,str(n),str(a),str(b)],env=native_env,capture_output=True,text=True,
                        preexec_fn=lambda:resource.setrlimit(resource.RLIMIT_CORE,(0,0)))
                    self.assertEqual(result.returncode,-signal.SIGABRT,result.stdout+result.stderr)
                    self.assertIn('Assertion',result.stderr)
                    self.assertNotIn('ERROR: AddressSanitizer',result.stderr)
                    self.assertNotIn('runtime error:',result.stderr)
        print(f'UnionFind original API: {index} full-state generated/recursive/native cases, 32000 stateful native operations, assertion failures')


if __name__=='__main__':disable_network();unittest.main()
