"""One-environment AST selection and connection of the original signed source."""

import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'verifier'))
sys.path.insert(0,str(ROOT/'tools'))
from ast_stream import root_objects,direct_functions
from scalar_ir import source_ast
from state_ir import lower_source,emit_lean
from test_scalar_ir import lean_environment
from offline import disable_network


class DirectASTTests(unittest.TestCase):
    def test_stream_chunk_boundaries_strings_and_trailer(self):
        nodes=[{'kind':'FunctionDecl','name':'one','loc':{'offset':1},
                'inner':[{'value':'quotes " \\ } { and \\" remain strings','inner':[]}]},
               {'kind':'NamespaceDecl','inner':[]},
               {'kind':'FunctionDecl','name':'two','loc':{'offset':9}}]
        raw=json.dumps({'kind':'TranslationUnitDecl','loc':{},'inner':nodes},indent=2).encode()
        for chunk in (1,2,3,7,31,1024):
            with self.subTest(chunk=chunk):
                self.assertEqual([json.loads(n) for n in root_objects(io.BytesIO(raw),chunk)],nodes)
        for raw in (b'{"kind":"Other","inner":[]}',b'{"kind":"TranslationUnitDecl","inner":[{}',
                    b'{"kind":"TranslationUnitDecl","inner":[]} {"inner":[]}'):
            with self.subTest(raw=raw),self.assertRaises(ValueError):list(root_objects(io.BytesIO(raw),3))
        self.assertEqual(list(root_objects(io.BytesIO(b'{"kind":"TranslationUnitDecl","inner":[]}'),1)),[])

    def test_same_ast_definitions_in_direct_file_and_includes(self):
        with tempfile.TemporaryDirectory() as directory:
            scratch=Path(directory);header=scratch/'dependency.hpp'
            header.write_text('inline long external_helper(long x){return x+1;}')
            source=scratch/'source.cpp'
            source.write_text('#include "dependency.hpp"\nnamespace cp {long helper(long x){return x+1;}long use(long x){return helper(x);}}')
            filtered=lower_source(source)
            direct=lower_source(source,None)
            self.assertEqual(filtered,direct)
            nodes=source_ast(source,None)
            self.assertEqual([n['name'] for n in nodes],['helper','use'])
            call=next(c for c in nodes[1]['inner'] if c['kind']=='CompoundStmt')['inner'][0]['inner'][0]
            self.assertEqual(call['inner'][0]['inner'][0]['referencedDecl']['id'],nodes[0]['id'])
            source.write_text('#include "dependency.hpp"\nlong use(long x){return external_helper(x);}')
            with self.assertRaisesRegex(ValueError,'definition in the selected AST'):lower_source(source,None)

    def test_original_signed_complete_model_and_checked_narrowing(self):
        source=ROOT/'experiments/library/cpp/number_theory/floor_sum.hpp'
        includes=[ROOT/'experiments/library/cpp']
        ir=lower_source(source,None,includes)
        self.assertEqual([f['name'] for f in ir['functions']],['safe_mod','floor_sum_unsigned','floor_sum'])
        for name in ('safe_mod','floor_sum_unsigned'):
            separate=lower_source(source,name,includes)
            self.assertEqual(next(f for f in ir['functions'] if f['name']==name),separate['functions'][0])
        generated=emit_lean(ir,'SignedSource')
        self.assertIn('(.invoke',generated)
        self.assertEqual(generated,(ROOT/'experiments/verification/number/floor_sum_signed_model.lean').read_text())
        guards=''
        native=[]
        for n in (0,1,2,5,9):
            for m in (1,2,5):
                for a,b in ((0,0),(1,2),(9,7),(4,-1),(-1,17)):
                    expected=sum((a*i+b)//m for i in range(n))
                    if expected>=0:
                        native.append(f'assert(floor_sum({n},{m},{a},{b})=={expected});')
                        guards+=f'#guard (match SignedSource.floor_sum.callFuel 4000 [] [.value {n},.value {m},.value ({a}),.value ({b})] with | .finished r => r.value == {expected} && r.memory == [] | _ => false)\n'
        # These remain model failures until implementation-defined signed
        # narrowing has an explicit target-compiler contract and execution rule.
        guards+='''#guard SignedSource.floor_sum.callFuel 4000 [] [.value 2,.value 1,.value 0,.value (-1)] == .fault
#guard SignedSource.floor_sum.callFuel 4000 [] [.value 2,.value 1,.value 0,.value 9223372036854775807] == .fault
#guard SignedSource.floor_sum.callFuel 4000 [] [.value (-1),.value 1,.value 0,.value 0] == .fault
#guard SignedSource.floor_sum.callFuel 4000 [] [.value 4294967296,.value 1,.value 0,.value 0] == .fault
#guard SignedSource.floor_sum.callFuel 4000 [] [.value 1,.value 0,.value 0,.value 0] == .fault
'''
        with tempfile.TemporaryDirectory() as directory:
            proof=Path(directory)/'test.lean';proof.write_text(generated+'\n'+guards)
            lake,env=lean_environment()
            result=subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            cpp=Path(directory)/'native.cpp';binary=Path(directory)/'native'
            cpp.write_text('#include \"template/small_template.hpp\"\n#include \"number_theory/floor_sum.hpp\"\nint main(){'+''.join(native)+'assert(floor_sum(2,1,0,-1)==-2);assert(floor_sum(2,1,0,INT64_MAX)==-2);}')
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined','-fno-sanitize-recover=all','-I',str(includes[0]),str(cpp),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)


if __name__=='__main__':
    disable_network()
    unittest.main()
