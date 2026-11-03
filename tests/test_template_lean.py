"""Generated template families specialize to actual syntax-generated programs."""
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'verifier'))
sys.path.insert(0,str(ROOT/'tools'))
import template_ir
import state_ir
from test_scalar_ir import lean_environment
from offline import disable_network

HEADER=ROOT/'experiments/verification/template/update_extrema.hpp'

class TemplateLeanTests(unittest.TestCase):
    def test_every_builtin_specialization_matches_actual_clang_in_lean(self):
        primary=template_ir.lower_source(HEADER)
        self.assertEqual(template_ir.emit_lean(primary),(ROOT/'Proofs/IntegralExtrema.lean').read_text())
        lake,env=lean_environment()
        with tempfile.TemporaryDirectory(prefix='template-lean-') as directory:
            scratch=Path(directory);cpp=scratch/'instances.cpp';lean=scratch/'proof.lean'
            text=f'#include "{HEADER}"\n'
            for t in primary['templates']:
                for left in template_ir.TYPES:
                    for right in template_ir.TYPES:
                        text+=f'template bool cp::{t["name"]}<{left},{right}>({left}&,const {right}&);\n'
            cpp.write_text(text)
            proof='import Proofs.IntegralExtremaShape\n'
            for policy,profile in [(False,'checked'),(True,template_ir.SIGNED_CONVERSIONS[1])]:
                namespace='ActualChecked' if not policy else 'ActualTarget'
                actual=state_ir.lower_source(cpp,signed_conversion=profile)
                proof+=re.sub(r'^import .*\n','',state_ir.emit_lean(actual,namespace),flags=re.M)+'\n'
                for f in actual['functions']:
                    args=','.join('.'+template_ir.INTEGRAL_NAMES[t] for t in f['template_arguments'])
                    proof+=f'example : Proofs.IntegralExtrema.{f["cpp_name"]}.instantiate [{args}] {str(policy).lower()} = some {namespace}.{f["name"]} := rfl\n'
            proof+='''open Proofs.CppTemplate
example : Proofs.IntegralExtrema.chmax.instantiate [.i32] = none := rfl
example : Proofs.IntegralExtrema.chmin.instantiate [.i32,.i32,.i32] = none := rfl
example : TypeExpr.resolve [] (.parameter 0) = none := rfl
example : Statement.instantiate [.i32] false [⟨.parameter 0,true,false⟩] .boolean
    (.assign 0 (.literal (.scalar .i32) 1)) = none := rfl
example : Statement.instantiate [.i32] false [] .boolean
    (.assign 0 (.literal (.scalar .i32) 1)) = none := rfl
'''
            lean.write_text(proof)
            checked=subprocess.run([lake,'env','lean',str(lean)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertEqual(checked.returncode,0,checked.stdout+checked.stderr)

    def test_name_and_source_changes_are_reflected_in_generated_lean(self):
        original=template_ir.emit_lean(template_ir.lower_source(HEADER))
        with tempfile.TemporaryDirectory(prefix='template-lean-change-') as directory:
            source=Path(directory)/'source.hpp'
            source.write_text(HEADER.read_text().replace('a < b','a <= b'))
            changed=template_ir.emit_lean(template_ir.lower_source(source))
            self.assertNotEqual(changed,original)
            self.assertIn('.comparison .le',changed)
            source.write_text(re.sub(r'\b(S|T|a|b)\b',lambda m:{'S':'X','T':'Y','a':'left','b':'right'}[m[0]],HEADER.read_text()))
            self.assertEqual(template_ir.emit_lean(template_ir.lower_source(source)),original)
            with self.assertRaises(ValueError):template_ir.emit_lean(template_ir.lower_source(source),'Bad;Namespace')

if __name__=='__main__':
    disable_network();lake,env=lean_environment()
    subprocess.run([lake,'build','Proofs.IntegralExtremaShape'],cwd=ROOT,env=env,check=True)
    unittest.main()
