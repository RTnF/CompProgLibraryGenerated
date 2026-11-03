"""Explicit scalar casts: Clang conversions, C++ comparison and rejection."""

from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "verifier"))
sys.path.insert(0, str(ROOT / "tools"))
from scalar_ir import lower_source, emit_lean
from test_scalar_ir import lean_environment
from offline import disable_network


class CastTests(unittest.TestCase):
    def test_all_three_forms_types_boundaries_and_model_rejections(self):
        types = [('bool',1,False,True),('int',32,True,False),('unsigned int',32,False,False),
                 ('long',64,True,False),('unsigned long',64,False,False)]
        aliases = '\n'.join(f'using cast_target_{i}={t[0]};' for i,t in enumerate(types))
        declarations, calls, invalid = [], [], []
        for i, (source_type, width, signed, boolean) in enumerate(types):
            low = -(1 << (width-1)) if signed else 0
            high = 1 if boolean else (1 << (width-int(signed))) - 1
            values = sorted({v for v in [low,low+1,-1,0,1,high-1,high,2147483648,4294967296]
                             if low<=v<=high})
            for j,(target_type,target_width,target_signed,target_boolean) in enumerate(types):
                forms = [f'({target_type})x',f'static_cast<{target_type}>(x)',f'cast_target_{j}(x)']
                for k, expression in enumerate(forms):
                    name = f'cast_{i}_{j}_{k}'
                    declarations.append(f'{target_type} {name}({source_type} x){{return {expression};}}')
                    for v in values:
                        if target_boolean:
                            expected = int(v != 0)
                        elif target_signed:
                            if not -(1 << (target_width-1)) <= v < (1 << (target_width-1)):
                                invalid.append((name,v))
                                continue
                            expected = v
                        else:
                            expected = v % (1 << target_width)
                        calls.append((name,source_type,v,expected))
        text = aliases + '\nnamespace cp {\n' + '\n'.join(declarations) + '\n}'
        with tempfile.TemporaryDirectory(prefix='explicit-casts-') as directory:
            scratch = Path(directory)
            source, proof, binary = scratch/'test.cpp',scratch/'test.lean',scratch/'test'
            source.write_text(text)
            ir = lower_source(source)
            # The forms select the same semantic rule, including NoOp wrappers.
            for start in range(0,len(ir['functions']),3):
                results = [f['result'] for f in ir['functions'][start:start+3]]
                self.assertEqual(results[0],results[1]); self.assertEqual(results[1],results[2])
            guards = [f'#guard (CastTest.{name}.call [{v}]).map (·.value) == some ({expected})'
                      for name,_,v,expected in calls]
            guards += [f'#guard CastTest.{name}.call [{v}] == none' for name,v in invalid]
            guards += ['#guard (CastTest.cast_3_1_1.call [7]).map (·.work) == some 3',
                       '#guard (CastTest.cast_1_1_1.call [7]).map (·.work) == some 2']
            proof.write_text(emit_lean(ir,'CastTest')+'\n'+'\n'.join(guards))
            lake, env = lean_environment()
            subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,check=True)
            def literal(v):
                if v == -(1<<63):
                    return '(-9223372036854775807LL-1LL)'
                return f'(-{-v}LL)' if v < 0 else f'{v}ULL'
            source.write_text('#include <iostream>\n'+text+'\nint main(){\n'+'\n'.join(
                f"std::cout << cp::{name}(static_cast<{ty}>({literal(v)})) << '\\n';"
                for name,ty,v,_ in calls)+'\n}')
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined',
                '-fno-sanitize-recover=all',str(source),'-o',str(binary)],check=True)
            actual = [int(v) for v in subprocess.check_output([str(binary)],text=True).splitlines()]
            self.assertEqual(actual,[expected for _,_,_,expected in calls])
            source.write_text('namespace cp {int f(long x){return static_cast<bool>(x);}}')
            proof.write_text(emit_lean(lower_source(source),'ChangedCast')+
                '\n#guard (ChangedCast.f.call [7]).map (·.value) == some 7\n')
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,capture_output=True,text=True)
            self.assertNotEqual(result.returncode,0)
            self.assertIn('did not evaluate to `true`',result.stdout+result.stderr)

    def test_noninteger_and_reference_casts_are_refused(self):
        cases = ['int f(int x){return static_cast<int&>(x);}',
                 'int f(int x){return (int&)x;}',
                 'int f(int x){return static_cast<int&&>(x);}',
                 'int f(int x){return const_cast<const int&>(x);}',
                 'long f(int x){return reinterpret_cast<long>(&x);}',
                 'int f(int x){return static_cast<int>(double(x));}',
                 'int f(int x){return (int)(++x);}']
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory)/'test.cpp'
            for case in cases:
                source.write_text('namespace cp {'+case+'}')
                with self.subTest(case=case),self.assertRaises(ValueError):
                    lower_source(source)


if __name__ == '__main__':
    disable_network()
    lake, env = lean_environment()
    subprocess.run([lake,'build','Proofs.CppScalar'],cwd=ROOT,env=env,check=True)
    unittest.main()
