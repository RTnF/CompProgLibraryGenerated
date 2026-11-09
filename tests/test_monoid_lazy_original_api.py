"""Preserve the original nested API in an unpublished namespace candidate."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parent.parent
sys.path.insert(0,str(ROOT/'tools'))
from check_public import check_compiler,lower_priority
from offline import disable_network

ORIGINAL=ROOT/'experiments/library/cpp/algebraic_structure/monoid_lazy.hpp'
CANDIDATE=ROOT/'experiments/verification/algebraic_structure/monoid_lazy.hpp'

class MonoidLazyOriginalApiTests(unittest.TestCase):
    def test_original_body_and_generic_copy_effects_are_preserved(self):
        original=ORIGINAL.read_text().removeprefix('#pragma once\n#include "template/small_template.hpp"\n')
        candidate=CANDIDATE.read_text().split('namespace cp {\n',1)[1].removesuffix('\n} // namespace cp\n')
        self.assertEqual(candidate,original)
        check_compiler()
        flags=['-std=c++17','-O1','-Wall','-Wextra','-pedantic','-fsanitize=undefined',
               '-fno-sanitize-recover=all','-I',str(ROOT),'-I',str(ROOT/'experiments/library/cpp')]
        with tempfile.TemporaryDirectory(prefix='monoid-lazy-api-') as tmp:
            directory=Path(tmp);traces=[]
            for tag,define in [('original',[]),('candidate',['-DCANDIDATE_API'])]:
                binary=directory/tag
                subprocess.run(['g++',*flags,*define,str(ROOT/'tests/imports/monoid_lazy_api_events.cpp'),
                                '-o',str(binary)],check=True,timeout=60)
                result=subprocess.run([str(binary)],capture_output=True,text=True,check=True,timeout=10)
                self.assertEqual(len(result.stdout.splitlines()),10)
                traces.append(result.stdout)
            self.assertEqual(traces[0],traces[1])
            # Original callers exercise every nested value/action family.
            for kind in ('add_extrema','set_extrema','add_sum','set_sum'):
                driver=directory/(kind+'.cpp')
                driver.write_text('#include "'+str(CANDIDATE)+'"\nusing namespace cp;\n'+
                    (ROOT/'tests/imports'/('original_mixed_'+kind+'.cpp')).read_text())
                binary=directory/(kind+'-native')
                subprocess.run(['g++',*flags,str(driver),'-o',str(binary)],check=True,timeout=60)
                subprocess.run([str(binary)],check=True,timeout=10)
            old=directory/'old.hpp'
            old.write_text(ORIGINAL.read_text().replace('return RangeAdd(0);','return 0;'))
            control=directory/'old_id.cpp'
            control.write_text('#include "old.hpp"\nstruct Box{int v;Box(int x):v(x){}};\n'
                'int main(){auto a=RangeAddRangeMaxMin<Box>::RangeAdd::id();'
                'auto b=RangeAddRangeSum<Box>::RangeAdd::id();return a.v+b.v;}\n')
            rejected=subprocess.run(['g++',*flags,'-fsyntax-only',str(control)],capture_output=True,text=True,timeout=60)
            self.assertNotEqual(rejected.returncode,0)
            self.assertGreaterEqual(rejected.stderr.count('could not convert'),2)
            # The currently published flat API is still missing these names.
            # Keep this control until the actual public switch is verified.
            control=directory/'flat.cpp'
            control.write_text('#include "library/algebraic_structure/monoid_lazy.hpp"\nusing namespace cp;\n'+
                (ROOT/'tests/imports/original_mixed_add_extrema.cpp').read_text())
            rejected=subprocess.run(['g++',*flags,'-fsyntax-only',str(control)],capture_output=True,text=True,timeout=60)
            self.assertNotEqual(rejected.returncode,0)
            self.assertIn('RangeAddRangeMaxMin',rejected.stderr)

if __name__=='__main__':
    disable_network();lower_priority();unittest.main()
