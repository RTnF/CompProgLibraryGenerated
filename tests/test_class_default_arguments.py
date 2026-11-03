"""Declaration-owned default arguments at constructor/method boundaries."""
from pathlib import Path
import copy,sys,tempfile,unittest
from unittest import mock
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'tests'),str(ROOT/'verifier'),str(ROOT/'tools')]
import class_call_ir as calls
import test_class_call_ir as helpers
from offline import disable_network

class DefaultArgumentTests(unittest.TestCase):
 def test_constructor_method_defaults_and_explicit_arguments(self):
  with tempfile.TemporaryDirectory(prefix='class-defaults-') as directory:
   source=Path(directory)/'source.hpp'
   source.write_text('''#include <vector>
struct Number {
 std::vector<int> data;int count;
 Number(int n=1+1,int value=static_cast<int>(3u)):data(n,0),count(value){}
 int get(int extra=4)const{return count+extra;}
 void set(int value=6){count=value;}
};
int use(){int n=99;Number a;const Number b(1);Number c(1,8);
 int x=a.get();a.set();int y=a.get();int z=b.get(5);int w=c.get();
 return x*1000+y*100+z*10+w;}
''')
   generated=calls.emit_class_callers(source,'Number','Generated')
   checks='''
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
 def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
 #guard (match Generated.use.callFuel 1024 empty [] with
   | .finished (out,.scalar value) => value == 8092 && out.scalars.memory == [] &&
       out.slots == [] && [0,1,2].all (fun owner => (out.frame.state.storage.lookup owner).isNone)
   | _ => false)
'''
   helpers.ClassCallerTests.check_lean(self,generated+checks,directory)
   self.assertEqual(helpers.ClassCallerTests.native(self,source,'std::cout << use();',directory),'8092')

 def test_target_signed_conversion_in_defaults(self):
  with tempfile.TemporaryDirectory(prefix='class-defaults-conversion-') as directory:
   source=Path(directory)/'source.hpp'
   source.write_text("""#include <vector>
struct Number {
 std::vector<int> data;int count;
 Number(int n=static_cast<int>(0xffffffffu)):data(1,n),count(n){}
 int get(int extra=static_cast<int>(0xffffffffu))const{return count+extra;}
};
int use(){Number p;return p.get();}
""")
   generated=calls.emit_class_callers(source,'Number','Generated',
     signed_conversion='gcc13.3-lp64-twos-complement')
   checks="""
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
 def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
 #guard (match Generated.use.callFuel 512 empty [] with
   | .finished (out,.scalar value) => value == -2 && out.scalars.memory == [] &&
       out.slots == [] && (out.frame.state.storage.lookup 0).isNone
   | _ => false)
"""
   helpers.ClassCallerTests.check_lean(self,generated+checks,directory)
   self.assertEqual(helpers.ClassCallerTests.native(self,source,'std::cout << use();',directory),'-2')

 def test_mismatched_expanded_default_expression_rejected(self):
  with tempfile.TemporaryDirectory(prefix='class-defaults-identity-') as directory:
   source=Path(directory)/'source.hpp'
   source.write_text("""#include <vector>
struct Number {std::vector<int> data;int count;
 Number(int n=2):data(n,0),count(n){}
 int get()const{return count;}
};
int use(){Number p;return p.get();}
""")
   original=calls._default_arguments
   def alter(arguments,defaults):
    changed=copy.deepcopy(arguments)
    for argument in changed:
     if argument.get('kind')=='CXXDefaultArgExpr' and argument.get('inner'):
      expression=argument['inner'][0]
      self.assertEqual(expression['kind'],'IntegerLiteral')
      expression['value']='99' # Preserve the ID but change the expression.
      break
    return original(changed,defaults)
   with mock.patch.object(calls,'_default_arguments',alter):
    with self.assertRaisesRegex(ValueError,'original declaration expression'):
     calls.lower_class_callers(source,'Number')

 def test_effectful_defaults_rejected(self):
  for boundary in ('constructor','method'):
   with self.subTest(boundary=boundary),tempfile.TemporaryDirectory(prefix='class-defaults-reject-') as directory:
    source=Path(directory)/'source.hpp'
    ctor='int n=++ticks' if boundary=='constructor' else 'int n=1'
    extra='int extra=++ticks' if boundary=='method' else 'int extra=0'
    source.write_text(f'''#include <vector>
int ticks=0;
struct Number {{std::vector<int> data;int count;
 Number({ctor}):data(n,0),count(n){{}}
 int get({extra})const{{return count+extra;}}
}};
int use(){{Number p;return p.get();}}
''')
    with self.assertRaisesRegex(ValueError,'side-effect-free'):
     calls.lower_class_callers(source,'Number')
    # An unused default expression is not evaluated by C++.
    source.write_text(source.read_text().replace('Number p;return p.get();','Number p(2);return p.get(3);'))
    generated=calls.emit_class_callers(source,'Number','Generated')
    checks="""
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
 def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
 #guard (match Generated.use.callFuel 512 empty [] with
   | .finished (out,.scalar value) => value == 5 && out.scalars.memory == [] && out.slots == []
   | _ => false)
"""
    helpers.ClassCallerTests.check_lean(self,generated+checks,directory)
    self.assertEqual(helpers.ClassCallerTests.native(self,source,'std::cout << use() << " " << ticks;',directory),'5 0')

if __name__=='__main__':
 disable_network();unittest.main()
