"""Void return control, caller aliases and constructor field retirement."""
from pathlib import Path
import sys,tempfile,unittest
ROOT=Path(__file__).resolve().parent.parent
sys.path[:0]=[str(ROOT/'tests'),str(ROOT/'verifier'),str(ROOT/'tools')]
import test_class_call_ir as helpers
from test_union_find_original_api import HEADER as CALLER_HEADER
from nested_ir import lower_source,emit_lean
from class_call_ir import emit_class_callers
from class_copy_layout import emit_class_layout
from offline import disable_network

class RetUnitTests(unittest.TestCase):
 def test_plain_void_early_return_retires_locals_and_keeps_aliases(self):
  with tempfile.TemporaryDirectory(prefix='ret-unit-plain-') as directory:
   source=Path(directory)/'source.hpp'
   source.write_text('''#include <vector>
void apply(std::vector<int> &v,int &x,bool stop){std::vector<int> local(3,7);if(stop)return;v[0]=9;x=5;}
''')
   generated=emit_lean(lower_source(source),'Generated')
   checks=r'''
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
 def bty : Proofs.CppScalar.Ty := ⟨1,false,true⟩
 def run (stop : Int) := Generated.apply.callFuel 128 (caller [1] 2)
   [.vectorReference 0,.scalarReference 1,.value (.literal bty stop)]
 #guard (match run 1 with
   | .finished (out,.unit) => out.scalars.memory == (caller [1] 2).scalars.memory &&
       out.slots == (caller [1] 2).slots && out.frame.state.storage.lookup 1 == none &&
       (out.frame.state.storage.lookup 0).map (·.items) == some [Value.integer 1]
   | _ => false)
 #guard (match run 0 with
   | .finished (out,.unit) => out.scalars.memory.map (·.value) == ([5,9876] : List Int) &&
       (out.scalarCell 2 intTy).map (fun (_,c) => c.value) == some (5 : Int) &&
       out.frame.state.storage.lookup 1 == none &&
       (out.frame.state.storage.lookup 0).map (·.items) == some [Value.integer 9]
   | _ => false)
 def bad : NProgram := ⟨[],.unit,.primitive (.ret (.literal intTy 1))⟩
 #guard bad.callFuel 8 (caller [1] 2) [] == .fault
'''
   helpers.ClassCallerTests.check_lean(self,generated+CALLER_HEADER+checks,directory)
   main='std::vector<int> a{1};int x=2;apply(a,x,true);std::cout << a[0] << " " << x << " ";apply(a,x,false);std::cout << a[0] << " " << x;'
   self.assertEqual(helpers.ClassCallerTests.native(self,source,main,directory),'1 2 9 5')

 def test_bare_constructor_return_and_void_method_return(self):
  with tempfile.TemporaryDirectory(prefix='ret-unit-class-') as directory:
   source=Path(directory)/'source.hpp'
   source.write_text('''#include <vector>
struct Returner {
 std::vector<int> data;int count;
 Returner(int n):data(n,0),count(0){if(n==0)return;count=1;}
 void update(int x){std::vector<int> local(2,3);if(x<0)return;count=x;}
 int get()const{return count;}
};
int use(int n){Returner p(n);p.update(-1);int a=p.get();p.update(5);int b=p.get();return a*10+b;}
void configure(Returner &r,int x){Returner local(1);if(x<0)return;return r.update(x);}
''')
   generated=emit_class_callers(source,'Returner','Generated')+emit_class_layout(source,'Returner','Constructors')
   checks=r'''
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppLoop
 def i32 : Ty := ⟨32,true,false⟩
 def empty : NState := ⟨⟨[],[],0,0,0⟩,⟨⟨⟨[]⟩,⟨[],0,0,0⟩⟩,[],[]⟩,[],0,0⟩
 #guard (match Generated.use.callFuel 1024 empty [.value (.literal i32 0)] with
   | .finished (out,.scalar value) => value == 5 && out.scalars.memory == [] &&
       [0,1,2].all (fun owner => (out.frame.state.storage.lookup owner).isNone)
   | _ => false)
 #guard (match Generated.use.callFuel 1024 empty [.value (.literal i32 2)] with
   | .finished (out,.scalar value) => value == 15 && out.scalars.memory == [] &&
       [0,1,2].all (fun owner => (out.frame.state.storage.lookup owner).isNone)
   | _ => false)
'''
   checks+=r"""
 #guard (match Constructors.Returner_construct0_exportViewFuel 32 empty [.value (.literal i32 2)] false with
   | .finished (s,obj) => match Generated.configure_arguments obj (.value (.literal i32 (-1))) with
     | some args => match Generated.configure.callFuel 1024 s args with
       | .finished (out,.unit) => out.scalars.memory == s.scalars.memory && out.slots == s.slots &&
           (out.frame.state.storage.lookup 1).isNone
       | _ => false
     | _ => false
   | _ => false)
 #guard (match Constructors.Returner_construct0_exportViewFuel 32 empty [.value (.literal i32 2)] false with
   | .finished (s,obj) => match Generated.configure_arguments obj (.value (.literal i32 5)) with
     | some args => match Generated.configure.callFuel 1024 s args with
       | .finished (out,.unit) => out.scalars.memory == [⟨i32,5⟩] && out.slots == s.slots &&
           (out.frame.state.storage.lookup 1).isNone && (out.frame.state.storage.lookup 2).isNone
       | _ => false
     | _ => false
   | _ => false)
"""
   helpers.ClassCallerTests.check_lean(self,generated+checks,directory)
   self.assertEqual(helpers.ClassCallerTests.native(self,source,'std::cout << use(0) << " " << use(2);Returner r(2);configure(r,-1);std::cout << " " << r.get();configure(r,5);std::cout << " " << r.get();',directory),'5 15 1 5')

if __name__=='__main__':
 disable_network();unittest.main()
