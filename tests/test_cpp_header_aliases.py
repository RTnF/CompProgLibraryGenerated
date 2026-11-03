"""Root/child header identity and resolver metadata across actual calls."""
from pathlib import Path
import subprocess
import tempfile
import unittest
from test_scalar_ir import lean_environment
from test_dynamic_expr import fixture_checks
from test_cpp_no_resize import CHECKS as SCALAR_CHECKS
from test_cpp_reference_headers import NESTED, UNION_FIND
from test_union_find_construction import HEADER
from test_union_find_original_api import HEADER as CALLER_HEADER
from test_union_find_construction_footprint import CHECKS as STAGE_CHECKS
from test_union_find_constructed_receiver import CHECKS as RECEIVER_CHECKS
from test_union_find_receiver_trace import CHECKS as TRACE_CHECKS
from test_union_find_rank_doubling import CHECKS as RANK_CHECKS
from test_cpp_call_metadata import METADATA
from offline import disable_network

ROOT = Path(__file__).resolve().parent.parent
ALIASES = '''
open Proofs.CppHeaderAliases Proofs.CppBufferHeaders
 def childGrant : Binding := entry.frame.bindings[3]?.getD ⟨4,atom,false,.root 0⟩
 def parentBuffer : Proofs.CppVector.Buffer Value := (entry.frame.state.storage.lookup 0).getD ⟨0,[],0,64,0⟩
 def parentTag : Proofs.CppVectorOwnership.Tag := (entry.frame.state.forest.lookup 0).getD ⟨row,none,some 0,[]⟩
 example := nested_lookup_kept entry.frame.state updated.frame.state 0 atom parentBuffer parentTag effects.headers
   (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
 example (binding : Binding) := header_owner entry updated binding effects (by decide +kernel) (by decide +kernel)
 example (slot : Nat) (element : Element) := resolve_signature entry updated slot element effects
   (by decide +kernel) (by decide +kernel)
 example := resolve_kept entry updated 3 atom childGrant rowBuffer effects
   (by decide +kernel) (by decide +kernel) (by decide +kernel)
 #guard entry.frame.headerOwner childGrant == some 4
 #guard updated.frame.headerOwner childGrant == some 4
 #guard entry.frame.resolve 3 atom != updated.frame.resolve 3 atom
 #guard (entry.frame.resolve 3 atom).map (fun pair => (pair.1,signature pair.2)) ==
   (updated.frame.resolve 3 atom).map (fun pair => (pair.1,signature pair.2))
 def badBindings : List Binding := [
   ⟨0,row,false,.root 999⟩,⟨999,atom,false,.root 0⟩,
   {childGrant with header := .child ⟨0,parentBuffer.epoch+1,1⟩},
   {childGrant with header := .child ⟨0,parentBuffer.epoch,999⟩},
   {childGrant with header := .child ⟨2,0,0⟩},
   {childGrant with element := .integer ⟨64,false,false⟩}]
 #guard badBindings.all (fun binding => (entry.frame.headerOwner binding).isNone &&
   (updated.frame.headerOwner binding).isNone)
 #guard (entry.frame.bindings++badBindings).all (fun binding =>
   entry.frame.headerOwner binding == updated.frame.headerOwner binding)
 #guard [0,1,2,3,999].all (fun slot => [row,atom,.integer ⟨64,false,false⟩].all (fun element =>
   (entry.frame.resolve slot element).map (fun pair => (pair.1,signature pair.2)) ==
     (updated.frame.resolve slot element).map (fun pair => (pair.1,signature pair.2))))
 #guard (malformed.frame.headerOwner childGrant).isNone
 #guard (updated.frame.headerOwner childGrant).isSome
 #guard (malformed.frame.resolve 3 atom).isNone
 #guard (updated.frame.resolve 3 atom).isSome
 example (s t : NState) (binding : Binding) (effects : CallEffects s t)
   (before : s.frame.state.wellFormed = true) (after : t.frame.state.wellFormed = true) :=
   header_owner s t binding effects before after
 example (s t : NState) (slot : Nat) (element : Element) (effects : CallEffects s t)
   (before : s.frame.state.wellFormed = true) (after : t.frame.state.wellFormed = true) :=
   resolve_signature s t slot element effects before after
'''
TRACE_ALIASES = '''
open Proofs.UfReceiverAliases
 example := of_effects built final finalEffects (by decide +kernel) (by decide +kernel)
 example := actual_calls_preserve (List.replicate mixed.length 128) mixed built final (layoutOf populated)
   [4,0,2,0,2,0,0,1,4,1,0,1] (by decide +kernel) (by decide +kernel) builtContexts (by decide +kernel)
 example := calls_work_aliases mixed built (layoutOf populated) (List.replicate 4 (-1)) 4 (fun _ => 0) builtStrong mixedAllowed
 #guard built.frame.bindings.all (fun binding => built.frame.headerOwner binding == final.frame.headerOwner binding)
 #guard [0,1,999].all (fun slot =>
   (built.frame.resolve slot (.integer i32)).map (fun pair => (pair.1,Proofs.CppBufferHeaders.signature pair.2)) ==
     (final.frame.resolve slot (.integer i32)).map (fun pair => (pair.1,Proofs.CppBufferHeaders.signature pair.2)))
 #guard built.frame.resolve 1 (.integer i32) != final.frame.resolve 1 (.integer i32)
 example (fuel : Nat) (s out : NState) (layout : Layout) (op : Operation) (ret : Ret)
   (ps vec : List Int) (count nextCount : Int) (rank nextRank : Nat → Nat)
   (before : Represents s layout ps count rank) (after : Represents out layout vec nextCount nextRank)
   (ran : call fuel s layout op = .finished (out,ret)) := call_preserves fuel s out layout op ret
     ps vec count nextCount rank nextRank before after ran
 example (ops : List Operation) (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
   (strong : Proofs.UfBalancedReceiver.Strong s layout ps count rank)
   (allowed : ∀ op ∈ ops, op.allowed ps.length) := calls_work_aliases ops s layout ps count rank strong allowed
'''

class HeaderAliasTests(unittest.TestCase):
    def check(self, source):
        with tempfile.TemporaryDirectory(prefix='cpp-header-aliases-') as directory:
            proof = Path(directory)/'checks.lean'
            proof.write_text(source)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT, env=env,
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout+result.stderr)

    def test_nested_headers_and_resolvers(self):
        self.check('import Proofs.CppHeaderAliases\nimport Proofs.Generated.UnionFindCandidate\n'
                   +'\n'.join(fixture_checks())+SCALAR_CHECKS+NESTED+ALIASES)

    def test_union_find_calls_and_trace(self):
        self.check('import Proofs.UfReceiverAliases\n'+HEADER+CALLER_HEADER+STAGE_CHECKS
                   +RECEIVER_CHECKS+TRACE_CHECKS+RANK_CHECKS+METADATA+UNION_FIND+TRACE_ALIASES)

if __name__ == '__main__':
    disable_network()
    unittest.main()
