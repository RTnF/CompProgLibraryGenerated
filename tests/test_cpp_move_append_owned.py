"""New owned-buffer export preserves old identities, stale grants and heap invariants."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT / 'tools'), str(ROOT / 'tests')]
from test_scalar_ir import lean_environment
from test_cpp_move_call_layout import APART_DEFINITIONS
from test_cpp_move_receiver_layout import UF_CHECKS, RECEIVER_CHECKS
from test_uf_receiver_layout import CHECKS as FRAME_CHECKS
from test_cpp_move_object_receiver import CHECKS as OBJECT_CHECKS
from test_uf_object_state import CHECKS as STATE_CHECKS
from test_uf_object_root_scalar_peak import CHECKS as ROOT_CHECKS
from test_uf_object_trace import CHECKS as TRACE_CHECKS, MEANING_CHECKS
from test_uf_object_heap_peak import CHECKS as HEAP_CHECKS
from offline import disable_network

PAYLOAD_CHECKS = r'''
namespace AppendOwnedPayloadExamples
open Proofs.CppMoveAppendOwned Proofs.CppMoveHeaders Proofs.CppMoveFrame Proofs.CppMoveSpace
open UfMoveCallExamples UfReceiverLayoutExamples

def payload : Proofs.CppVector.Buffer Int := ⟨0,[9,-7],2,limit,0⟩
def exported := appended moved.1.objects.heap payload 1 false

example : Unique exported ∧ OwnsAll exported ∧ HeadersLive exported ∧ AllocationsValid exported ty := by
  exact ⟨appended_unique _ _ _ _ unique UfObjectHeapPeakExamples.headerLive,
    appended_ownsAll _ _ _ _ covered,appended_headersLive _ _ _ _ UfObjectHeapPeakExamples.headerLive,
    appended_valid _ _ _ _ ty allocationsValid (by decide +kernel)⟩
example : currentBuffer exported 2 ⟨some 2,1,false,limit⟩ = some ⟨2,[9,-7],2,limit,0⟩ :=
  current_buffer _ _ _ _
example : Proofs.CppMoveHeaders.read exported ty.valid 0 = some 2 := by decide +kernel
example : Proofs.CppMoveHeaders.read exported ty.valid 1 = none := by decide +kernel
example : exported.allocation 1 = none := by decide +kernel
example : exported.liveSpace = 10 := by decide +kernel
example : Proofs.CppMoveHeaders.capture exported ty.valid 2 0 true = none := by decide +kernel
example : Proofs.CppMoveHeaders.readable exported ⟨some 2,1,false,limit⟩ ty.valid = true := by decide +kernel
end AppendOwnedPayloadExamples
'''

EMPTY_CHECKS = r'''
namespace AppendOwnedEmptyExamples
open Proofs.CppMoveAppendOwned Proofs.CppMoveHeaders Proofs.CppMoveFrame Proofs.CppMoveSpace
open UfMoveCallExamples UfReceiverLayoutExamples

def payload : Proofs.CppVector.Buffer Int := ⟨0,[],0,limit,0⟩
def exported := appended moved.1.objects.heap payload 1 false

example : Unique exported ∧ OwnsAll exported ∧ HeadersLive exported ∧ AllocationsValid exported ty := by
  exact ⟨appended_unique _ _ _ _ unique UfObjectHeapPeakExamples.headerLive,
    appended_ownsAll _ _ _ _ covered,appended_headersLive _ _ _ _ UfObjectHeapPeakExamples.headerLive,
    appended_valid _ _ _ _ ty allocationsValid (by decide +kernel)⟩
example : currentBuffer exported 2 ⟨some 2,1,false,limit⟩ = some ⟨2,[],0,limit,0⟩ :=
  current_buffer _ _ _ _
example : Proofs.CppMoveHeaders.read exported ty.valid 0 = some 2 := by decide +kernel
example : Proofs.CppMoveHeaders.read exported ty.valid 1 = none := by decide +kernel
example : exported.allocation 1 = none := by decide +kernel
example : exported.liveSpace = 8 := by decide +kernel
example : Proofs.CppMoveHeaders.capture exported ty.valid 2 0 true = none := by decide +kernel
example : Proofs.CppMoveHeaders.capture exported ty.valid 2 0 false = none := by decide +kernel
end AppendOwnedEmptyExamples
'''

class CppMoveAppendOwnedTests(unittest.TestCase):
    def check_lean(self, checks):
        with tempfile.TemporaryDirectory(prefix='cpp-move-append-owned-') as directory:
            proof = Path(directory) / 'checks.lean'
            proof.write_text('import Proofs.CppMoveAppendOwned\nimport Proofs.UfObjectTotalPeak\nimport Proofs.UfClassCopyBridge\n' +
                UF_CHECKS + RECEIVER_CHECKS + FRAME_CHECKS +
                OBJECT_CHECKS.split('namespace GeneratedObjectReceiverExamples')[0] +
                APART_DEFINITIONS + STATE_CHECKS + TRACE_CHECKS + MEANING_CHECKS + ROOT_CHECKS + HEAP_CHECKS + checks)
            lake, env = lean_environment()
            result = subprocess.run([lake, 'env', 'lean', str(proof)], cwd=ROOT,
                env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertNotIn('warning:', result.stdout + result.stderr)

    def test_new_readonly_payload_preserves_existing_and_stale_grants(self):
        self.check_lean(PAYLOAD_CHECKS)

    def test_empty_allocation_counts_header_without_reviving_stale_grant(self):
        self.check_lean(EMPTY_CHECKS)

if __name__ == '__main__':
    disable_network()
    unittest.main()
