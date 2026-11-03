"""The actual fifteen-vector allocation prefix, including its input buffer."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
sys.path[:0] = [str(ROOT/'tools'),str(ROOT/'tests')]
from offline import disable_network
from test_scalar_ir import lean_environment


class BeatsAllocationTests(unittest.TestCase):
    def check_fixtures(self, module, names):
        with tempfile.TemporaryDirectory(prefix='beats-allocation-') as directory:
            proof = Path(directory)/'check.lean'
            proof.write_text(f'import Proofs.{module}\n' + '\n'.join(
                (ROOT/'tests/lean'/name).read_text() for name in names))
            lake,env = lean_environment()
            result = subprocess.run([lake,'env','lean',str(proof)],cwd=ROOT,env=env,
                                    capture_output=True,text=True)
            self.assertEqual(result.returncode,0,result.stdout+result.stderr)
            self.assertNotIn('warning:',result.stdout+result.stderr)

    def test_actual_prefix_and_field_models(self):
        self.check_fixtures('BeatsAllocation',['beats_allocation.lean'])

    def test_exact_buffers_storage_work_and_arguments(self):
        self.check_fixtures('BeatsAllocationLayout',['beats_allocation.lean','beats_allocation_layout.lean'])

    def test_complete_constructor_vector_conditions(self):
        self.check_fixtures('BeatsAllocationArgs',[
            'beats_allocation.lean','beats_allocation_layout.lean','beats_allocation_args.lean'])

    def test_normalized_wide_constructor_call(self):
        self.check_fixtures('BeatsWideCall',[
            'beats_allocation.lean','beats_allocation_layout.lean','beats_wide_call.lean'])

    def test_inline_frame_and_complete_stage(self):
        self.check_fixtures('BeatsInlineExec',[
            'beats_allocation.lean','beats_allocation_layout.lean',
            'beats_inline_frame.lean','beats_inline_exec.lean'])

    def test_root_input_prepare_and_stage(self):
        self.check_fixtures('BeatsInputPrepare',['beats_input_prepare.lean'])

    def test_constructor_final_layout_and_export(self):
        self.check_fixtures('BeatsConstructorFields',[
            'beats_allocation.lean','beats_constructor_fields.lean'])

    def test_root_caller_to_constructed_object(self):
        self.check_fixtures('BeatsConstructReceiver',[
            'beats_input_prepare.lean','beats_construct_call.lean','beats_construct_receiver.lean'])

    def test_receiver_method_trace_matches_cpp(self):
        self.check_fixtures('BeatsReceiverRestore',[
            'beats_input_prepare.lean','beats_construct_call.lean','beats_receiver_calls.lean',
            'beats_receiver_restore.lean','cpp_call_unit_frame.lean'])
        with tempfile.TemporaryDirectory(prefix='beats-receiver-cpp-') as directory:
            cpp = Path(directory)/'check.cpp'
            cpp.write_text(f'#include "{ROOT}/experiments/library/cpp/template/small_template.hpp"\n'
                f'#include "{ROOT}/experiments/verification/segment_tree_beats_wide.hpp"\n'
                '#include <cassert>\nint main(){std::vector<long long> a{4,5,6};cp::SegmentTreeBeats t(a);'
                'assert(t.calc_max(1,3)==6);assert(t.calc_min(1,3)==5);'
                't.chmin(0,3,5);assert(t.calc_max(0,3)==5);'
                't.chmax(0,2,6);assert(t.calc_min(0,3)==5);'
                't.add_val(1,3,2);assert(t.calc_max(0,3)==8);'
                't.update_val(0,2,3);assert(t.calc_min(0,3)==3);assert(t.calc_max(0,3)==7);'
                'assert(a==std::vector<long long>({4,5,6}));}')
            binary = Path(directory)/'check'
            subprocess.run(['g++','-std=c++17','-O1','-fsanitize=undefined',
                            '-fno-sanitize-recover=all',str(cpp),'-o',str(binary)],check=True)
            subprocess.run([str(binary)],check=True)

    def test_closed_allocation_and_stage_resource_bounds(self):
        self.check_fixtures('BeatsAllocationResources',[
            'beats_allocation.lean','beats_allocation_resources.lean'])


if __name__=='__main__':
    disable_network()
    unittest.main()
