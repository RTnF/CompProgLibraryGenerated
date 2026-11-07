namespace CopyReturnSamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine
theorem RangeSet_new0_v_explicit : (pexec 1 OriginalSetSum.RangeSet_new0_v.body (⟨[⟨⟨64,true,false⟩,3⟩],[⟨0,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (3)) := by
  simp only [OriginalSetSum.RangeSet_new0_v,pexec]
  decide +kernel
theorem RangeSet_new1_v_default : (pexec 1 OriginalSetSum.RangeSet_new1_v.body (⟨[],[]⟩ : PS)).map (fun r => r.ret) = some (some (0)) := by
  simp only [OriginalSetSum.RangeSet_new1_v,pexec]
  decide +kernel
theorem RangeSet_id_v_identity : (pexec 1 OriginalSetSum.RangeSet_id_v.body (⟨[],[]⟩ : PS)).map (fun r => r.ret) = some (some (0)) := by
  simp only [OriginalSetSum.RangeSet_id_v,pexec]
  decide +kernel
theorem RangeSet_compose_v_compose_00 : (pexec 1 OriginalSetSum.RangeSet_compose_v.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,0⟩,⟨⟨64,true,false⟩,2⟩,⟨⟨1,false,true⟩,0⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (3)) := by
  simp only [OriginalSetSum.RangeSet_compose_v,pexec]
  decide +kernel
theorem RangeSet_compose_v_compose_01 : (pexec 1 OriginalSetSum.RangeSet_compose_v.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,0⟩,⟨⟨64,true,false⟩,2⟩,⟨⟨1,false,true⟩,1⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (3)) := by
  simp only [OriginalSetSum.RangeSet_compose_v,pexec]
  decide +kernel
theorem RangeSet_compose_v_compose_10 : (pexec 1 OriginalSetSum.RangeSet_compose_v.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,1⟩,⟨⟨64,true,false⟩,2⟩,⟨⟨1,false,true⟩,0⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (2)) := by
  simp only [OriginalSetSum.RangeSet_compose_v,pexec]
  decide +kernel
theorem RangeSet_compose_v_compose_11 : (pexec 1 OriginalSetSum.RangeSet_compose_v.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,1⟩,⟨⟨64,true,false⟩,2⟩,⟨⟨1,false,true⟩,1⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (2)) := by
  simp only [OriginalSetSum.RangeSet_compose_v,pexec]
  decide +kernel
theorem RangeSet_new0_noop_explicit : (pexec 1 OriginalSetSum.RangeSet_new0_noop.body (⟨[⟨⟨64,true,false⟩,3⟩],[⟨0,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (0)) := by
  simp only [OriginalSetSum.RangeSet_new0_noop,pexec]
  decide +kernel
theorem RangeSet_new1_noop_default : (pexec 1 OriginalSetSum.RangeSet_new1_noop.body (⟨[],[]⟩ : PS)).map (fun r => r.ret) = some (some (1)) := by
  simp only [OriginalSetSum.RangeSet_new1_noop,pexec]
  decide +kernel
theorem RangeSet_id_noop_identity : (pexec 1 OriginalSetSum.RangeSet_id_noop.body (⟨[],[]⟩ : PS)).map (fun r => r.ret) = some (some (1)) := by
  simp only [OriginalSetSum.RangeSet_id_noop,pexec]
  decide +kernel
theorem RangeSet_compose_noop_compose_00 : (pexec 1 OriginalSetSum.RangeSet_compose_noop.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,0⟩,⟨⟨64,true,false⟩,2⟩,⟨⟨1,false,true⟩,0⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (0)) := by
  simp only [OriginalSetSum.RangeSet_compose_noop,pexec]
  decide +kernel
theorem RangeSet_compose_noop_compose_01 : (pexec 1 OriginalSetSum.RangeSet_compose_noop.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,0⟩,⟨⟨64,true,false⟩,2⟩,⟨⟨1,false,true⟩,1⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (0)) := by
  simp only [OriginalSetSum.RangeSet_compose_noop,pexec]
  decide +kernel
theorem RangeSet_compose_noop_compose_10 : (pexec 1 OriginalSetSum.RangeSet_compose_noop.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,1⟩,⟨⟨64,true,false⟩,2⟩,⟨⟨1,false,true⟩,0⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (0)) := by
  simp only [OriginalSetSum.RangeSet_compose_noop,pexec]
  decide +kernel
theorem RangeSet_compose_noop_compose_11 : (pexec 1 OriginalSetSum.RangeSet_compose_noop.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,1⟩,⟨⟨64,true,false⟩,2⟩,⟨⟨1,false,true⟩,1⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (1)) := by
  simp only [OriginalSetSum.RangeSet_compose_noop,pexec]
  decide +kernel
theorem RangeSet_apply_x_apply_0_4 : (pexec 1 OriginalSetSum.RangeSet_apply_x.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,0⟩,⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,4⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (12)) := by
  simp only [OriginalSetSum.RangeSet_apply_x,pexec]
  decide +kernel
theorem RangeSet_apply_x_apply_0_neg4 : (pexec 1 OriginalSetSum.RangeSet_apply_x.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,0⟩,⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,-4⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (-12)) := by
  simp only [OriginalSetSum.RangeSet_apply_x,pexec]
  decide +kernel
theorem RangeSet_apply_x_apply_0_0 : (pexec 1 OriginalSetSum.RangeSet_apply_x.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,0⟩,⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,0⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (0)) := by
  simp only [OriginalSetSum.RangeSet_apply_x,pexec]
  decide +kernel
theorem RangeSet_apply_x_apply_1_4 : (pexec 1 OriginalSetSum.RangeSet_apply_x.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,1⟩,⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,4⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (7)) := by
  simp only [OriginalSetSum.RangeSet_apply_x,pexec]
  decide +kernel
theorem RangeSet_apply_x_apply_1_neg4 : (pexec 1 OriginalSetSum.RangeSet_apply_x.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,1⟩,⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,-4⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (7)) := by
  simp only [OriginalSetSum.RangeSet_apply_x,pexec]
  decide +kernel
theorem RangeSet_apply_x_apply_1_0 : (pexec 1 OriginalSetSum.RangeSet_apply_x.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,1⟩,⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,0⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (7)) := by
  simp only [OriginalSetSum.RangeSet_apply_x,pexec]
  decide +kernel
theorem RangeSet_apply_x_noop_skips_overflow : (pexec 1 OriginalSetSum.RangeSet_apply_x.body (⟨[⟨⟨64,true,false⟩,9223372036854775807⟩,⟨⟨1,false,true⟩,1⟩,⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,4⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (7)) := by
  simp only [OriginalSetSum.RangeSet_apply_x,pexec]
  decide +kernel
theorem RangeSet_apply_x_overflow_rejected : (pexec 1 OriginalSetSum.RangeSet_apply_x.body (⟨[⟨⟨64,true,false⟩,9223372036854775807⟩,⟨⟨1,false,true⟩,0⟩,⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,2⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = none := by
  simp only [OriginalSetSum.RangeSet_apply_x,pexec]
  decide +kernel
theorem RangeSum_new0_x_explicit : (pexec 1 OriginalSetSum.RangeSum_new0_x.body (⟨[⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,-4⟩],[⟨0,true⟩,⟨1,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (7)) := by
  simp only [OriginalSetSum.RangeSum_new0_x,pexec]
  decide +kernel
theorem RangeSum_new1_x_default : (pexec 1 OriginalSetSum.RangeSum_new1_x.body (⟨[],[]⟩ : PS)).map (fun r => r.ret) = some (some (0)) := by
  simp only [OriginalSetSum.RangeSum_new1_x,pexec]
  decide +kernel
theorem RangeSum_e_x_identity : (pexec 1 OriginalSetSum.RangeSum_e_x.body (⟨[],[]⟩ : PS)).map (fun r => r.ret) = some (some (0)) := by
  simp only [OriginalSetSum.RangeSum_e_x,pexec]
  decide +kernel
theorem RangeSum_op_x_combine : (pexec 1 OriginalSetSum.RangeSum_op_x.body (⟨[⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,4⟩,⟨⟨64,true,false⟩,2⟩,⟨⟨32,true,false⟩,-1⟩],[⟨0,false⟩,⟨1,false⟩,⟨2,false⟩,⟨3,false⟩]⟩ : PS)).map (fun r => r.ret) = some (some (9)) := by
  simp only [OriginalSetSum.RangeSum_op_x,pexec]
  decide +kernel
theorem RangeSet_apply_size_apply_0_4 : (pexec 1 OriginalSetSum.RangeSet_apply_size.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,0⟩,⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,4⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (4)) := by
  simp only [OriginalSetSum.RangeSet_apply_size,pexec]
  decide +kernel
theorem RangeSet_apply_size_apply_0_neg4 : (pexec 1 OriginalSetSum.RangeSet_apply_size.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,0⟩,⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,-4⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (-4)) := by
  simp only [OriginalSetSum.RangeSet_apply_size,pexec]
  decide +kernel
theorem RangeSet_apply_size_apply_0_0 : (pexec 1 OriginalSetSum.RangeSet_apply_size.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,0⟩,⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,0⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (0)) := by
  simp only [OriginalSetSum.RangeSet_apply_size,pexec]
  decide +kernel
theorem RangeSet_apply_size_apply_1_4 : (pexec 1 OriginalSetSum.RangeSet_apply_size.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,1⟩,⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,4⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (4)) := by
  simp only [OriginalSetSum.RangeSet_apply_size,pexec]
  decide +kernel
theorem RangeSet_apply_size_apply_1_neg4 : (pexec 1 OriginalSetSum.RangeSet_apply_size.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,1⟩,⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,-4⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (-4)) := by
  simp only [OriginalSetSum.RangeSet_apply_size,pexec]
  decide +kernel
theorem RangeSet_apply_size_apply_1_0 : (pexec 1 OriginalSetSum.RangeSet_apply_size.body (⟨[⟨⟨64,true,false⟩,3⟩,⟨⟨1,false,true⟩,1⟩,⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,0⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (0)) := by
  simp only [OriginalSetSum.RangeSet_apply_size,pexec]
  decide +kernel
theorem RangeSet_apply_size_noop_skips_overflow : (pexec 1 OriginalSetSum.RangeSet_apply_size.body (⟨[⟨⟨64,true,false⟩,9223372036854775807⟩,⟨⟨1,false,true⟩,1⟩,⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,4⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (4)) := by
  simp only [OriginalSetSum.RangeSet_apply_size,pexec]
  decide +kernel
theorem RangeSet_apply_size_overflow_rejected : (pexec 1 OriginalSetSum.RangeSet_apply_size.body (⟨[⟨⟨64,true,false⟩,9223372036854775807⟩,⟨⟨1,false,true⟩,0⟩,⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,2⟩],[⟨0,true⟩,⟨1,true⟩,⟨2,true⟩,⟨3,true⟩]⟩ : PS)).map (fun r => r.ret) = none := by
  simp only [OriginalSetSum.RangeSet_apply_size,pexec]
  decide +kernel
theorem RangeSum_new0_size_explicit : (pexec 1 OriginalSetSum.RangeSum_new0_size.body (⟨[⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,-4⟩],[⟨0,true⟩,⟨1,true⟩]⟩ : PS)).map (fun r => r.ret) = some (some (-4)) := by
  simp only [OriginalSetSum.RangeSum_new0_size,pexec]
  decide +kernel
theorem RangeSum_new1_size_default : (pexec 1 OriginalSetSum.RangeSum_new1_size.body (⟨[],[]⟩ : PS)).map (fun r => r.ret) = some (some (0)) := by
  simp only [OriginalSetSum.RangeSum_new1_size,pexec]
  decide +kernel
theorem RangeSum_e_size_identity : (pexec 1 OriginalSetSum.RangeSum_e_size.body (⟨[],[]⟩ : PS)).map (fun r => r.ret) = some (some (0)) := by
  simp only [OriginalSetSum.RangeSum_e_size,pexec]
  decide +kernel
theorem RangeSum_op_size_combine : (pexec 1 OriginalSetSum.RangeSum_op_size.body (⟨[⟨⟨64,true,false⟩,7⟩,⟨⟨32,true,false⟩,4⟩,⟨⟨64,true,false⟩,2⟩,⟨⟨32,true,false⟩,-1⟩],[⟨0,false⟩,⟨1,false⟩,⟨2,false⟩,⟨3,false⟩]⟩ : PS)).map (fun r => r.ret) = some (some (3)) := by
  simp only [OriginalSetSum.RangeSum_op_size,pexec]
  decide +kernel
end CopyReturnSamples
