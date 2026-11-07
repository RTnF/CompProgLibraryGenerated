namespace SetSumTransferred
open StrictMixedBodyAudit
open Proofs
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch
open Proofs.ExtremaCall
open Proofs.CppState (Cell)

open Proofs.GroupCall


open Proofs.MonoidLazyCall Proofs.MonoidCall

theorem e_program (second : Bool) :
  (if second then OriginalSetSum.RangeSum_e_size else OriginalSetSum.RangeSum_e_x) =
  (if second then OriginalMixedAddSum.RangeSum_e_size else OriginalMixedAddSum.RangeSum_e_x) := by cases second <;> rfl

theorem e_correct (second : Bool) (caller : NState)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    let prog := if second then OriginalSetSum.RangeSum_e_size else OriginalSetSum.RangeSum_e_x
    ∃ Sinit fuel res, prepare caller prog.parameters [] = some Sinit ∧
      prog.callFuel fuel caller [] = .finished (res,.scalar 0) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  simpa only [e_program] using StrictMixedBodyAudit.e_correct second caller valid lengths strict base

theorem new1_program (second : Bool) :
  (if second then OriginalSetSum.RangeSum_new1_size else OriginalSetSum.RangeSum_new1_x) =
  (if second then OriginalMixedAddSum.RangeSum_new1_size else OriginalMixedAddSum.RangeSum_new1_x) := by cases second <;> rfl

theorem default_correct (second : Bool) (caller : NState)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    let prog := if second then OriginalSetSum.RangeSum_new1_size else OriginalSetSum.RangeSum_new1_x
    ∃ Sinit fuel res, prepare caller prog.parameters [] = some Sinit ∧
      prog.callFuel fuel caller [] = .finished (res,.scalar 0) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  simpa only [new1_program] using StrictMixedBodyAudit.default_correct second caller valid lengths strict base

theorem new0_program (second : Bool) :
  (if second then OriginalSetSum.RangeSum_new0_size else OriginalSetSum.RangeSum_new0_x) =
  (if second then OriginalMixedAddSum.RangeSum_new0_size else OriginalMixedAddSum.RangeSum_new0_x) := by cases second <;> rfl

theorem new_correct (second : Bool) (caller : NState) (e1 e2 : NExpr) (x sz : Int)
    (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true)
    (ht1 : e1.resultType = s64) (ht2 : e2.resultType = i32)
    (d1 : e1.denote (envOf caller) = some x) (d2 : e2.denote (envOf caller) = some sz)
    (hx : s64.valid x = true) (hz : i32.valid sz = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    let prog := if second then OriginalSetSum.RangeSum_new0_size else OriginalSetSum.RangeSum_new0_x
    ∃ Sinit fuel res, prepare caller prog.parameters [.value e1,.value e2] = some Sinit ∧
      prog.callFuel fuel caller [.value e1,.value e2] = .finished (res,.scalar (if second then sz else x)) ∧
      ScalarPost2 caller Sinit res (e1.nodes+e2.nodes) 70 caller.scalars.memory := by
  simpa only [new0_program] using StrictMixedBodyAudit.new_correct second caller e1 e2 x sz hs1 hs2 ht1 ht2 d1 d2 hx hz valid lengths strict base

theorem op_program (second : Bool) :
  (if second then OriginalSetSum.RangeSum_op_size else OriginalSetSum.RangeSum_op_x) =
  (if second then OriginalMixedAddSum.RangeSum_op_size else OriginalMixedAddSum.RangeSum_op_x) := by cases second <;> rfl

theorem op_correct (second : Bool) (caller : NState) (s1 s2 s3 s4 : Nat)
    (b1 b2 b3 b4 : CppState.Binding) (v1 v2 v3 v4 : Int)
    (c1 : caller.scalarCell s1 s64 = some (b1,⟨s64,v1⟩)) (c2 : caller.scalarCell s2 i32 = some (b2,⟨i32,v2⟩))
    (c3 : caller.scalarCell s3 s64 = some (b3,⟨s64,v3⟩)) (c4 : caller.scalarCell s4 i32 = some (b4,⟨i32,v4⟩))
    (g1 : s64.valid v1 = true) (g2 : i32.valid v2 = true)
    (g3 : s64.valid v3 = true) (g4 : i32.valid v4 = true)
    (gx : s64.valid (v1+v3) = true) (gz : i32.valid (v2+v4) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    let prog := if second then OriginalSetSum.RangeSum_op_size else OriginalSetSum.RangeSum_op_x
    ∃ Sinit fuel res, prepare caller prog.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference s1,.scalarReference s2,.scalarReference s3,.scalarReference s4] =
        .finished (res,.scalar (if second then v2+v4 else v1+v3)) ∧
      ScalarPost2 caller Sinit res 0 80 caller.scalars.memory := by
  simpa only [op_program] using StrictMixedBodyAudit.op_correct second caller s1 s2 s3 s4 b1 b2 b3 b4 v1 v2 v3 v4 c1 c2 c3 c4 g1 g2 g3 g4 gx gz valid lengths strict base

open CopiedScalarFieldsAudit

theorem set_default_correct (second : Bool) (caller : NState)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    let prog := if second then OriginalSetSum.RangeSet_new1_noop else OriginalSetSum.RangeSet_new1_v
    ∃ Sinit fuel res, prepare caller prog.parameters [] = some Sinit ∧
      prog.callFuel fuel caller [] = .finished (res,.scalar (if second then 1 else 0)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  let prog := if second then OriginalSetSum.RangeSet_new1_noop else OriginalSetSum.RangeSet_new1_v
  refine constant_body_correct prog (if second then bl else s64) (if second then 1 else 0)
    (by cases second <;> rfl) (by cases second <;> rfl) (by cases second <;> decide)
    (by cases second <;> decide) caller valid lengths strict base ?_
  intro P hP
  subst hP
  obtain ⟨r,ran,ret,cost,need,ps⟩ := copy_exec (callerP caller) [] s64 bl
    zero64 (.literal bl 1) 0 1 second rfl rfl rfl rfl
  have body : prog.body = copyBody 0 s64 bl zero64 (.literal bl 1) second := by cases second <;> rfl
  refine ⟨r,?_,ret,?_,?_,?_⟩
  · rw [body]; simpa only [ws_nil,List.length_nil] using ran
  · simp [NExpr.nodes] at cost
    omega
  · simp [NExpr.nodes] at need
    omega
  · rw [ps]
    exact take_P caller _

theorem set_id_program (second : Bool) :
    (if second then OriginalSetSum.RangeSet_id_noop else OriginalSetSum.RangeSet_id_v) =
    (if second then OriginalSetSum.RangeSet_new1_noop else OriginalSetSum.RangeSet_new1_v) := by cases second <;> rfl

theorem set_id_correct (second : Bool) (caller : NState)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    let prog := if second then OriginalSetSum.RangeSet_id_noop else OriginalSetSum.RangeSet_id_v
    ∃ Sinit fuel res, prepare caller prog.parameters [] = some Sinit ∧
      prog.callFuel fuel caller [] = .finished (res,.scalar (if second then 1 else 0)) ∧
      ScalarPost2 caller Sinit res 0 70 caller.scalars.memory := by
  simpa only [set_id_program] using set_default_correct second caller valid lengths strict base

end SetSumTransferred
