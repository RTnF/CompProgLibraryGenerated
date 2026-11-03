import Proofs.RunLengthExec
import Proofs.CompressPrepare
import Proofs.Generated.RunLength

namespace Proofs.RunLengthCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.CompressExec Proofs.CompressPrepare Proofs.RunLengthExec
open Proofs.RunLengthMath
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)

theorem body_eqRL : Proofs.RunLengthInstance.run_length_std_vector_long_long.body = bodyRL 3 := rfl

theorem wr_bodyRL : WrM (fun k => decide (k ≠ 0)) (bodyRL 3) = true := by decide

set_option maxHeartbeats 4000000 in
/-- `cp::run_length(v, values, counts)` stores the maximal runs of `v` in `values` and `counts` and returns their number. -/
theorem run_length_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 : Nat} {m0 : Bool}
    {vbuf0 vbuf1 vbuf2 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 true true vbuf2) (h01 : V0 ≠ V1) (h02 : V0 ≠ V2) (h12 : V1 ≠ V2)
    (X U Y : List Int) (hX : ∀ x ∈ X, s64.valid x = true) (n : Nat) (hn : n < 2147483647)
    (hlX : X.length = n) (hlU : U.length = n) (hlY : Y.length = n)
    (i0 : vbuf0.items = X.map Value.integer) (i1 : vbuf1.items = U.map Value.integer)
    (i2 : vbuf2.items = Y.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (bv2 : vbuf2.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (U' Y' : List Int),
      prepare caller Proofs.RunLengthInstance.run_length_std_vector_long_long.parameters
        [.vectorReference s0,.vectorReference s1,.vectorReference s2] = some Sinit ∧
      Proofs.RunLengthInstance.run_length_std_vector_long_long.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.vectorReference s2] = .finished (res,.scalar (((rle X).length : Nat) : Int)) ∧
      (rle X).length ≤ n ∧ U'.length = n ∧ Y'.length = n ∧ pairsOf U' Y' (rle X).length = rle X ∧
      rleFlat (rle X) = X ∧ (∀ p ∈ rle X, 0 < p.2) ∧ AdjOK (rle X) ∧
      ScalarPostM (mvCm V0 V1 V2 vsc0 vsc1 vsc2 m0 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01 h02 h12)
        caller Sinit res 0 (420 * n + 300) caller.scalars.memory (2 * n + 2) (V3 X U' Y') := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_vvv caller Proofs.RunLengthInstance.run_length_std_vector_long_long rfl ok0 ok1 ok2
  have fwS := fwC_init caller ok0 ok1 ok2 h01 h02 h12 X U Y n hn hlX hlU hlY i0 i1 i2 bv0 bv1 bv2 l0 l1 l2 o0 o1 o2
  rw [← sFrame] at fwS
  obtain ⟨rr,U',Y',hexec,hret,⟨cs,hrps⟩,hrvv,hlU',hlY',hpairs,hcost,hneed,hwk⟩ :=
    body_execRL (mvCm V0 V1 V2 vsc0 vsc1 vsc2 m0 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01 h02 h12) rfl rfl rfl rfl X U Y hX (callerP caller) n
      hlX hlU hlY hn (n + 2) (Nat.le_refl _)
  have hle : (rle X).length ≤ n := by rw [← hlX]; exact rle_length_le X
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller, []⟩ : PS) = gS (callerP caller) [] := by simp [gS]
  have hpost := call_vecm (mvCm V0 V1 V2 vsc0 vsc1 vsc2 m0 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01 h02 h12) (fun k => decide (k ≠ 0))
    (by intro k hk; have : k ≠ 0 := by simpa using hk
        simp [mvCm, this])
    caller Proofs.RunLengthInstance.run_length_std_vector_long_long [.vectorReference s0,.vectorReference s1,.vectorReference s2] Sinit
    (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]) (by rw [takeM]) ok0.base (by rw [body_eqRL]; exact wr_bodyRL) (n + 2) rr
    (by rw [hmk, body_eqRL]; exact hexec) (((rle X).length : Nat) : Int) hret i32 rfl (validN _ (by omega))
    (by omega) (by simp) 0 (420 * n + 300) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  obtain ⟨hs1, hs2, hs3⟩ := rle_spec X
  refine ⟨Sinit,fuel,res,U',Y',hprep,hrun,hle,hlU',hlY',hpairs,hs1,hs2,hs3,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.RunLengthCall
