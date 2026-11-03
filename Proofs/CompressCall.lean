import Proofs.CompressPrepare
import Proofs.MultiVecCall

namespace Proofs.CompressCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.CompressExec Proofs.CompressPrepare
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN LInv stepsL)

set_option maxHeartbeats 4000000 in
/-- `cp::compress(x, unzip, cmp)` leaves the sorted distinct values of `x` in `unzip` and, in `cmp`, the position
of every `x[j]` in `unzip`. -/
theorem compress_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 : Nat} {m0 : Bool}
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
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (Yf : List Int),
      prepare caller Proofs.SortUtilInstance.compress_std_vector_long_long.parameters
        [.vectorReference s0,.vectorReference s1,.vectorReference s2] = some Sinit ∧
      Proofs.SortUtilInstance.compress_std_vector_long_long.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.vectorReference s2] = .finished (res,Ret.unit) ∧
      (zipped X).Pairwise (fun a b => a < b) ∧ (∀ x, x ∈ zipped X ↔ x ∈ X) ∧ (zipped X).length ≤ n ∧
      Yf.length = n ∧ (∀ j, j < n → ∃ q : Nat, Yf[j]? = some (q : Int) ∧ (zipped X)[q]? = some (X.getD j 0)) ∧
      ScalarPostM (mvCm V0 V1 V2 vsc0 vsc1 vsc2 m0 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01 h02 h12)
        caller Sinit res 0 (costCmp n + 100) caller.scalars.memory
        (Proofs.StlContracts.sortComparisons n + 5 * n) (V3 X (zipped X) Yf) := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ := prepare_cmp caller ok0 ok1 ok2
  have fwS := fwC_init caller ok0 ok1 ok2 h01 h02 h12 X U Y n hn hlX hlU hlY i0 i1 i2 bv0 bv1 bv2 l0 l1 l2 o0 o1 o2
  rw [← sFrame] at fwS
  obtain ⟨rr,Yf,hexec,hret,hrps,hrvv,hlYf,hjf,hcost,hneed,hwk⟩ :=
    body_execCmp (mvCm V0 V1 V2 vsc0 vsc1 vsc2 m0 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01 h02 h12) rfl rfl rfl rfl X U Y hX (callerP caller) n
      hlX hlU hlY hn (stepsL n + 2 * n + 3) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller, []⟩ : PS) = gS (callerP caller) [] := by simp [gS]
  have hpost := call_vecm_unit (mvCm V0 V1 V2 vsc0 vsc1 vsc2 m0 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01 h02 h12) (fun k => decide (k ≠ 0))
    (by intro k hk; have : k ≠ 0 := by simpa using hk
        simp [mvCm, this])
    caller Proofs.SortUtilInstance.compress_std_vector_long_long [.vectorReference s0,.vectorReference s1,.vectorReference s2] Sinit
    (callerP caller) []
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]) (by rw [takeM]) ok0.base (by rw [body_eqCmp]; decide) (stepsL n + 2 * n + 3) rr
    (by rw [hmk, body_eqCmp]; exact hexec) hret rfl (by omega) (by simp) 0 (costCmp n + 100) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  have hZs := zipped_spec X
  refine ⟨Sinit,fuel,res,Yf,hprep,hrun,hZs.1,hZs.2,?_,hlYf,?_,?_⟩
  · rw [← hlX]; exact zipped_length X
  · intro j hj
    obtain ⟨q, hq1, hq2, hq3⟩ := hjf j hj
    have hxj : X.getD j 0 ∈ X := by
      have : X.getD j 0 = X[j]'(by omega) := by simp [List.getD_eq_getElem?_getD, show j < X.length by omega]
      rw [this]; exact List.getElem_mem _
    exact ⟨q, hq1, lb_pos _ hZs.1 _ ((hZs.2 _).mpr hxj) q hq3⟩
  · have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
      rw [hrps]
      simp only [gS_mem, callerP, List.append_assoc]
      rw [List.take_append_of_le_length (by simp)]
      exact List.take_length
    rw [hs', hrvv] at post
    exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.CompressCall
