import Proofs.MatPowPrepare
import Proofs.MatPowExec
import Proofs.MultiVecCallB

namespace Proofs.MatPowCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCallB
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.MatPowPrepare
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (cs)
open Proofs.MatPowBody Proofs.MatPowExec
open Proofs.MatMulExec (M64 u64v cu)

def sel4 {α : Type} (a0 a1 a2 a3 : α) : Nat → α := fun k =>
  if k = 0 then a0 else if k = 1 then a1 else if k = 2 then a2 else a3

theorem cases4 (k : Nat) (hk : k < 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega

/-- The callee of `mat_pow`: `a` (read-only) and `r`, `y`, `t` (writable), all `unsigned long long` vectors. -/
def mvMP (V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 : Nat) (m0 : Bool) (L0 T0 sc N : Nat)
    (hd : ∀ j k, j < 4 → k < 4 → j ≠ k → 1 ≤ k → sel4 V0 V1 V2 V3 j ≠ sel4 V0 V1 V2 V3 k) : MV where
  nv := 4
  ty := fun _ => u64
  wV := fun k => decide (1 ≤ k)
  flag := fun k => if k = 0 then m0 else true
  R := sel4 V0 V1 V2 V3
  vsc := sel4 vsc0 vsc1 vsc2 vsc3
  perm := by
    intro k hk
    have : 1 ≤ k := by simpa using hk
    simp [show k ≠ 0 by omega]
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk hw
    exact hd j k hj hk hjk (by simpa using hw)

def bbMP (b0 b1 b2 b3 : Buffer Value) : Nat → Buffer Value := sel4 b0 b1 b2 b3

theorem body_eqMP4 : Proofs.SquareMatrixInstance.mat_pow_std_vector_unsigned_long_long.body = bodyPow 4 := rfl

theorem wr_bodyMP : WrM (fun k => decide (1 ≤ k)) (bodyPow 4) = true := by decide


theorem fwMP_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 : Nat} {m0 : Bool}
    {vbuf0 vbuf1 vbuf2 vbuf3 : Buffer Value}
    (ok0 : VOKG caller u64 s0 vb0 V0 vsc0 false m0 vbuf0)
    (ok1 : VOKG caller u64 s1 vb1 V1 vsc1 true true vbuf1)
    (ok2 : VOKG caller u64 s2 vb2 V2 vsc2 true true vbuf2)
    (ok3 : VOKG caller u64 s3 vb3 V3 vsc3 true true vbuf3)
    (hdist : ∀ j k, j < 4 → k < 4 → j ≠ k → 1 ≤ k → sel4 V0 V1 V2 V3 j ≠ sel4 V0 V1 V2 V3 k)
    (a r0 y0 t0 : List Nat)
    (hs : a.length < 2147483647 ∧ r0.length < 2147483647 ∧ y0.length < 2147483647 ∧ t0.length < 2147483647)
    (i0 : vbuf0.items = (a.map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = (r0.map (fun x : Nat => (x : Int))).map Value.integer)
    (i2 : vbuf2.items = (y0.map (fun x : Nat => (x : Int))).map Value.integer)
    (i3 : vbuf3.items = (t0.map (fun x : Nat => (x : Int))).map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer u64)))
    (bv1 : vbuf1.Valid (accepts (.integer u64)))
    (bv2 : vbuf2.Valid (accepts (.integer u64)))
    (bv3 : vbuf3.Valid (accepts (.integer u64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit u64)
    (l1 : vbuf1.limit = CppVectorBindings.sizeLimit u64)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit u64)
    (l3 : vbuf3.limit = CppVectorBindings.sizeLimit u64)
    (o0 : vbuf0.owner = V0)
    (o1 : vbuf1.owner = V1)
    (o2 : vbuf2.owner = V2)
    (o3 : vbuf3.owner = V3)
    :
    FWM (mvMP V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 m0 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length hdist)
      (VP a r0 y0 t0) (bbMP vbuf0 vbuf1 vbuf2 vbuf3) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer u64,false,.root vsc0⟩,
         ⟨V1,.integer u64,true,.root vsc1⟩,
         ⟨V2,.integer u64,true,.root vsc2⟩,
         ⟨V3,.integer u64,true,.root vsc3⟩]⟩ : Frame) := by
  obtain ⟨s0l, s1l, s2l, s3l⟩ := hs
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl <;> first | simpa [mvMP, bbMP, VP, sel4] using ok0.vtag | simpa [mvMP, bbMP, VP, sel4] using ok1.vtag | simpa [mvMP, bbMP, VP, sel4] using ok2.vtag | simpa [mvMP, bbMP, VP, sel4] using ok3.vtag
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl <;> first | simpa [mvMP, bbMP, VP, sel4] using ok0.vfound | simpa [mvMP, bbMP, VP, sel4] using ok1.vfound | simpa [mvMP, bbMP, VP, sel4] using ok2.vfound | simpa [mvMP, bbMP, VP, sel4] using ok3.vfound
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl <;> first | simpa [mvMP, bbMP, VP, sel4] using ok0.flag | simpa [mvMP, bbMP, VP, sel4] using ok1.flag | simpa [mvMP, bbMP, VP, sel4] using ok2.flag | simpa [mvMP, bbMP, VP, sel4] using ok3.flag
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl <;> first | simpa [mvMP, bbMP, VP, sel4] using i0 | simpa [mvMP, bbMP, VP, sel4] using i1 | simpa [mvMP, bbMP, VP, sel4] using i2 | simpa [mvMP, bbMP, VP, sel4] using i3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl <;> first | simpa [mvMP, bbMP, sel4] using bv0 | simpa [mvMP, bbMP, sel4] using bv1 | simpa [mvMP, bbMP, sel4] using bv2 | simpa [mvMP, bbMP, sel4] using bv3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl <;> first | simpa [mvMP, bbMP, sel4] using l0 | simpa [mvMP, bbMP, sel4] using l1 | simpa [mvMP, bbMP, sel4] using l2 | simpa [mvMP, bbMP, sel4] using l3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl <;> first | simpa [mvMP, bbMP, sel4] using o0 | simpa [mvMP, bbMP, sel4] using o1 | simpa [mvMP, bbMP, sel4] using o2 | simpa [mvMP, bbMP, sel4] using o3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl <;> simp [VP, mvMP, sel4] <;> omega

set_option maxHeartbeats 16000000 in
/-- `cp::mat_pow(a, r, y, t, n, e)`: `r = a^e` (the vectors `y`, `t` are scratch). -/
theorem mat_pow_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 : Nat} {m0 : Bool}
    {vbuf0 vbuf1 vbuf2 vbuf3 : Buffer Value}
    (ok0 : VOKG caller u64 s0 vb0 V0 vsc0 false m0 vbuf0)
    (ok1 : VOKG caller u64 s1 vb1 V1 vsc1 true true vbuf1)
    (ok2 : VOKG caller u64 s2 vb2 V2 vsc2 true true vbuf2)
    (ok3 : VOKG caller u64 s3 vb3 V3 vsc3 true true vbuf3)
    (hdist : ∀ j k, j < 4 → k < 4 → j ≠ k → 1 ≤ k → sel4 V0 V1 V2 V3 j ≠ sel4 V0 V1 V2 V3 k)
    (a r0 y0 t0 : List Nat) (n e : Nat) (hnn : n * n < 2147483647) (he : e < M64) (hla : a.length = n * n)
    (hlr : r0.length = n * n) (hly : y0.length = n * n) (hlt : t0.length = n * n) (haM : ∀ x ∈ a, x < M64)
    (i0 : vbuf0.items = (a.map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = (r0.map (fun x : Nat => (x : Int))).map Value.integer)
    (i2 : vbuf2.items = (y0.map (fun x : Nat => (x : Int))).map Value.integer)
    (i3 : vbuf3.items = (t0.map (fun x : Nat => (x : Int))).map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer u64)))
    (bv1 : vbuf1.Valid (accepts (.integer u64)))
    (bv2 : vbuf2.Valid (accepts (.integer u64)))
    (bv3 : vbuf3.Valid (accepts (.integer u64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit u64)
    (l1 : vbuf1.limit = CppVectorBindings.sizeLimit u64)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit u64)
    (l3 : vbuf3.limit = CppVectorBindings.sizeLimit u64)
    (o0 : vbuf0.owner = V0)
    (o1 : vbuf1.owner = V1)
    (o2 : vbuf2.owner = V2)
    (o3 : vbuf3.owner = V3)
    (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (ty1 : e1.resultType = i32)
    (ty2 : e2.resultType = u64) (value1 : e1.denote (envOf caller) = some (n : Int))
    (value2 : e2.denote (envOf caller) = some (e : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (R Y T : List Nat),
      prepare caller Proofs.SquareMatrixInstance.mat_pow_std_vector_unsigned_long_long.parameters
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.value e1,.value e2] = some Sinit ∧
      Proofs.SquareMatrixInstance.mat_pow_std_vector_unsigned_long_long.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.value e1,.value e2] = .finished (res,Ret.unit) ∧
      R.length = n * n ∧ (∀ x ∈ R, x < M64) ∧
      (∀ i j, i < n → j < n → R.getD (i * n + j) 0 = Proofs.MatPowMath.PW n (toF n a) e i j) ∧
      ScalarPostMB 1000 (mvMP V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 m0 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length hdist)
        caller Sinit res (e1.nodes + e2.nodes) (CTOT n + 100) caller.scalars.memory
        (64 * (2 * (n * n + n * n)) + 3 * (n * n)) (VP a R Y T) := by
  have hn32 : n < 2147483648 := by
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_mp caller ok0 ok1 ok2 ok3 e1 e2 (n : Int) (e : Int) hs1 hs2 ty1 ty2 value1 value2 (validN n hn32) (u64v e he)
  have fwS := fwMP_init caller ok0 ok1 ok2 ok3 hdist a r0 y0 t0
    ⟨by omega, by omega, by omega, by omega⟩ i0 i1 i2 i3 bv0 bv1 bv2 bv3 l0 l1 l2 l3 o0 o1 o2 o3
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrps,hrvv,hcost,hneed,hwk⟩ :=
    body_pow (mvMP V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 m0 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length hdist) rfl (by simp [mvMP]) (callerP caller)
      (64 + (3 * n + 4 + n * n + 2)) a r0 y0 t0 n e hnn he hla hlr hly hlt haM (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),(⟨u64,(e : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),(⟨u64,(e : Int)⟩ : Cell)],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]⟩ : PS) = gS (callerP caller) [ci n, cu e] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2
  have hpost := call_vecm_unitB 1000 (mvMP V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 m0 caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length hdist)
    (fun k => decide (1 ≤ k))
    (by intro k hk; have : 1 ≤ k := by simpa using hk
        simp [mvMP, show k ≠ 0 by omega, this])
    caller Proofs.SquareMatrixInstance.mat_pow_std_vector_unsigned_long_long
    [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),(⟨u64,(e : Int)⟩ : Cell)])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [body_eqMP4]; exact wr_bodyMP)
    (64 + (3 * n + 4 + n * n + 2)) rr (by rw [hmk, body_eqMP4]; exact hexec) hret rfl (by omega)
    (by simp [hlenP]) (e1.nodes + e2.nodes) (CTOT n + 100) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  have hfin := pow_final n e hnn he a r0 t0 hla hlr hlt haM
  refine ⟨Sinit,fuel,res,(powRun n 64 (diagL (zeroL r0 (n * n)) n n, a, t0) e).1,
    (powRun n 64 (diagL (zeroL r0 (n * n)) n n, a, t0) e).2.1,(powRun n 64 (diagL (zeroL r0 (n * n)) n n, a, t0) e).2.2,
    hprep,hrun,hfin.1,hfin.2.1,hfin.2.2,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.MatPowCall
