import Proofs.TreeHeightPrepare
import Proofs.TreeHeightExec
import Proofs.MultiVecCall

namespace Proofs.TreeHeightCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.TreeHeightPrepare Proofs.TreeHeightExec
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)

/-- The callee of `tree_height`: three `long long` vectors, the last one writable. -/
def mvTH (V0 V1 V2 vsc0 vsc1 vsc2 : Nat) (m0 m1 : Bool) (L0 T0 sc N : Nat) (h02 : V0 ≠ V2) (h12 : V1 ≠ V2) : MV where
  nv := 3
  ty := fun _ => s64
  wV := fun k => decide (k = 2)
  flag := fun k => if k = 0 then m0 else if k = 1 then m1 else true
  R := fun k => if k = 0 then V0 else if k = 1 then V1 else V2
  vsc := fun k => if k = 0 then vsc0 else if k = 1 then vsc1 else vsc2
  perm := by
    intro k hk
    have : k = 2 := by simpa using hk
    subst this
    simp
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk hw
    have : k = 2 := by simpa using hw
    subst this
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · simpa using h02
    · simpa using h12

def bbTH (b0 b1 b2 : Buffer Value) : Nat → Buffer Value := fun k => if k = 0 then b0 else if k = 1 then b1 else b2

theorem wr_bodyTH : WrM (fun k => decide (k = 2)) (bodyTH 3) = true := by decide

theorem cases3 (k : Nat) (hk : k < 3) : k = 0 ∨ k = 1 ∨ k = 2 := by omega

theorem fwTH_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 : Nat} {m0 m1 : Bool}
    {vbuf0 vbuf1 vbuf2 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller s64 s2 vb2 V2 vsc2 true true vbuf2) (h02 : V0 ≠ V2) (h12 : V1 ≠ V2)
    (D0 D1 H : List Int) (hD0 : D0.length < 2147483647) (hD1 : D1.length < 2147483647) (hH : H.length < 2147483647)
    (i0 : vbuf0.items = D0.map Value.integer) (i1 : vbuf1.items = D1.map Value.integer)
    (i2 : vbuf2.items = H.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (bv2 : vbuf2.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) :
    FWM (mvTH V0 V1 V2 vsc0 vsc1 vsc2 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h02 h12)
      (VH D0 D1 H) (bbTH vbuf0 vbuf1 vbuf2) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer s64,false,.root vsc0⟩,⟨V1,.integer s64,false,.root vsc1⟩,⟨V2,.integer s64,true,.root vsc2⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvTH] using ok0.vtag
    · simpa [mvTH] using ok1.vtag
    · simpa [mvTH] using ok2.vtag
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvTH, bbTH] using ok0.vfound
    · simpa [mvTH, bbTH] using ok1.vfound
    · simpa [mvTH, bbTH] using ok2.vfound
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvTH] using ok0.flag
    · simpa [mvTH] using ok1.flag
    · simpa [mvTH] using ok2.flag
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvTH, bbTH, VH] using i0
    · simpa [mvTH, bbTH, VH] using i1
    · simpa [mvTH, bbTH, VH] using i2
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvTH, bbTH] using bv0
    · simpa [mvTH, bbTH] using bv1
    · simpa [mvTH, bbTH] using bv2
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvTH, bbTH] using l0
    · simpa [mvTH, bbTH] using l1
    · simpa [mvTH, bbTH] using l2
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvTH, bbTH] using o0
    · simpa [mvTH, bbTH] using o1
    · simpa [mvTH, bbTH] using o2
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simp [VH]; omega
    · simp [VH]; omega
    · simp [VH]; omega

set_option maxHeartbeats 8000000 in
/-- `cp::tree_height<long long>(cost_depth0, cost_depth1, h, n)` sets `h[i] = max(cost_depth0[i], cost_depth1[i])` for
`i < n`. -/
theorem tree_height_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 : Nat} {m0 m1 : Bool}
    {vbuf0 vbuf1 vbuf2 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller s64 s2 vb2 V2 vsc2 true true vbuf2) (h02 : V0 ≠ V2) (h12 : V1 ≠ V2)
    (D0 D1 H : List Int) (n : Nat) (hn : n < 2147483647) (h0 : n ≤ D0.length) (h1 : n ≤ D1.length) (h2 : n ≤ H.length)
    (hD0 : D0.length < 2147483647) (hD1 : D1.length < 2147483647) (hH : H.length < 2147483647)
    (hv0 : ∀ x ∈ D0, s64.valid x = true) (hv1 : ∀ x ∈ D1, s64.valid x = true)
    (i0 : vbuf0.items = D0.map Value.integer) (i1 : vbuf1.items = D1.map Value.integer)
    (i2 : vbuf2.items = H.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (bv2 : vbuf2.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2)
    (e1 : NExpr) (hs1 : e1.scalarOnly = true) (ty1 : e1.resultType = i32) (value1 : e1.denote (envOf caller) = some (n : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.TreeHeightInstance.tree_height_std_vector_long_long.parameters
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.value e1] = some Sinit ∧
      Proofs.TreeHeightInstance.tree_height_std_vector_long_long.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.value e1] = .finished (res,Ret.unit) ∧
      ScalarPostM (mvTH V0 V1 V2 vsc0 vsc1 vsc2 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h02 h12)
        caller Sinit res e1.nodes (120 * n + 200) caller.scalars.memory n (VH D0 D1 (hfill D0 D1 H n)) := by
  have hn32 : n < 2147483648 := by omega
  obtain ⟨t1,g1,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    prepare_th caller ok0 ok1 ok2 e1 (n : Int) hs1 ty1 value1 (validN n hn32)
  have fwS := fwTH_init caller ok0 ok1 ok2 h02 h12 D0 D1 H hD0 hD1 hH i0 i1 i2 bv0 bv1 bv2 l0 l1 l2 o0 o1 o2
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrps,hrvv,hcost,hneed,hwk⟩ :=
    body_exec (mvTH V0 V1 V2 vsc0 vsc1 vsc2 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length h02 h12) rfl rfl rfl rfl D0 D1 H (callerP caller) n
    hn32 hn h0 h1 h2 hv0 hv1 (n + 1) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)], [⟨(callerP caller).length,true⟩]⟩ : PS) =
      gS (callerP caller) [ci n] := by
    simp [gS]
  have gw := g1.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw
  have hpost := call_vecm_unit (mvTH V0 V1 V2 vsc0 vsc1 vsc2 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length h02 h12) (fun k => decide (k = 2))
    (by intro k hk; have : k = 2 := by simpa using hk
        subst this; simp [mvTH])
    caller Proofs.TreeHeightInstance.tree_height_std_vector_long_long
    [.vectorReference s0,.vectorReference s1,.vectorReference s2,.value e1] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)]) [⟨(callerP caller).length,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [body_eqTH]; exact wr_bodyTH)
    (n + 1) rr (by rw [hmk, body_eqTH]; exact hexec) hret rfl (by omega) (by simp [hlenP]) e1.nodes (120 * n + 200) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.TreeHeightCall
