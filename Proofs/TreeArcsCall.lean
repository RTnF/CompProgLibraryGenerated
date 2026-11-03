import Proofs.TreeArcsPrepare
import Proofs.TreeArcsExec
import Proofs.MultiVecCall

namespace Proofs.TreeArcsCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.TreeArcsPrepare Proofs.TreeArcsExec
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)

/-- The callee of `tree_arcs_from_list`: four `int` vectors, the last two writable. -/
def mvAR (V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 : Nat) (m0 m1 : Bool) (L0 T0 sc N : Nat) (h02 : V0 ≠ V2) (h03 : V0 ≠ V3)
    (h12 : V1 ≠ V2) (h13 : V1 ≠ V3) (h23 : V2 ≠ V3) : MV where
  nv := 4
  ty := fun _ => i32
  wV := fun k => decide (k = 2 ∨ k = 3)
  flag := fun k => if k = 0 then m0 else if k = 1 then m1 else true
  R := fun k => if k = 0 then V0 else if k = 1 then V1 else if k = 2 then V2 else V3
  vsc := fun k => if k = 0 then vsc0 else if k = 1 then vsc1 else if k = 2 then vsc2 else vsc3
  perm := by
    intro k hk
    have : k = 2 ∨ k = 3 := by simpa using hk
    rcases this with rfl | rfl <;> simp
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk hw
    have : k = 2 ∨ k = 3 := by simpa using hw
    rcases this with rfl | rfl
    · have : j = 0 ∨ j = 1 ∨ j = 3 := by omega
      rcases this with rfl | rfl | rfl
      · simpa using h02
      · simpa using h12
      · simpa using h23.symm
    · have : j = 0 ∨ j = 1 ∨ j = 2 := by omega
      rcases this with rfl | rfl | rfl
      · simpa using h03
      · simpa using h13
      · simpa using h23

def bbAR (b0 b1 b2 b3 : Buffer Value) : Nat → Buffer Value :=
  fun k => if k = 0 then b0 else if k = 1 then b1 else if k = 2 then b2 else b3

theorem wr_bodyAR : WrM (fun k => decide (k = 2 ∨ k = 3)) (bodyAR 4) = true := by decide

theorem cases4 (k : Nat) (hk : k < 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega

theorem fwAR_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 : Nat} {m0 m1 : Bool}
    {vbuf0 vbuf1 vbuf2 vbuf3 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 true true vbuf2) (ok3 : VOKG caller i32 s3 vb3 V3 vsc3 true true vbuf3)
    (h02 : V0 ≠ V2) (h03 : V0 ≠ V3) (h12 : V1 ≠ V2) (h13 : V1 ≠ V3) (h23 : V2 ≠ V3)
    (Fr To AF AT : List Int) (hFr : Fr.length < 2147483647) (hTo : To.length < 2147483647) (hAF : AF.length < 2147483647)
    (hAT : AT.length < 2147483647)
    (i0 : vbuf0.items = Fr.map Value.integer) (i1 : vbuf1.items = To.map Value.integer)
    (i2 : vbuf2.items = AF.map Value.integer) (i3 : vbuf3.items = AT.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (bv2 : vbuf2.Valid (accepts (.integer i32))) (bv3 : vbuf3.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32) (l3 : vbuf3.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) (o3 : vbuf3.owner = V3) :
    FWM (mvAR V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h02 h03 h12 h13 h23)
      (VA Fr To AF AT) (bbAR vbuf0 vbuf1 vbuf2 vbuf3) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer i32,false,.root vsc0⟩,⟨V1,.integer i32,false,.root vsc1⟩,⟨V2,.integer i32,true,.root vsc2⟩,
         ⟨V3,.integer i32,true,.root vsc3⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvAR] using ok0.vtag
    · simpa [mvAR] using ok1.vtag
    · simpa [mvAR] using ok2.vtag
    · simpa [mvAR] using ok3.vtag
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvAR, bbAR] using ok0.vfound
    · simpa [mvAR, bbAR] using ok1.vfound
    · simpa [mvAR, bbAR] using ok2.vfound
    · simpa [mvAR, bbAR] using ok3.vfound
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvAR] using ok0.flag
    · simpa [mvAR] using ok1.flag
    · simpa [mvAR] using ok2.flag
    · simpa [mvAR] using ok3.flag
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvAR, bbAR, VA] using i0
    · simpa [mvAR, bbAR, VA] using i1
    · simpa [mvAR, bbAR, VA] using i2
    · simpa [mvAR, bbAR, VA] using i3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvAR, bbAR] using bv0
    · simpa [mvAR, bbAR] using bv1
    · simpa [mvAR, bbAR] using bv2
    · simpa [mvAR, bbAR] using bv3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvAR, bbAR] using l0
    · simpa [mvAR, bbAR] using l1
    · simpa [mvAR, bbAR] using l2
    · simpa [mvAR, bbAR] using l3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvAR, bbAR] using o0
    · simpa [mvAR, bbAR] using o1
    · simpa [mvAR, bbAR] using o2
    · simpa [mvAR, bbAR] using o3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simp [VA]; omega
    · simp [VA]; omega
    · simp [VA]; omega
    · simp [VA]; omega

set_option maxHeartbeats 8000000 in
/-- `cp::tree_arcs_from_list(from, to, af, at, m)` writes the two arcs of every edge to the positions `2 * i`, `2 * i + 1`. -/
theorem tree_arcs_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 : Nat} {m0 m1 : Bool}
    {vbuf0 vbuf1 vbuf2 vbuf3 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 true true vbuf2) (ok3 : VOKG caller i32 s3 vb3 V3 vsc3 true true vbuf3)
    (h02 : V0 ≠ V2) (h03 : V0 ≠ V3) (h12 : V1 ≠ V2) (h13 : V1 ≠ V3) (h23 : V2 ≠ V3)
    (Fr To AF AT : List Int) (m : Nat) (hm : m < 536870912) (hF : m ≤ Fr.length) (hT : m ≤ To.length)
    (hAF : 2 * m ≤ AF.length) (hAT : 2 * m ≤ AT.length) (hFr : Fr.length < 2147483647) (hTo : To.length < 2147483647)
    (hAF2 : AF.length < 2147483647) (hAT2 : AT.length < 2147483647)
    (hFv : ∀ x ∈ Fr, i32.valid x = true) (hTv : ∀ x ∈ To, i32.valid x = true)
    (i0 : vbuf0.items = Fr.map Value.integer) (i1 : vbuf1.items = To.map Value.integer)
    (i2 : vbuf2.items = AF.map Value.integer) (i3 : vbuf3.items = AT.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (bv2 : vbuf2.Valid (accepts (.integer i32))) (bv3 : vbuf3.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32) (l3 : vbuf3.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) (o3 : vbuf3.owner = V3)
    (e1 : NExpr) (hs1 : e1.scalarOnly = true) (ty1 : e1.resultType = i32) (value1 : e1.denote (envOf caller) = some (m : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.TreeArcsInstance.tree_arcs_from_list.parameters
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.value e1] = some Sinit ∧
      Proofs.TreeArcsInstance.tree_arcs_from_list.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.value e1] = .finished (res,Ret.unit) ∧
      ScalarPostM (mvAR V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h02 h03 h12 h13 h23)
        caller Sinit res e1.nodes (320 * m + 200) caller.scalars.memory (4 * m)
        (VA Fr To (AFt Fr To AF m) (ATt Fr To AT m)) := by
  have hm32 : m < 2147483648 := by omega
  obtain ⟨t1,g1,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    prepare_ta caller ok0 ok1 ok2 ok3 e1 (m : Int) hs1 ty1 value1 (validN m hm32)
  have fwS := fwAR_init caller ok0 ok1 ok2 ok3 h02 h03 h12 h13 h23 Fr To AF AT hFr hTo hAF2 hAT2 i0 i1 i2 i3 bv0 bv1 bv2 bv3
    l0 l1 l2 l3 o0 o1 o2 o3
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,⟨cs,hrps⟩,hcost,hneed,hwk⟩ :=
    body_exec (mvAR V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length h02 h03 h12 h13 h23) rfl rfl rfl rfl rfl Fr To AF AT (callerP caller) m
    hm hF hT hAF hAT hFv hTv (m + 1) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(m : Int)⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(m : Int)⟩ : Cell)], [⟨(callerP caller).length,true⟩]⟩ : PS) =
      gS (callerP caller) [ci m] := by
    simp [gS]
  have gw := g1.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw
  have hpost := call_vecm_unit (mvAR V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 m0 m1 caller.frame.state.liveSpace
      caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h02 h03 h12 h13 h23)
    (fun k => decide (k = 2 ∨ k = 3))
    (by intro k hk; have : k = 2 ∨ k = 3 := by simpa using hk
        rcases this with rfl | rfl <;> simp [mvAR])
    caller Proofs.TreeArcsInstance.tree_arcs_from_list
    [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.value e1] Sinit
    (callerP caller ++ [(⟨i32,(m : Int)⟩ : Cell)]) [⟨(callerP caller).length,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [body_eqAR]; exact wr_bodyAR)
    (m + 1) rr (by rw [hmk, body_eqAR]; exact hexec) hret rfl (by omega) (by simp [hlenP]) e1.nodes (320 * m + 200) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.TreeArcsCall
