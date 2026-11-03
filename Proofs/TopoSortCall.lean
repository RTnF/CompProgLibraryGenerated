import Proofs.TopoSortPrepare
import Proofs.TopoSortExec
import Proofs.MultiVecCall

namespace Proofs.TopoSortCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.TopoSortPrepare Proofs.TopoSortExec Proofs.TopoSortMath
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)

/-- The callee of `topological_sort`: four flat `int` vectors (`head`, `target` read-only; `indeg`, `order` writable). -/
def mvTS (V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 : Nat) (m0 m1 : Bool) (L0 T0 sc N : Nat) (h02 : V0 ≠ V2) (h12 : V1 ≠ V2)
    (h03 : V0 ≠ V3) (h13 : V1 ≠ V3) (h23 : V2 ≠ V3) : MV where
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

def bbTS (b0 b1 b2 b3 : Buffer Value) : Nat → Buffer Value :=
  fun k => if k = 0 then b0 else if k = 1 then b1 else if k = 2 then b2 else b3

theorem body_eqTS4 : Proofs.TopoInstance.topological_sort.body = bodyTS 4 := rfl

theorem cases4 (k : Nat) (hk : k < 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega


/-- The frame facts at entry of `topological_sort` (before any work). -/
theorem fwTS_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 : Nat} {m0 m1 : Bool}
    {vbuf0 vbuf1 vbuf2 vbuf3 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 true true vbuf2) (ok3 : VOKG caller i32 s3 vb3 V3 vsc3 true true vbuf3)
    (h02 : V0 ≠ V2) (h12 : V1 ≠ V2) (h03 : V0 ≠ V3) (h13 : V1 ≠ V3) (h23 : V2 ≠ V3)
    (H T I O : List Nat) (hHl : H.length < 2147483647) (hTl : T.length < 2147483647) (hIl : I.length < 2147483647)
    (hOl : O.length < 2147483647)
    (i0 : vbuf0.items = (H.map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = (T.map (fun x : Nat => (x : Int))).map Value.integer)
    (i2 : vbuf2.items = (I.map (fun x : Nat => (x : Int))).map Value.integer)
    (i3 : vbuf3.items = (O.map (fun x : Nat => (x : Int))).map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (bv2 : vbuf2.Valid (accepts (.integer i32))) (bv3 : vbuf3.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32) (l3 : vbuf3.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) (o3 : vbuf3.owner = V3) :
    FWM (mvTS V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h02 h12 h03 h13 h23)
      (VT H T I O) (bbTS vbuf0 vbuf1 vbuf2 vbuf3) 0
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
    · simpa [mvTS] using ok0.vtag
    · simpa [mvTS] using ok1.vtag
    · simpa [mvTS] using ok2.vtag
    · simpa [mvTS] using ok3.vtag
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvTS, bbTS] using ok0.vfound
    · simpa [mvTS, bbTS] using ok1.vfound
    · simpa [mvTS, bbTS] using ok2.vfound
    · simpa [mvTS, bbTS] using ok3.vfound
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvTS] using ok0.flag
    · simpa [mvTS] using ok1.flag
    · simpa [mvTS] using ok2.flag
    · simpa [mvTS] using ok3.flag
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvTS, bbTS, VT] using i0
    · simpa [mvTS, bbTS, VT] using i1
    · simpa [mvTS, bbTS, VT] using i2
    · simpa [mvTS, bbTS, VT] using i3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvTS, bbTS] using bv0
    · simpa [mvTS, bbTS] using bv1
    · simpa [mvTS, bbTS] using bv2
    · simpa [mvTS, bbTS] using bv3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvTS, bbTS] using l0
    · simpa [mvTS, bbTS] using l1
    · simpa [mvTS, bbTS] using l2
    · simpa [mvTS, bbTS] using l3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simpa [mvTS, bbTS] using o0
    · simpa [mvTS, bbTS] using o1
    · simpa [mvTS, bbTS] using o2
    · simpa [mvTS, bbTS] using o3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl
    · simp [VT]; omega
    · simp [VT]; omega
    · simp [VT]; omega
    · simp [VT]; omega


theorem wr_bodyTS4 : WrM (fun k => decide (k = 2 ∨ k = 3)) (bodyTS 4) = true := by decide

set_option maxHeartbeats 8000000 in
/-- `cp::topological_sort(head, target, indeg, order, n)` (Kahn's algorithm on the CSR arrays) returns the number `k` of vertices
placed in `order[0..k)`. -/
theorem topological_sort_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 : Nat}
    {m0 m1 : Bool} {vbuf0 vbuf1 vbuf2 vbuf3 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 true true vbuf2) (ok3 : VOKG caller i32 s3 vb3 V3 vsc3 true true vbuf3)
    (h02 : V0 ≠ V2) (h12 : V1 ≠ V2) (h03 : V0 ≠ V3) (h13 : V1 ≠ V3) (h23 : V2 ≠ V3)
    (H T O : List Nat) (n : Nat) (hn : n < 2147483646) (hm : T.length < 2147483647) (hTn : ∀ x ∈ T, x < n)
    (hOl : O.length = n) (HK : HeadOK H T n)
    (i0 : vbuf0.items = (H.map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = (T.map (fun x : Nat => (x : Int))).map Value.integer)
    (i2 : vbuf2.items = ((List.replicate n 0).map (fun x : Nat => (x : Int))).map Value.integer)
    (i3 : vbuf3.items = (O.map (fun x : Nat => (x : Int))).map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (bv2 : vbuf2.Valid (accepts (.integer i32))) (bv3 : vbuf3.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32) (l3 : vbuf3.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) (o3 : vbuf3.owner = V3)
    (e : NExpr) (hs : e.scalarOnly = true) (ty : e.resultType = i32) (value : e.denote (envOf caller) = some (n : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (I' : List Nat),
      prepare caller Proofs.TopoInstance.topological_sort.parameters
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.value e] = some Sinit ∧
      Proofs.TopoInstance.topological_sort.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.value e] =
        .finished (res,.scalar (((kahnL H T n (initSt T n)).2.length : Nat) : Int)) ∧
      (kahnL H T n (initSt T n)).2.Nodup ∧ (∀ x ∈ (kahnL H T n (initSt T n)).2, x < n) ∧
      (kahnL H T n (initSt T n)).2.length ≤ n ∧
      (∀ j (hj : j < (kahnL H T n (initSt T n)).2.length), ∀ u, u < n →
        (kahnL H T n (initSt T n)).2[j] ∈ outL H T u → u ∈ (kahnL H T n (initSt T n)).2.take j) ∧
      (∀ w, w < n → w ∉ (kahnL H T n (initSt T n)).2 → ∃ u, u < n ∧ u ∉ (kahnL H T n (initSt T n)).2 ∧ w ∈ outL H T u) ∧
      ScalarPostM (mvTS V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h02 h12 h03 h13 h23)
        caller Sinit res e.nodes (420 * (T.length * n) + 840 * n + 120 * T.length + 500) caller.scalars.memory
        (T.length + n + 2 * (T.length * n))
        (VT H T I' (ordPad (kahnL H T n (initSt T n)).2 O)) := by
  have hn32 : n < 2147483648 := by omega
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_ts caller ok0 ok1 ok2 ok3 e (n : Int) hs ty value (validN n hn32)
  have hHl : H.length < 2147483647 := by rw [HK.len]; omega
  have hZl : (List.replicate n 0).length < 2147483647 := by simp; omega
  have fwS := fwTS_init caller ok0 ok1 ok2 ok3 h02 h12 h03 h13 h23 H T (List.replicate n 0) O hHl hm hZl (by omega) i0 i1 i2 i3
    bv0 bv1 bv2 bv3 l0 l1 l2 l3 o0 o1 o2 o3
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrps,hrvv,hcost,hneed,hwk⟩ :=
    body_exec (mvTS V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h02 h12 h03 h13 h23) rfl (fun _ => rfl) H T O (callerP caller) n
      (by omega) hm hTn hOl HK (T.length + 2 + n + 1) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)], [⟨(callerP caller).length,true⟩]⟩ : PS) =
      gS (callerP caller) [ci n] := by
    simp [gS]
  have gw := good.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw
  have hk32 : (kahnL H T n (initSt T n)).2.length < 2147483648 := by
    have := (kahnL_inv H T n (fun x hx => hTn x hx) (initSt T n) (init_inv H T n HK hTn) n).ord_len
    omega
  have hpost := call_vecm (mvTS V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 m0 m1 caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h02 h12 h03 h13 h23)
    (fun k => decide (k = 2 ∨ k = 3))
    (by intro k hk; have : k = 2 ∨ k = 3 := by simpa using hk
        rcases this with rfl | rfl <;> simp [mvTS])
    caller Proofs.TopoInstance.topological_sort
    [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.value e] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)]) [⟨(callerP caller).length,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [body_eqTS4]; exact wr_bodyTS4)
    (T.length + 2 + n + 1) rr (by rw [hmk, body_eqTS4]; exact hexec)
    (((kahnL H T n (initSt T n)).2.length : Nat) : Int) hret i32 rfl (validN _ hk32)
    (by omega) (by simp [hlenP]) e.nodes (420 * (T.length * n) + 840 * n + 120 * T.length + 500) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  have hF := kahn_final H T n (fun x hx => hTn x hx) (initSt T n) (init_inv H T n HK hTn)
  obtain ⟨hnd, hlt, hle, hjp, hC⟩ := hF
  refine ⟨Sinit,fuel,res,(kahnL H T n (initSt T n)).1,hprep,hrun,hnd,hlt,hle,hjp,hC,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.TopoSortCall
