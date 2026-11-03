import Proofs.TreeOrderPrepare
import Proofs.TreeOrderExec
import Proofs.MultiVecCallB

namespace Proofs.TreeOrderCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCallB
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.TreeOrderPrepare
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (cs)
open Proofs.TreeOrderBody Proofs.TreeOrderExec Proofs.TreeOrderMath Proofs.TreeDpSpec Proofs.TreeDpMath

def sel4 {α : Type} (a0 a1 a2 a3 : α) : Nat → α := fun k =>
  if k = 0 then a0 else if k = 1 then a1 else if k = 2 then a2 else a3

theorem cases4 (k : Nat) (hk : k < 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega

/-- The callee of `tree_order`: `head`, `target`, `parent` (read-only) and `ord` (writable), all `int` vectors. -/
def mvTO (V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 : Nat) (m0 m1 m2 : Bool) (L0 T0 sc N : Nat)
    (hd : ∀ j k, j < 4 → k < 4 → j ≠ k → 3 ≤ k → sel4 V0 V1 V2 V3 j ≠ sel4 V0 V1 V2 V3 k) : MV where
  nv := 4
  ty := fun _ => i32
  wV := fun k => decide (3 ≤ k)
  flag := fun k => if k = 0 then m0 else if k = 1 then m1 else if k = 2 then m2 else true
  R := sel4 V0 V1 V2 V3
  vsc := sel4 vsc0 vsc1 vsc2 vsc3
  perm := by
    intro k hk
    have : 3 ≤ k := by simpa using hk
    simp [show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega]
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk hw
    exact hd j k hj hk hjk (by simpa using hw)

def bbTO (b0 b1 b2 b3 : Buffer Value) : Nat → Buffer Value := sel4 b0 b1 b2 b3

theorem body_eqTO4 : Proofs.TreeOrderInstance.tree_order.body = bodyTO 4 := rfl

theorem wr_bodyTO : WrM (fun k => decide (3 ≤ k)) (bodyTO 4) = true := by decide


theorem fwTO_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 : Nat} {m0 m1 m2 : Bool}
    {vbuf0 vbuf1 vbuf2 vbuf3 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0)
    (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 false m2 vbuf2)
    (ok3 : VOKG caller i32 s3 vb3 V3 vsc3 true true vbuf3)
    (hdist : ∀ j k, j < 4 → k < 4 → j ≠ k → 3 ≤ k → sel4 V0 V1 V2 V3 j ≠ sel4 V0 V1 V2 V3 k)
    (head target : List Nat) (parent : List Int) (od0 : List Int)
    (hs : head.length < 2147483647 ∧ target.length < 2147483647 ∧ parent.length < 2147483647 ∧ od0.length < 2147483647)
    (i0 : vbuf0.items = (head.map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = (target.map (fun x : Nat => (x : Int))).map Value.integer)
    (i2 : vbuf2.items = parent.map Value.integer)
    (i3 : vbuf3.items = od0.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32)))
    (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (bv2 : vbuf2.Valid (accepts (.integer i32)))
    (bv3 : vbuf3.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32)
    (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32)
    (l3 : vbuf3.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0)
    (o1 : vbuf1.owner = V1)
    (o2 : vbuf2.owner = V2)
    (o3 : vbuf3.owner = V3)
    :
    FWM (mvTO V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 m0 m1 m2 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length hdist)
      (VA ⟨head.map (fun x : Nat => (x : Int)), target.map (fun x : Nat => (x : Int)), parent, od0⟩) (bbTO vbuf0 vbuf1 vbuf2 vbuf3) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer i32,false,.root vsc0⟩,
         ⟨V1,.integer i32,false,.root vsc1⟩,
         ⟨V2,.integer i32,false,.root vsc2⟩,
         ⟨V3,.integer i32,true,.root vsc3⟩]⟩ : Frame) := by
  obtain ⟨s0l, s1l, s2l, s3l⟩ := hs
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl <;> first | simpa [mvTO, bbTO, VA, sel4] using ok0.vtag | simpa [mvTO, bbTO, VA, sel4] using ok1.vtag | simpa [mvTO, bbTO, VA, sel4] using ok2.vtag | simpa [mvTO, bbTO, VA, sel4] using ok3.vtag
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl <;> first | simpa [mvTO, bbTO, VA, sel4] using ok0.vfound | simpa [mvTO, bbTO, VA, sel4] using ok1.vfound | simpa [mvTO, bbTO, VA, sel4] using ok2.vfound | simpa [mvTO, bbTO, VA, sel4] using ok3.vfound
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl <;> first | simpa [mvTO, bbTO, VA, sel4] using ok0.flag | simpa [mvTO, bbTO, VA, sel4] using ok1.flag | simpa [mvTO, bbTO, VA, sel4] using ok2.flag | simpa [mvTO, bbTO, VA, sel4] using ok3.flag
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl <;> first | simpa [mvTO, bbTO, VA, sel4] using i0 | simpa [mvTO, bbTO, VA, sel4] using i1 | simpa [mvTO, bbTO, VA, sel4] using i2 | simpa [mvTO, bbTO, VA, sel4] using i3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl <;> first | simpa [mvTO, bbTO, sel4] using bv0 | simpa [mvTO, bbTO, sel4] using bv1 | simpa [mvTO, bbTO, sel4] using bv2 | simpa [mvTO, bbTO, sel4] using bv3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl <;> first | simpa [mvTO, bbTO, sel4] using l0 | simpa [mvTO, bbTO, sel4] using l1 | simpa [mvTO, bbTO, sel4] using l2 | simpa [mvTO, bbTO, sel4] using l3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl <;> first | simpa [mvTO, bbTO, sel4] using o0 | simpa [mvTO, bbTO, sel4] using o1 | simpa [mvTO, bbTO, sel4] using o2 | simpa [mvTO, bbTO, sel4] using o3
  · intro k hk
    rcases cases4 k hk with rfl | rfl | rfl | rfl <;> simp [VA, mvTO, sel4] <;> omega

set_option maxHeartbeats 16000000 in
/-- `cp::tree_order(head, target, parent, ord, root, n)`. -/
theorem tree_order_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 : Nat} {m0 m1 m2 : Bool}
    {vbuf0 vbuf1 vbuf2 vbuf3 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0)
    (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 false m2 vbuf2)
    (ok3 : VOKG caller i32 s3 vb3 V3 vsc3 true true vbuf3)
    (hdist : ∀ j k, j < 4 → k < 4 → j ≠ k → 3 ≤ k → sel4 V0 V1 V2 V3 j ≠ sel4 V0 V1 V2 V3 k)
    (head target : List Nat) (parent : List Int) (od0 : List Int) (n root : Nat)
    (H : TO head target parent n root)
    (hlen : head.length = n + 1) (hmono : ∀ v, v < n → head.getD v 0 ≤ head.getD (v + 1) 0)
    (hlast : head.getD n 0 = target.length) (tlen : target.length < 2147483647)
    (tlt : ∀ q, q < target.length → target.getD q 0 < n) (nb : n + 2 < 2147483648) (palen : parent.length = n)
    (pav : ∀ w, w < n → 0 ≤ parent.getD w 0 ∧ parent.getD w 0 < n) (odl : od0.length = n)
    (i0 : vbuf0.items = (head.map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = (target.map (fun x : Nat => (x : Int))).map Value.integer)
    (i2 : vbuf2.items = parent.map Value.integer)
    (i3 : vbuf3.items = od0.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32)))
    (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (bv2 : vbuf2.Valid (accepts (.integer i32)))
    (bv3 : vbuf3.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32)
    (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32)
    (l3 : vbuf3.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0)
    (o1 : vbuf1.owner = V1)
    (o2 : vbuf2.owner = V2)
    (o3 : vbuf3.owner = V3)
    (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (ty1 : e1.resultType = i32)
    (ty2 : e2.resultType = i32) (value1 : e1.denote (envOf caller) = some (root : Int))
    (value2 : e2.denote (envOf caller) = some (n : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (Qf : List Nat),
      prepare caller Proofs.TreeOrderInstance.tree_order.parameters
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.value e1,.value e2] = some Sinit ∧
      Proofs.TreeOrderInstance.tree_order.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.value e1,.value e2] = .finished (res,Ret.unit) ∧
      Qf.length = n ∧ Qf.Nodup ∧ (∀ x ∈ Qf, x < n) ∧ Qf.getD 0 0 = root ∧
      (∀ j, 1 ≤ j → j < n → ∃ j', j' < j ∧ Qf.getD j' 0 = par parent (Qf.getD j 0)) ∧
      ScalarPostMB 1000 (mvTO V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 m0 m1 m2 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length hdist)
        caller Sinit res (e1.nodes + e2.nodes) (1100 * target.length + 1600 * n + 700) caller.scalars.memory
        (target.length + 2 * n + 6) (VA ⟨head.map (fun x : Nat => (x : Int)), target.map (fun x : Nat => (x : Int)), parent, Qf.map (fun x : Nat => (x : Int))⟩) := by
  have hrn := H.rootlt
  have hrk : root < 2147483648 := by omega
  have hn32 : n < 2147483648 := by omega
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_to caller ok0 ok1 ok2 ok3 e1 e2 (root : Int) (n : Int) hs1 hs2 ty1 ty2 value1 value2 (validN root hrk) (validN n hn32)
  have fwS := fwTO_init caller ok0 ok1 ok2 ok3 hdist head target parent od0
    ⟨by omega, by omega, by omega, by omega⟩ i0 i1 i2 i3 bv0 bv1 bv2 bv3 l0 l1 l2 l3 o0 o1 o2 o3
  rw [← sFrame] at fwS
  obtain ⟨rr,Qf,hexec,hret,hrps,hrvv,hQf,hlenQ,hnd,hlt,hhd,hpar,hcost,hneed,hwk⟩ :=
    to_body (mvTO V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 m0 m1 m2 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length hdist) rfl (by simp [mvTO]) (by simp [mvTO])
      (by simp [mvTO]) (by simp [mvTO]) (callerP caller) (n + target.length + 6) head target parent n root H ⟨head.map (fun x : Nat => (x : Int)), target.map (fun x : Nat => (x : Int)), parent, od0⟩
      ⟨rfl, rfl, rfl, hlen, hmono, hlast, tlen, tlt, nb, palen, pav⟩ odl (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(root : Int)⟩ : Cell),(⟨i32,(n : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(root : Int)⟩ : Cell),(⟨i32,(n : Int)⟩ : Cell)],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]⟩ : PS) = gS (callerP caller) [ci root, ci n] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2
  have hpost := call_vecm_unitB 1000 (mvTO V0 V1 V2 V3 vsc0 vsc1 vsc2 vsc3 m0 m1 m2 caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length hdist)
    (fun k => decide (3 ≤ k))
    (by intro k hk; have : 3 ≤ k := by simpa using hk
        simp [mvTO, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, this])
    caller Proofs.TreeOrderInstance.tree_order
    [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨i32,(root : Int)⟩ : Cell),(⟨i32,(n : Int)⟩ : Cell)])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [body_eqTO4]; exact wr_bodyTO)
    (n + target.length + 6) rr (by rw [hmk, body_eqTO4]; exact hexec) hret rfl (by omega)
    (by simp [hlenP]) (e1.nodes + e2.nodes) (1100 * target.length + 1600 * n + 700) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,Qf,hprep,hrun,hlenQ,hnd,hlt,hhd,hpar,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.TreeOrderCall
