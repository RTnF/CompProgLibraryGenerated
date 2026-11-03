import Proofs.FindCyclePrepare
import Proofs.FindCycleProgExec
import Proofs.MultiVecCall

namespace Proofs.FindCycleCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.MatMulPrepare Proofs.FindCyclePrepare
open Proofs.ForLoop (ci)
open Proofs.DijkstraScan (i32v)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (M31)
open Proofs.FindCycleProg Proofs.FindCycleLists Proofs.FindCycleIter Proofs.FindCycleProgExec Proofs.FindCycleInv
open Proofs.FindCyclePhi Proofs.FindCycleSpec

theorem getD_mem_nat (t : List Nat) (k : Nat) (h : k < t.length) : t.getD k 0 ∈ t := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  exact List.getElem_mem _

theorem nodup_getD_ne : ∀ (l : List Nat), l.Nodup → ∀ j k, j < l.length → k < l.length → j ≠ k →
    l.getD j 0 ≠ l.getD k 0 := by
  intro l
  induction l with
  | nil => intro _ j k hj; simp at hj
  | cons a t ih =>
    intro hl j k hj hk hjk
    rw [List.nodup_cons] at hl
    cases j with
    | zero =>
      cases k with
      | zero => exact absurd rfl hjk
      | succ k' =>
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        intro h
        exact hl.1 (h ▸ getD_mem_nat t k' (by simpa using hk))
    | succ j' =>
      cases k with
      | zero =>
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        intro h
        exact hl.1 (h.symm ▸ getD_mem_nat t j' (by simpa using hj))
      | succ k' =>
        simp only [List.getD_cons_succ]
        exact ih hl.2 j' k' (by simpa using hj) (by simpa using hk) (fun e => hjk (by omega))

/-- The callee of `find_cycle`: `head`, `target` read-only, the four other vectors writable (all `int`). -/
def mvFC (V0 V1 V2 V3 V4 V5 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 : Nat) (m0 m1 : Bool) (L0 T0 sc N : Nat)
    (hnd : [V0, V1, V2, V3, V4, V5].Nodup) : MV where
  nv := 6
  ty := fun _ => i32
  wV := fun k => decide (2 ≤ k)
  flag := fun k => if k = 0 then m0 else if k = 1 then m1 else true
  R := fun k => [V0, V1, V2, V3, V4, V5].getD k 0
  vsc := fun k => [vsc0, vsc1, vsc2, vsc3, vsc4, vsc5].getD k 0
  perm := by
    intro k hk
    have : 2 ≤ k := by simpa using hk
    show (if k = 0 then m0 else if k = 1 then m1 else true) = true
    rw [if_neg (by omega), if_neg (by omega)]
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk _
    exact nodup_getD_ne _ hnd j k (by simpa using hj) (by simpa using hk) hjk

def bbFC (b0 b1 b2 b3 b4 b5 : Buffer Value) : Nat → Buffer Value :=
  fun k => if k = 0 then b0 else if k = 1 then b1 else if k = 2 then b2 else if k = 3 then b3 else if k = 4 then b4 else b5

theorem cases6 (k : Nat) (hk : k < 6) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega

theorem wr_bodyFC : WrM (fun k => decide (2 ≤ k)) (progFC 6) = true := by decide

theorem fwFC_init (caller : NState)
    {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 s4 vb4 V4 vsc4 s5 vb5 V5 vsc5 : Nat} {m0 m1 : Bool} {vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 vbuf5 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1) (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 true true vbuf2) (ok3 : VOKG caller i32 s3 vb3 V3 vsc3 true true vbuf3) (ok4 : VOKG caller i32 s4 vb4 V4 vsc4 true true vbuf4) (ok5 : VOKG caller i32 s5 vb5 V5 vsc5 true true vbuf5)
    (hnd : [V0, V1, V2, V3, V4, V5].Nodup) (H T : List Nat) (x : XF) (hH : H.length < 2147483647) (hT : T.length < 2147483647) (hC : x.Cl.length < 2147483647) (hI : x.Il.length < 2147483647) (hK : x.Kl.length < 2147483647) (hY : x.Yl.length < 2147483647)
    (i0 : vbuf0.items = (H.map (fun a : Nat => (a : Int))).map Value.integer) (i1 : vbuf1.items = (T.map (fun a : Nat => (a : Int))).map Value.integer) (i2 : vbuf2.items = (x.Cl).map Value.integer) (i3 : vbuf3.items = (x.Il).map Value.integer) (i4 : vbuf4.items = (x.Kl).map Value.integer) (i5 : vbuf5.items = (x.Yl).map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32))) (bv2 : vbuf2.Valid (accepts (.integer i32))) (bv3 : vbuf3.Valid (accepts (.integer i32))) (bv4 : vbuf4.Valid (accepts (.integer i32))) (bv5 : vbuf5.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32) (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32) (l3 : vbuf3.limit = CppVectorBindings.sizeLimit i32) (l4 : vbuf4.limit = CppVectorBindings.sizeLimit i32) (l5 : vbuf5.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) (o3 : vbuf3.owner = V3) (o4 : vbuf4.owner = V4) (o5 : vbuf5.owner = V5) :
    FWM (mvFC V0 V1 V2 V3 V4 V5 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length hnd)
      (VXF H T x) (bbFC vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 vbuf5) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer i32,false,.root vsc0⟩,
         ⟨V1,.integer i32,false,.root vsc1⟩,
         ⟨V2,.integer i32,true,.root vsc2⟩,
         ⟨V3,.integer i32,true,.root vsc3⟩,
         ⟨V4,.integer i32,true,.root vsc4⟩,
         ⟨V5,.integer i32,true,.root vsc5⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases6 k hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvFC] using ok0.vtag
    · simpa [mvFC] using ok1.vtag
    · simpa [mvFC] using ok2.vtag
    · simpa [mvFC] using ok3.vtag
    · simpa [mvFC] using ok4.vtag
    · simpa [mvFC] using ok5.vtag
  · intro k hk
    rcases cases6 k hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvFC, bbFC] using ok0.vfound
    · simpa [mvFC, bbFC] using ok1.vfound
    · simpa [mvFC, bbFC] using ok2.vfound
    · simpa [mvFC, bbFC] using ok3.vfound
    · simpa [mvFC, bbFC] using ok4.vfound
    · simpa [mvFC, bbFC] using ok5.vfound
  · intro k hk
    rcases cases6 k hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvFC] using ok0.flag
    · simpa [mvFC] using ok1.flag
    · simpa [mvFC] using ok2.flag
    · simpa [mvFC] using ok3.flag
    · simpa [mvFC] using ok4.flag
    · simpa [mvFC] using ok5.flag
  · intro k hk
    rcases cases6 k hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvFC, bbFC, VXF] using i0
    · simpa [mvFC, bbFC, VXF] using i1
    · simpa [mvFC, bbFC, VXF] using i2
    · simpa [mvFC, bbFC, VXF] using i3
    · simpa [mvFC, bbFC, VXF] using i4
    · simpa [mvFC, bbFC, VXF] using i5
  · intro k hk
    rcases cases6 k hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvFC, bbFC] using bv0
    · simpa [mvFC, bbFC] using bv1
    · simpa [mvFC, bbFC] using bv2
    · simpa [mvFC, bbFC] using bv3
    · simpa [mvFC, bbFC] using bv4
    · simpa [mvFC, bbFC] using bv5
  · intro k hk
    rcases cases6 k hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvFC, bbFC] using l0
    · simpa [mvFC, bbFC] using l1
    · simpa [mvFC, bbFC] using l2
    · simpa [mvFC, bbFC] using l3
    · simpa [mvFC, bbFC] using l4
    · simpa [mvFC, bbFC] using l5
  · intro k hk
    rcases cases6 k hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvFC, bbFC] using o0
    · simpa [mvFC, bbFC] using o1
    · simpa [mvFC, bbFC] using o2
    · simpa [mvFC, bbFC] using o3
    · simpa [mvFC, bbFC] using o4
    · simpa [mvFC, bbFC] using o5
  · intro k hk
    rcases cases6 k hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [VXF]; omega
    · simp [VXF]; omega
    · simp [VXF]; omega
    · simp [VXF]; omega
    · simp [VXF]; omega
    · simp [VXF]; omega

set_option maxHeartbeats 16000000 in
/-- `cp::find_cycle(head, target, state, it, stk, cyc, n)`: returns `0` iff the graph has no directed cycle, otherwise the
length `k` of a simple directed cycle, written to `cyc[0 .. k)`. -/
theorem find_cycle_correct (caller : NState)
    {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 s4 vb4 V4 vsc4 s5 vb5 V5 vsc5 : Nat} {m0 m1 : Bool} {vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 vbuf5 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1) (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 true true vbuf2) (ok3 : VOKG caller i32 s3 vb3 V3 vsc3 true true vbuf3) (ok4 : VOKG caller i32 s4 vb4 V4 vsc4 true true vbuf4) (ok5 : VOKG caller i32 s5 vb5 V5 vsc5 true true vbuf5)
    (hnd : [V0, V1, V2, V3, V4, V5].Nodup)
    (H T : List Nat) (n : Nat) (hn : n < 2147483646) (HK : Proofs.TopoSortMath.HeadOK H T n)
    (hTn : ∀ y ∈ T, y < n) (hTM : T.length < 2147483647)
    (Il0 Kl0 Yl0 : List Int) (hIl : Il0.length = n) (hKl : Kl0.length = n) (hYl : Yl0.length = n)
    (i0 : vbuf0.items = (H.map (fun a : Nat => (a : Int))).map Value.integer) (i1 : vbuf1.items = (T.map (fun a : Nat => (a : Int))).map Value.integer) (i2 : vbuf2.items = (List.replicate n (0 : Int)).map Value.integer) (i3 : vbuf3.items = (Il0).map Value.integer) (i4 : vbuf4.items = (Kl0).map Value.integer) (i5 : vbuf5.items = (Yl0).map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32))) (bv2 : vbuf2.Valid (accepts (.integer i32))) (bv3 : vbuf3.Valid (accepts (.integer i32))) (bv4 : vbuf4.Valid (accepts (.integer i32))) (bv5 : vbuf5.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32) (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32) (l3 : vbuf3.limit = CppVectorBindings.sizeLimit i32) (l4 : vbuf4.limit = CppVectorBindings.sizeLimit i32) (l5 : vbuf5.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) (o3 : vbuf3.owner = V3) (o4 : vbuf4.owner = V4) (o5 : vbuf5.owner = V5)
    (e1 : NExpr) (hs1 : e1.scalarOnly = true) (ty1 : e1.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (n : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (kk : Nat) (x' : XF),
      prepare caller Proofs.FindCycleInstance.find_cycle.parameters
        [.vectorReference s0,
         .vectorReference s1,
         .vectorReference s2,
         .vectorReference s3,
         .vectorReference s4,
         .vectorReference s5,
         .value e1] = some Sinit ∧
      Proofs.FindCycleInstance.find_cycle.callFuel fuel caller
        [.vectorReference s0,
         .vectorReference s1,
         .vectorReference s2,
         .vectorReference s3,
         .vectorReference s4,
         .vectorReference s5,
         .value e1] = .finished (res, Ret.scalar (kk : Int)) ∧
      FCOut n (hdF H) (tgF T) x'.Yl kk ∧
      ScalarPostM (mvFC V0 V1 V2 V3 V4 V5 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length hnd)
        caller Sinit res e1.nodes (4000 * n + 1360 * T.length + 1360 * n + 3150) caller.scalars.memory
        (9 * n + 4 * T.length) (VXF H T x') := by
  have hn32 : n < 2147483648 := by omega
  obtain ⟨t1, g1, Sinit, hprep, sSlots, sMem, sBind, sBase, sScope, sFrame, sWork, sPeakT, sPeak⟩ :=
    prepare_fc caller ok0 ok1 ok2 ok3 ok4 ok5 e1 (n : Int) hs1 ty1 value1 (validN n hn32)
  obtain ⟨x0, hx0⟩ : ∃ x0 : XF, x0 = ⟨initFS (fun i => Il0.getD i 0), List.replicate n (0 : Int), Il0, Kl0, Yl0⟩ := ⟨_, rfl⟩
  have valid_of : ∀ (l : List Int) (b : Buffer Value), b.items = l.map Value.integer → b.Valid (accepts (.integer i32)) →
      ∀ y ∈ l, i32.valid y = true := by
    intro l b hi hv y hy
    have h := hv.2.2
    rw [hi, List.all_eq_true] at h
    have := h (Value.integer y) (List.mem_map.mpr ⟨y, hy, rfl⟩)
    simpa [accepts] using this
  have R0 : LRF n x0 := by
    subst hx0
    refine ⟨by simp, hIl, hKl, hYl, ?_, fun i => rfl, fun i hi => by simp [initFS] at hi, ?_, valid_of _ _ i3 bv3,
      valid_of _ _ i4 bv4, valid_of _ _ i5 bv5⟩
    · intro i
      show (0 : Int) = (List.replicate n (0 : Int)).getD i 0
      rw [List.getD_eq_getElem?_getD]
      by_cases h : i < n <;> simp [h]
    · intro y hy
      simp at hy
      rw [hy.2]; decide
  have I0 : FInv n (hdF H) (tgF T) x0.st := by subst hx0; exact inv_initF n _ _ _
  have fwS := fwFC_init caller ok0 ok1 ok2 ok3 ok4 ok5 hnd H T x0 (by have := HK.len; omega) hTM (by rw [R0.lC]; omega)
    (by rw [R0.lI]; omega) (by rw [R0.lK]; omega) (by rw [R0.lY]; omega)
    i0 i1 (by rw [hx0]; exact i2) (by rw [hx0]; exact i3) (by rw [hx0]; exact i4) (by rw [hx0]; exact i5) bv0 bv1 bv2 bv3 bv4 bv5 l0 l1 l2 l3 l4 l5 o0 o1 o2 o3 o4 o5
  rw [← sFrame] at fwS
  have E : FE (mvFC V0 V1 V2 V3 V4 V5 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length hnd) n H T := ⟨rfl, fun k _ => rfl, by unfold M31; omega, HK, by unfold M31; omega, hTn⟩
  have hdle : ∀ a, a ≤ n → H.getD a 0 ≤ T.length := E.hd_le
  have G : FGH n (hdF H) (tgF T) := by
    refine ⟨fun a ha => HK.mono a ha, ?_⟩
    intro a b ⟨q, hq1, hq2, hq3⟩
    have han : a < n := by
      apply Classical.byContradiction
      intro hge
      have hlen := HK.len
      have h1 : H.getD (a + 1) 0 = 0 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      have : (hdF H) (a + 1) = 0 := h1
      omega
    refine ⟨han, ?_⟩
    have hq : q < T.length := by
      have := hdle (a + 1) (by omega)
      have h2 : q < H.getD (a + 1) 0 := hq2
      omega
    rw [← hq3]
    exact hTn _ (by
      show T.getD q 0 ∈ T
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
      exact List.getElem_mem _)
  have hphi0 : phiF n (hdF H) x0.st ≤ T.length + n := by subst hx0; exact phi0F E _
  obtain ⟨rr, x', kk, cl, hexec, hret, hrps, hrvv, hout, hkk, hcost, hneed, hwk⟩ :=
    prog_execF E G x0 I0 R0 (by subst hx0; rfl) (by subst hx0; intro a; rfl) hphi0 (callerP caller)
      (400 * n + T.length + n + 400) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length + caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32, (n : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32, (n : Int)⟩ : Cell)], [⟨(callerP caller).length, true⟩]⟩ : PS) =
      gS (callerP caller) [ci n] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hpost := call_vecm (mvFC V0 V1 V2 V3 V4 V5 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length hnd)
    (fun k => decide (2 ≤ k))
    (by
      intro k hk
      have h2 : 2 ≤ k := by simpa using hk
      refine ⟨hk, ?_⟩
      show (if k = 0 then m0 else if k = 1 then m1 else true) = true
      rw [if_neg (by omega), if_neg (by omega)])
    caller Proofs.FindCycleInstance.find_cycle
    [.vectorReference s0,
      .vectorReference s1,
      .vectorReference s2,
      .vectorReference s3,
      .vectorReference s4,
      .vectorReference s5,
      .value e1] Sinit
    (callerP caller ++ [(⟨i32, (n : Int)⟩ : Cell)]) [⟨(callerP caller).length, true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    sPeak (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [body_eqFC]; exact wr_bodyFC)
    (400 * n + T.length + n + 400) rr (by rw [hmk, body_eqFC]; exact hexec) (kk : Int) hret i32 rfl (i32v kk hkk)
    (by omega) (by simp [hlenP])
    e1.nodes (4000 * n + 1360 * T.length + 1360 * n + 3150) (by omega)
  obtain ⟨fuel, res, hrun, post⟩ := hpost
  refine ⟨Sinit, fuel, res, kk, x', hprep, hrun, hout, ?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

end Proofs.FindCycleCall
