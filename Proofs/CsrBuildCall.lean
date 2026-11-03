import Proofs.CsrBuildPrepare
import Proofs.CsrBuildExec
import Proofs.CsrBuildSpec
import Proofs.MultiVecCall

namespace Proofs.CsrBuildCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.MatMulPrepare Proofs.CsrBuildPrepare
open Proofs.ForLoop (ci)
open Proofs.DijkstraOldScan (i32v)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (M31)
open Proofs.CsrBuildProg Proofs.CsrBuildExec Proofs.CsrBuildMath Proofs.CsrBuildSpec

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

/-- The callee of `csr_build`: `from`, `to` read-only, `head`, `target`, `pos` writable (all `int`). -/
def mvCB (V0 V1 V2 V3 V4 vsc0 vsc1 vsc2 vsc3 vsc4 : Nat) (m0 m1 : Bool) (L0 T0 sc N : Nat)
    (hnd : [V0, V1, V2, V3, V4].Nodup) : MV where
  nv := 5
  ty := fun _ => i32
  wV := fun k => decide (2 ≤ k)
  flag := fun k => if k = 0 then m0 else if k = 1 then m1 else true
  R := fun k => [V0, V1, V2, V3, V4].getD k 0
  vsc := fun k => [vsc0, vsc1, vsc2, vsc3, vsc4].getD k 0
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

def bbCB (b0 b1 b2 b3 b4 : Buffer Value) : Nat → Buffer Value :=
  fun k => if k = 0 then b0 else if k = 1 then b1 else if k = 2 then b2 else if k = 3 then b3 else b4

theorem cases5 (k : Nat) (hk : k < 5) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega

theorem wr_bodyCB : WrM (fun k => decide (2 ≤ k)) (progCB 5) = true := by decide

theorem fwCB_init (caller : NState)
    {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 s4 vb4 V4 vsc4 : Nat} {m0 m1 : Bool} {vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1) (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 true true vbuf2) (ok3 : VOKG caller i32 s3 vb3 V3 vsc3 true true vbuf3) (ok4 : VOKG caller i32 s4 vb4 V4 vsc4 true true vbuf4)
    (hnd : [V0, V1, V2, V3, V4].Nodup) (F T : List Nat) (x : XB) (hF : F.length < 2147483647) (hT : T.length < 2147483647)
    (hH : x.Hd.length < 2147483647) (hG : x.Tg.length < 2147483647) (hP : x.Ps.length < 2147483647)
    (i0 : vbuf0.items = ((F.map (fun a : Nat => (a : Int)))).map Value.integer) (i1 : vbuf1.items = ((T.map (fun a : Nat => (a : Int)))).map Value.integer) (i2 : vbuf2.items = (x.Hd).map Value.integer) (i3 : vbuf3.items = (x.Tg).map Value.integer) (i4 : vbuf4.items = (x.Ps).map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32))) (bv2 : vbuf2.Valid (accepts (.integer i32))) (bv3 : vbuf3.Valid (accepts (.integer i32))) (bv4 : vbuf4.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32) (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32) (l3 : vbuf3.limit = CppVectorBindings.sizeLimit i32) (l4 : vbuf4.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) (o3 : vbuf3.owner = V3) (o4 : vbuf4.owner = V4) :
    FWM (mvCB V0 V1 V2 V3 V4 vsc0 vsc1 vsc2 vsc3 vsc4 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length hnd)
      (VB F T x) (bbCB vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 ) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer i32,false,.root vsc0⟩,
         ⟨V1,.integer i32,false,.root vsc1⟩,
         ⟨V2,.integer i32,true,.root vsc2⟩,
         ⟨V3,.integer i32,true,.root vsc3⟩,
         ⟨V4,.integer i32,true,.root vsc4⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvCB] using ok0.vtag
    · simpa [mvCB] using ok1.vtag
    · simpa [mvCB] using ok2.vtag
    · simpa [mvCB] using ok3.vtag
    · simpa [mvCB] using ok4.vtag
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvCB, bbCB] using ok0.vfound
    · simpa [mvCB, bbCB] using ok1.vfound
    · simpa [mvCB, bbCB] using ok2.vfound
    · simpa [mvCB, bbCB] using ok3.vfound
    · simpa [mvCB, bbCB] using ok4.vfound
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvCB] using ok0.flag
    · simpa [mvCB] using ok1.flag
    · simpa [mvCB] using ok2.flag
    · simpa [mvCB] using ok3.flag
    · simpa [mvCB] using ok4.flag
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvCB, bbCB, VB] using i0
    · simpa [mvCB, bbCB, VB] using i1
    · simpa [mvCB, bbCB, VB] using i2
    · simpa [mvCB, bbCB, VB] using i3
    · simpa [mvCB, bbCB, VB] using i4
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvCB, bbCB] using bv0
    · simpa [mvCB, bbCB] using bv1
    · simpa [mvCB, bbCB] using bv2
    · simpa [mvCB, bbCB] using bv3
    · simpa [mvCB, bbCB] using bv4
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvCB, bbCB] using l0
    · simpa [mvCB, bbCB] using l1
    · simpa [mvCB, bbCB] using l2
    · simpa [mvCB, bbCB] using l3
    · simpa [mvCB, bbCB] using l4
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvCB, bbCB] using o0
    · simpa [mvCB, bbCB] using o1
    · simpa [mvCB, bbCB] using o2
    · simpa [mvCB, bbCB] using o3
    · simpa [mvCB, bbCB] using o4
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simp [VB]; omega
    · simp [VB]; omega
    · simp [VB]; omega
    · simp [VB]; omega
    · simp [VB]; omega


set_option maxHeartbeats 16000000 in
/-- `cp::csr_build(from, to, head, target, pos, n)`: for zero-initialised `head` (size `n + 1`), sizes `target` = `|from|` and
`pos` = `n`, builds the CSR graph: `head` becomes the prefix counts, the edges of each source are stored stably in `target`. -/
theorem csr_build_correct (caller : NState)
    {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 s4 vb4 V4 vsc4 : Nat} {m0 m1 : Bool} {vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1) (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 true true vbuf2) (ok3 : VOKG caller i32 s3 vb3 V3 vsc3 true true vbuf3) (ok4 : VOKG caller i32 s4 vb4 V4 vsc4 true true vbuf4)
    (hnd : [V0, V1, V2, V3, V4].Nodup)
    (F T : List Nat) (n : Nat) (hn : n < 2147483646) (hFl : F.length < 2147483646) (hTl : T.length = F.length)
    (hF : ∀ j, j < F.length → F.getD j 0 < n) (hT : ∀ j, j < F.length → T.getD j 0 < M31)
    (Tg0 Ps0 : List Int) (hTg : Tg0.length = F.length) (hPs : Ps0.length = n)
    (i0 : vbuf0.items = ((F.map (fun a : Nat => (a : Int)))).map Value.integer) (i1 : vbuf1.items = ((T.map (fun a : Nat => (a : Int)))).map Value.integer) (i2 : vbuf2.items = ((List.replicate (n + 1) (0 : Int))).map Value.integer) (i3 : vbuf3.items = (Tg0).map Value.integer) (i4 : vbuf4.items = (Ps0).map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32))) (bv2 : vbuf2.Valid (accepts (.integer i32))) (bv3 : vbuf3.Valid (accepts (.integer i32))) (bv4 : vbuf4.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32) (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32) (l3 : vbuf3.limit = CppVectorBindings.sizeLimit i32) (l4 : vbuf4.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) (o3 : vbuf3.owner = V3) (o4 : vbuf4.owner = V4)
    (e1 : NExpr) (hs1 : e1.scalarOnly = true) (ty1 : e1.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (n : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (H' T' : List Nat) (Ps' : List Int),
      prepare caller Proofs.CsrBuildInstance.csr_build.parameters
        [.vectorReference s0,
         .vectorReference s1,
         .vectorReference s2,
         .vectorReference s3,
         .vectorReference s4,
         .value e1] = some Sinit ∧
      Proofs.CsrBuildInstance.csr_build.callFuel fuel caller
        [.vectorReference s0,
         .vectorReference s1,
         .vectorReference s2,
         .vectorReference s3,
         .vectorReference s4,
         .value e1] = .finished (res, Ret.unit) ∧
      CSROut n F T H' T' ∧
      ScalarPostM (mvCB V0 V1 V2 V3 V4 vsc0 vsc1 vsc2 vsc3 vsc4 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length hnd)
        caller Sinit res e1.nodes (800 * (n + F.length) + 420) caller.scalars.memory
        (3 * F.length + 2 * n) (VB F T ⟨H'.map (fun a : Nat => (a : Int)), T'.map (fun a : Nat => (a : Int)), Ps'⟩) := by
  have hn32 : n < 2147483648 := by omega
  obtain ⟨t1, g1, Sinit, hprep, sSlots, sMem, sBind, sBase, sScope, sFrame, sWork, sPeakT, sPeak⟩ :=
    prepare_cb caller ok0 ok1 ok2 ok3 ok4 e1 (n : Int) hs1 ty1 value1 (validN n hn32)
  have fwS := fwCB_init caller ok0 ok1 ok2 ok3 ok4 hnd F T ⟨List.replicate (n + 1) (0 : Int), Tg0, Ps0⟩
    (by omega) (by omega) (by simp; omega) (by simp [hTg]; omega) (by simp [hPs]; omega)
    i0 i1 i2 i3 i4 bv0 bv1 bv2 bv3 bv4 l0 l1 l2 l3 l4 o0 o1 o2 o3 o4
  rw [← sFrame] at fwS
  obtain ⟨rr, Hd, Tg, Ps, hexec, hret, hrps, hrvv, hHl, hHf, hTgl, hTgf, hcost, hneed, hwk⟩ :=
    body_exec (mvCB V0 V1 V2 V3 V4 vsc0 vsc1 vsc2 vsc3 vsc4 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length hnd) rfl (fun _ _ => rfl) F T (callerP caller) n F.length (by unfold M31; omega) (by unfold M31; omega)
      (by unfold M31; omega) rfl hTl hF hT (List.replicate (n + 1) (0 : Int)) Tg0 Ps0 (by simp)
      (by intro y hy; simp at hy; exact hy) hTg hPs (n + F.length + 2) (Nat.le_refl _)
  obtain ⟨H', T', hout, hHd, hTgE⟩ := csr_glue F T n F.length rfl hF Hd Tg hHl hHf hTgl hTgf
  subst hHd
  subst hTgE
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
  have hpost := call_vecm_unit (mvCB V0 V1 V2 V3 V4 vsc0 vsc1 vsc2 vsc3 vsc4 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length hnd)
    (fun k => decide (2 ≤ k))
    (by
      intro k hk
      have h2 : 2 ≤ k := by simpa using hk
      refine ⟨hk, ?_⟩
      show (if k = 0 then m0 else if k = 1 then m1 else true) = true
      rw [if_neg (by omega), if_neg (by omega)])
    caller Proofs.CsrBuildInstance.csr_build
    [.vectorReference s0,
      .vectorReference s1,
      .vectorReference s2,
      .vectorReference s3,
      .vectorReference s4,
      .value e1] Sinit
    (callerP caller ++ [(⟨i32, (n : Int)⟩ : Cell)]) [⟨(callerP caller).length, true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    sPeak (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [body_eqCB]; exact wr_bodyCB)
    (n + F.length + 2) rr (by rw [hmk, body_eqCB]; exact hexec) hret rfl (by omega) (by simp [hlenP])
    e1.nodes (800 * (n + F.length) + 420) (by omega)
  obtain ⟨fuel, res, hrun, post⟩ := hpost
  refine ⟨Sinit, fuel, res, H', T', Ps, hprep, hrun, hout, ?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.CsrBuildCall
