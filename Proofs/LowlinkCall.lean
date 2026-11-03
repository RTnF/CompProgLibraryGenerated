import Proofs.LowlinkPrepare
import Proofs.LowlinkProgExec
import Proofs.LowlinkSpec
import Proofs.MultiVecCall

namespace Proofs.LowlinkCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.DoublingNested (i32)
open Proofs.MatMulPrepare Proofs.LowlinkPrepare
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (M31)
open Proofs.LowlinkProg Proofs.LowlinkLists Proofs.LowlinkExec Proofs.LowlinkIter Proofs.LowlinkProgExec Proofs.LowlinkInv
open Proofs.LowlinkSpec Proofs.LowlinkFinal Proofs.LowlinkPhi

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

/-- The callee of `lowlink`: `head`, `target` read-only, the six other vectors writable (all `int`). -/
def mvLL (V0 V1 V2 V3 V4 V5 V6 V7 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 vsc6 vsc7 : Nat) (m0 m1 : Bool) (L0 T0 sc N : Nat)
    (hnd : [V0, V1, V2, V3, V4, V5, V6, V7].Nodup) : MV where
  nv := 8
  ty := fun _ => i32
  wV := fun k => decide (2 ≤ k)
  flag := fun k => if k = 0 then m0 else if k = 1 then m1 else true
  R := fun k => [V0, V1, V2, V3, V4, V5, V6, V7].getD k 0
  vsc := fun k => [vsc0, vsc1, vsc2, vsc3, vsc4, vsc5, vsc6, vsc7].getD k 0
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

def bbLL (b0 b1 b2 b3 b4 b5 b6 b7 : Buffer Value) : Nat → Buffer Value :=
  fun k => if k = 0 then b0 else if k = 1 then b1 else if k = 2 then b2 else if k = 3 then b3 else if k = 4 then b4 else if k = 5 then b5 else if k = 6 then b6 else b7

theorem cases8 (k : Nat) (hk : k < 8) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega

theorem wr_bodyLL : WrM (fun k => decide (2 ≤ k)) (progLL 8) = true := by decide

theorem fwLL_init (caller : NState)
    {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 s4 vb4 V4 vsc4 s5 vb5 V5 vsc5 s6 vb6 V6 vsc6 s7 vb7 V7 vsc7 : Nat} {m0 m1 : Bool} {vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 vbuf5 vbuf6 vbuf7 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1) (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 true true vbuf2) (ok3 : VOKG caller i32 s3 vb3 V3 vsc3 true true vbuf3) (ok4 : VOKG caller i32 s4 vb4 V4 vsc4 true true vbuf4) (ok5 : VOKG caller i32 s5 vb5 V5 vsc5 true true vbuf5) (ok6 : VOKG caller i32 s6 vb6 V6 vsc6 true true vbuf6) (ok7 : VOKG caller i32 s7 vb7 V7 vsc7 true true vbuf7)
    (hnd : [V0, V1, V2, V3, V4, V5, V6, V7].Nodup) (H T : List Nat) (x : XS) (hH : H.length < 2147483647) (hT : T.length < 2147483647) (hO : x.Ol.length < 2147483647) (hL : x.Ll.length < 2147483647) (hP : x.Pl.length < 2147483647) (hS : x.Sl.length < 2147483647) (hI : x.Il.length < 2147483647) (hK : x.Kl.length < 2147483647)
    (i0 : vbuf0.items = (H.map (fun a : Nat => (a : Int))).map Value.integer) (i1 : vbuf1.items = (T.map (fun a : Nat => (a : Int))).map Value.integer) (i2 : vbuf2.items = (x.Ol).map Value.integer) (i3 : vbuf3.items = (x.Ll).map Value.integer) (i4 : vbuf4.items = (x.Pl).map Value.integer) (i5 : vbuf5.items = (x.Sl).map Value.integer) (i6 : vbuf6.items = (x.Il).map Value.integer) (i7 : vbuf7.items = (x.Kl).map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32))) (bv2 : vbuf2.Valid (accepts (.integer i32))) (bv3 : vbuf3.Valid (accepts (.integer i32))) (bv4 : vbuf4.Valid (accepts (.integer i32))) (bv5 : vbuf5.Valid (accepts (.integer i32))) (bv6 : vbuf6.Valid (accepts (.integer i32))) (bv7 : vbuf7.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32) (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32) (l3 : vbuf3.limit = CppVectorBindings.sizeLimit i32) (l4 : vbuf4.limit = CppVectorBindings.sizeLimit i32) (l5 : vbuf5.limit = CppVectorBindings.sizeLimit i32) (l6 : vbuf6.limit = CppVectorBindings.sizeLimit i32) (l7 : vbuf7.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) (o3 : vbuf3.owner = V3) (o4 : vbuf4.owner = V4) (o5 : vbuf5.owner = V5) (o6 : vbuf6.owner = V6) (o7 : vbuf7.owner = V7) :
    FWM (mvLL V0 V1 V2 V3 V4 V5 V6 V7 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 vsc6 vsc7 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length hnd)
      (VX H T x) (bbLL vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 vbuf5 vbuf6 vbuf7) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer i32,false,.root vsc0⟩,
         ⟨V1,.integer i32,false,.root vsc1⟩,
         ⟨V2,.integer i32,true,.root vsc2⟩,
         ⟨V3,.integer i32,true,.root vsc3⟩,
         ⟨V4,.integer i32,true,.root vsc4⟩,
         ⟨V5,.integer i32,true,.root vsc5⟩,
         ⟨V6,.integer i32,true,.root vsc6⟩,
         ⟨V7,.integer i32,true,.root vsc7⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases8 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvLL] using ok0.vtag
    · simpa [mvLL] using ok1.vtag
    · simpa [mvLL] using ok2.vtag
    · simpa [mvLL] using ok3.vtag
    · simpa [mvLL] using ok4.vtag
    · simpa [mvLL] using ok5.vtag
    · simpa [mvLL] using ok6.vtag
    · simpa [mvLL] using ok7.vtag
  · intro k hk
    rcases cases8 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvLL, bbLL] using ok0.vfound
    · simpa [mvLL, bbLL] using ok1.vfound
    · simpa [mvLL, bbLL] using ok2.vfound
    · simpa [mvLL, bbLL] using ok3.vfound
    · simpa [mvLL, bbLL] using ok4.vfound
    · simpa [mvLL, bbLL] using ok5.vfound
    · simpa [mvLL, bbLL] using ok6.vfound
    · simpa [mvLL, bbLL] using ok7.vfound
  · intro k hk
    rcases cases8 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvLL] using ok0.flag
    · simpa [mvLL] using ok1.flag
    · simpa [mvLL] using ok2.flag
    · simpa [mvLL] using ok3.flag
    · simpa [mvLL] using ok4.flag
    · simpa [mvLL] using ok5.flag
    · simpa [mvLL] using ok6.flag
    · simpa [mvLL] using ok7.flag
  · intro k hk
    rcases cases8 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvLL, bbLL, VX] using i0
    · simpa [mvLL, bbLL, VX] using i1
    · simpa [mvLL, bbLL, VX] using i2
    · simpa [mvLL, bbLL, VX] using i3
    · simpa [mvLL, bbLL, VX] using i4
    · simpa [mvLL, bbLL, VX] using i5
    · simpa [mvLL, bbLL, VX] using i6
    · simpa [mvLL, bbLL, VX] using i7
  · intro k hk
    rcases cases8 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvLL, bbLL] using bv0
    · simpa [mvLL, bbLL] using bv1
    · simpa [mvLL, bbLL] using bv2
    · simpa [mvLL, bbLL] using bv3
    · simpa [mvLL, bbLL] using bv4
    · simpa [mvLL, bbLL] using bv5
    · simpa [mvLL, bbLL] using bv6
    · simpa [mvLL, bbLL] using bv7
  · intro k hk
    rcases cases8 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvLL, bbLL] using l0
    · simpa [mvLL, bbLL] using l1
    · simpa [mvLL, bbLL] using l2
    · simpa [mvLL, bbLL] using l3
    · simpa [mvLL, bbLL] using l4
    · simpa [mvLL, bbLL] using l5
    · simpa [mvLL, bbLL] using l6
    · simpa [mvLL, bbLL] using l7
  · intro k hk
    rcases cases8 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvLL, bbLL] using o0
    · simpa [mvLL, bbLL] using o1
    · simpa [mvLL, bbLL] using o2
    · simpa [mvLL, bbLL] using o3
    · simpa [mvLL, bbLL] using o4
    · simpa [mvLL, bbLL] using o5
    · simpa [mvLL, bbLL] using o6
    · simpa [mvLL, bbLL] using o7
  · intro k hk
    rcases cases8 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [VX]; omega
    · simp [VX]; omega
    · simp [VX]; omega
    · simp [VX]; omega
    · simp [VX]; omega
    · simp [VX]; omega
    · simp [VX]; omega
    · simp [VX]; omega

/-- The meaning of the output arrays of `lowlink`. -/
def LLOut (n : Nat) (hd tg : Nat → Nat) (Ol Ll Pl Sl : List Int) : Prop :=
  Ol.length = n ∧ Ll.length = n ∧ Pl.length = n ∧ Sl.length = n ∧
  (∀ v, v < n → 0 ≤ Ol.getD v (-1) ∧ Ol.getD v (-1) < (n : Int)) ∧
  (∀ u v, u < n → v < n → Ol.getD u (-1) = Ol.getD v (-1) → u = v) ∧
  (∀ v, v < n → Pl.getD v (-1) = -1 ∨ ∃ p : Nat, p < n ∧ Pl.getD v (-1) = (p : Int) ∧ AdjH hd tg p v ∧
    Ol.getD p (-1) < Ol.getD v (-1)) ∧
  (∀ v p : Nat, v < n → Pl.getD v (-1) = (p : Int) →
    (Ll.getD v 0 = Ol.getD v (-1) ↔ ¬ Proofs.PrimMath.Rtc (Proofs.LowlinkGraph.LlFinal.EB (AdjH hd tg) p v) p v)) ∧
  (∀ v, v < n → (((Pl.getD v (-1) < 0 ∧ 2 ≤ Sl.getD v 0) ∨ (0 ≤ Pl.getD v (-1) ∧ 1 ≤ Sl.getD v 0)) ↔
    ∃ a b, AdjH hd tg v a ∧ AdjH hd tg v b ∧
      ¬ Proofs.PrimMath.Rtc (Proofs.LowlinkGraph.LlFinal.EV (AdjH hd tg) v) a b))

theorem llout_of {n : Nat} {hd tg : Nat → Nat} (G : GH n hd tg) (x' : XS) (I : MInv n hd tg x'.st) (R : LR n x')
    (hsp : x'.st.sp = 0) (hall : ∀ a, a < n → a ∈ x'.st.Vis) : LLOut n hd tg x'.Ol x'.Ll x'.Pl x'.Sl := by
  obtain ⟨s1, s2, s3, s4, s5⟩ := lowlink_spec G I hsp hall
  have eO : ∀ v, v < n → x'.Ol.getD v (-1) = x'.st.O v := fun v _ => (R.fO v).symm
  have eL : ∀ v, v < n → x'.Ll.getD v 0 = x'.st.L v := fun v _ => (R.fL v).symm
  have eP : ∀ v, v < n → x'.Pl.getD v (-1) = x'.st.P v := fun v _ => (R.fP v).symm
  have eS : ∀ v, v < n → x'.Sl.getD v 0 = x'.st.Sp v := fun v _ => (R.fS v).symm
  refine ⟨R.lO, R.lL, R.lP, R.lS, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv; rw [eO v hv]; exact s1 v hv
  · intro u v hu hv h; rw [eO u hu, eO v hv] at h; exact s2 u v hu hv h
  · intro v hv
    rw [eP v hv]
    rcases s3 v hv with h | ⟨p, hp, hP, hA, hO⟩
    · exact Or.inl h
    · refine Or.inr ⟨p, hp, hP, hA, ?_⟩
      rw [eO p hp, eO v hv]; exact hO
  · intro v p hv hp
    rw [eP v hv] at hp
    rw [eL v hv, eO v hv]
    exact s4 v p hv hp
  · intro v hv
    rw [eP v hv, eS v hv]
    exact s5 v hv

set_option maxHeartbeats 16000000 in
/-- `cp::lowlink(head, target, ord, low, par, sep, it, stk, n)`: the DFS order, the low links, the parents and the
separating child counts of the symmetric loop-free graph given by the CSR arrays `head`/`target`. -/
theorem lowlink_correct (caller : NState)
    {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 s4 vb4 V4 vsc4 s5 vb5 V5 vsc5 s6 vb6 V6 vsc6 s7 vb7 V7 vsc7 : Nat} {m0 m1 : Bool} {vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 vbuf5 vbuf6 vbuf7 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1) (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 true true vbuf2) (ok3 : VOKG caller i32 s3 vb3 V3 vsc3 true true vbuf3) (ok4 : VOKG caller i32 s4 vb4 V4 vsc4 true true vbuf4) (ok5 : VOKG caller i32 s5 vb5 V5 vsc5 true true vbuf5) (ok6 : VOKG caller i32 s6 vb6 V6 vsc6 true true vbuf6) (ok7 : VOKG caller i32 s7 vb7 V7 vsc7 true true vbuf7)
    (hnd : [V0, V1, V2, V3, V4, V5, V6, V7].Nodup)
    (H T : List Nat) (n : Nat) (hn : n < 2147483646) (HK : Proofs.TopoSortMath.HeadOK H T n)
    (hTn : ∀ y ∈ T, y < n) (hTM : T.length < 2147483647)
    (hsym : ∀ a b, AdjH (hdF H) (tgF T) a b → AdjH (hdF H) (tgF T) b a)
    (hirr : ∀ a, ¬ AdjH (hdF H) (tgF T) a a)
    (Ll0 Il0 Kl0 : List Int) (hLl : Ll0.length = n) (hIl : Il0.length = n) (hKl : Kl0.length = n)
    (i0 : vbuf0.items = (H.map (fun a : Nat => (a : Int))).map Value.integer) (i1 : vbuf1.items = (T.map (fun a : Nat => (a : Int))).map Value.integer) (i2 : vbuf2.items = (List.replicate n (-1 : Int)).map Value.integer) (i3 : vbuf3.items = (Ll0).map Value.integer) (i4 : vbuf4.items = (List.replicate n (-1 : Int)).map Value.integer) (i5 : vbuf5.items = (List.replicate n (0 : Int)).map Value.integer) (i6 : vbuf6.items = (Il0).map Value.integer) (i7 : vbuf7.items = (Kl0).map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32))) (bv2 : vbuf2.Valid (accepts (.integer i32))) (bv3 : vbuf3.Valid (accepts (.integer i32))) (bv4 : vbuf4.Valid (accepts (.integer i32))) (bv5 : vbuf5.Valid (accepts (.integer i32))) (bv6 : vbuf6.Valid (accepts (.integer i32))) (bv7 : vbuf7.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32) (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32) (l3 : vbuf3.limit = CppVectorBindings.sizeLimit i32) (l4 : vbuf4.limit = CppVectorBindings.sizeLimit i32) (l5 : vbuf5.limit = CppVectorBindings.sizeLimit i32) (l6 : vbuf6.limit = CppVectorBindings.sizeLimit i32) (l7 : vbuf7.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) (o3 : vbuf3.owner = V3) (o4 : vbuf4.owner = V4) (o5 : vbuf5.owner = V5) (o6 : vbuf6.owner = V6) (o7 : vbuf7.owner = V7)
    (e1 : NExpr) (hs1 : e1.scalarOnly = true) (ty1 : e1.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (n : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (x' : XS),
      prepare caller Proofs.LowlinkInstance.lowlink.parameters
        [.vectorReference s0,
         .vectorReference s1,
         .vectorReference s2,
         .vectorReference s3,
         .vectorReference s4,
         .vectorReference s5,
         .vectorReference s6,
         .vectorReference s7,
         .value e1] = some Sinit ∧
      Proofs.LowlinkInstance.lowlink.callFuel fuel caller
        [.vectorReference s0,
         .vectorReference s1,
         .vectorReference s2,
         .vectorReference s3,
         .vectorReference s4,
         .vectorReference s5,
         .vectorReference s6,
         .vectorReference s7,
         .value e1] = .finished (res, Ret.unit) ∧
      LLOut n (hdF H) (tgF T) x'.Ol x'.Ll x'.Pl x'.Sl ∧
      ScalarPostM (mvLL V0 V1 V2 V3 V4 V5 V6 V7 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 vsc6 vsc7 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length hnd)
        caller Sinit res e1.nodes (2670 * n + 1750 * T.length + 250) caller.scalars.memory
        (11 * n + 7 * T.length + 10) (VX H T x') := by
  have hn32 : n < 2147483648 := by omega
  obtain ⟨t1, g1, Sinit, hprep, sSlots, sMem, sBind, sBase, sScope, sFrame, sWork, sPeakT, sPeak⟩ :=
    prepare_ll caller ok0 ok1 ok2 ok3 ok4 ok5 ok6 ok7 e1 (n : Int) hs1 ty1 value1 (validN n hn32)
  -- the initial arrays
  obtain ⟨x0, hx0⟩ : ∃ x0 : XS, x0 = ⟨initS (fun i => Ll0.getD i 0) (fun i => Il0.getD i 0) (fun _ => 0),
      List.replicate n (-1 : Int), Ll0, List.replicate n (-1 : Int), List.replicate n (0 : Int), Il0, Kl0⟩ := ⟨_, rfl⟩
  have valid_of : ∀ (l : List Int) (b : Buffer Value), b.items = l.map Value.integer → b.Valid (accepts (.integer i32)) →
      ∀ y ∈ l, i32.valid y = true := by
    intro l b hi hv y hy
    have h := hv.2.2
    rw [hi, List.all_eq_true] at h
    have := h (Value.integer y) (List.mem_map.mpr ⟨y, hy, rfl⟩)
    simpa [accepts] using this
  have R0 : LR n x0 := by
    subst hx0
    refine ⟨by simp, hLl, by simp, by simp, hIl, hKl, ?_, fun i => rfl, ?_, ?_, fun i => rfl, fun i hi => by simp [initS] at hi, ?_,
      valid_of _ _ i3 bv3, ?_, ?_, valid_of _ _ i6 bv6, valid_of _ _ i7 bv7⟩
    · intro i
      show (-1 : Int) = (List.replicate n (-1 : Int)).getD i (-1)
      rw [List.getD_eq_getElem?_getD]
      by_cases h : i < n <;> simp [h]
    · intro i
      show (-1 : Int) = (List.replicate n (-1 : Int)).getD i (-1)
      rw [List.getD_eq_getElem?_getD]
      by_cases h : i < n <;> simp [h]
    · intro i
      show (0 : Int) = (List.replicate n (0 : Int)).getD i 0
      rw [List.getD_eq_getElem?_getD]
      by_cases h : i < n <;> simp [h]
    · intro y hy
      simp at hy
      rw [hy.2]; decide
    · intro y hy
      simp at hy
      rw [hy.2]; decide
    · intro y hy
      simp at hy
      rw [hy.2]; decide
  have I0 : MInv n (hdF H) (tgF T) x0.st := by subst hx0; exact inv_init n _ _ _ _ _
  have fwS := fwLL_init caller ok0 ok1 ok2 ok3 ok4 ok5 ok6 ok7 hnd H T x0 (by have := HK.len; omega) hTM (by rw [R0.lO]; omega)
    (by rw [R0.lL]; omega) (by rw [R0.lP]; omega) (by rw [R0.lS]; omega) (by rw [R0.lI]; omega) (by rw [R0.lK]; omega)
    i0 i1 (by rw [hx0]; exact i2) (by rw [hx0]; exact i3) (by rw [hx0]; exact i4) (by rw [hx0]; exact i5)
    (by rw [hx0]; exact i6) (by rw [hx0]; exact i7) bv0 bv1 bv2 bv3 bv4 bv5 bv6 bv7 l0 l1 l2 l3 l4 l5 l6 l7 o0 o1 o2 o3 o4 o5 o6 o7
  rw [← sFrame] at fwS
  -- the standing hypotheses of the execution
  have E : XE (mvLL V0 V1 V2 V3 V4 V5 V6 V7 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 vsc6 vsc7 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length hnd) n H T := ⟨rfl, fun k _ => rfl, by unfold M31; omega, HK, by unfold M31; omega, hTn⟩
  have hdle : ∀ a, a ≤ n → H.getD a 0 ≤ T.length := E.hd_le
  have G : GH n (hdF H) (tgF T) := by
    refine ⟨fun a ha => HK.mono a ha, ?_, hsym, hirr⟩
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
  have hphi0 : phi n (hdF H) x0.st ≤ T.length + n := by subst hx0; exact phi0_le E _ _ _
  obtain ⟨rr, x', hexec, hret, hrps, hrvv, I', R', hsp', hall, hcost, hneed, hwk⟩ :=
    prog_exec E G x0 I0 R0 (by subst hx0; rfl) (by subst hx0; rfl) hphi0 (callerP caller) (T.length + 2 * n + 3)
      (Nat.le_refl _)
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
  have hpost := call_vecm_unit (mvLL V0 V1 V2 V3 V4 V5 V6 V7 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 vsc6 vsc7 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length hnd)
    (fun k => decide (2 ≤ k))
    (by
      intro k hk
      have h2 : 2 ≤ k := by simpa using hk
      refine ⟨hk, ?_⟩
      show (if k = 0 then m0 else if k = 1 then m1 else true) = true
      rw [if_neg (by omega), if_neg (by omega)])
    caller Proofs.LowlinkInstance.lowlink
    [.vectorReference s0,
      .vectorReference s1,
      .vectorReference s2,
      .vectorReference s3,
      .vectorReference s4,
      .vectorReference s5,
      .vectorReference s6,
      .vectorReference s7,
      .value e1] Sinit
    (callerP caller ++ [(⟨i32, (n : Int)⟩ : Cell)]) [⟨(callerP caller).length, true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    sPeak (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [body_eqLL]; exact wr_bodyLL)
    (T.length + 2 * n + 3) rr (by rw [hmk, body_eqLL]; exact hexec) hret rfl (by omega) (by simp [hlenP])
    e1.nodes (2670 * n + 1750 * T.length + 250) (by omega)
  obtain ⟨fuel, res, hrun, post⟩ := hpost
  refine ⟨Sinit, fuel, res, x', hprep, hrun, llout_of G x' I' R' hsp' hall, ?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.LowlinkCall
