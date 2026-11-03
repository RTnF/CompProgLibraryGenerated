import Proofs.BellmanFordPrepare
import Proofs.BellmanFordBridge
import Proofs.BellmanFordParent
import Proofs.MultiVecCall

namespace Proofs.BellmanFordCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.BellmanFordPrepare Proofs.BellmanFordExec Proofs.BellmanFordMath Proofs.BellmanFordBridge
open Proofs.BellmanFordPExec Proofs.BellmanFordParent
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)

/-- The callee of `bellman_ford`: the flat vectors `from`, `to` (`int`), `cost`, `dist` (`long long`) and `parent` (`int`);
the last two are writable. -/
def mvBF (V0 V1 V2 V3 V4 vsc0 vsc1 vsc2 vsc3 vsc4 : Nat) (m0 m1 m2 : Bool) (L0 T0 sc N : Nat) (h03 : V0 ≠ V3) (h13 : V1 ≠ V3)
    (h23 : V2 ≠ V3) (h04 : V0 ≠ V4) (h14 : V1 ≠ V4) (h24 : V2 ≠ V4) (h34 : V3 ≠ V4) : MV where
  nv := 5
  ty := fun k => if k = 2 ∨ k = 3 then s64 else i32
  wV := fun k => decide (k = 3 ∨ k = 4)
  flag := fun k => if k = 0 then m0 else if k = 1 then m1 else if k = 2 then m2 else true
  R := fun k => if k = 0 then V0 else if k = 1 then V1 else if k = 2 then V2 else if k = 3 then V3 else V4
  vsc := fun k => if k = 0 then vsc0 else if k = 1 then vsc1 else if k = 2 then vsc2 else if k = 3 then vsc3 else vsc4
  perm := by
    intro k hk
    have : k = 3 ∨ k = 4 := by simpa using hk
    rcases this with rfl | rfl <;> simp
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk hw
    have : k = 3 ∨ k = 4 := by simpa using hw
    rcases this with rfl | rfl
    · have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · simpa using h03
      · simpa using h13
      · simpa using h23
      · simpa using h34.symm
    · have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · simpa using h04
      · simpa using h14
      · simpa using h24
      · simpa using h34

def bbBF (b0 b1 b2 b3 b4 : Buffer Value) : Nat → Buffer Value :=
  fun k => if k = 0 then b0 else if k = 1 then b1 else if k = 2 then b2 else if k = 3 then b3 else b4

theorem body_eqBF5 : Proofs.BellmanFordInstance.bellman_ford_std_vector_int.body = bodyBFP 5 := rfl

theorem wr_bodyBF : WrM (fun k => decide (k = 3 ∨ k = 4)) (bodyBFP 5) = true := by decide

theorem cases5 (k : Nat) (hk : k < 5) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega


/-- The frame facts at entry of `bellman_ford` (before any work). -/
theorem fwBF_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 s4 vb4 V4 vsc4 : Nat} {m0 m1 m2 : Bool}
    {vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller s64 s2 vb2 V2 vsc2 false m2 vbuf2) (ok3 : VOKG caller s64 s3 vb3 V3 vsc3 true true vbuf3)
    (ok4 : VOKG caller i32 s4 vb4 V4 vsc4 true true vbuf4)
    (h03 : V0 ≠ V3) (h13 : V1 ≠ V3) (h23 : V2 ≠ V3) (h04 : V0 ≠ V4) (h14 : V1 ≠ V4) (h24 : V2 ≠ V4) (h34 : V3 ≠ V4)
    (F T : List Nat) (Cc D Pp : List Int) (m n : Nat) (hFl : F.length = m) (hTl : T.length = m) (hCl : Cc.length = m)
    (hDl : D.length = n) (hPl : Pp.length = n) (hm : m < 2147483647) (hn : n < 2147483647)
    (i0 : vbuf0.items = (F.map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = (T.map (fun x : Nat => (x : Int))).map Value.integer)
    (i2 : vbuf2.items = Cc.map Value.integer) (i3 : vbuf3.items = D.map Value.integer) (i4 : vbuf4.items = Pp.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (bv2 : vbuf2.Valid (accepts (.integer s64))) (bv3 : vbuf3.Valid (accepts (.integer s64)))
    (bv4 : vbuf4.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit s64) (l3 : vbuf3.limit = CppVectorBindings.sizeLimit s64)
    (l4 : vbuf4.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) (o3 : vbuf3.owner = V3) (o4 : vbuf4.owner = V4) :
    FWM (mvBF V0 V1 V2 V3 V4 vsc0 vsc1 vsc2 vsc3 vsc4 m0 m1 m2 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h03 h13 h23 h04 h14 h24 h34)
      (VVP F T Cc D Pp) (bbBF vbuf0 vbuf1 vbuf2 vbuf3 vbuf4) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer i32,false,.root vsc0⟩,⟨V1,.integer i32,false,.root vsc1⟩,⟨V2,.integer s64,false,.root vsc2⟩,
         ⟨V3,.integer s64,true,.root vsc3⟩,⟨V4,.integer i32,true,.root vsc4⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvBF] using ok0.vtag
    · simpa [mvBF] using ok1.vtag
    · simpa [mvBF] using ok2.vtag
    · simpa [mvBF] using ok3.vtag
    · simpa [mvBF] using ok4.vtag
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvBF, bbBF] using ok0.vfound
    · simpa [mvBF, bbBF] using ok1.vfound
    · simpa [mvBF, bbBF] using ok2.vfound
    · simpa [mvBF, bbBF] using ok3.vfound
    · simpa [mvBF, bbBF] using ok4.vfound
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvBF] using ok0.flag
    · simpa [mvBF] using ok1.flag
    · simpa [mvBF] using ok2.flag
    · simpa [mvBF] using ok3.flag
    · simpa [mvBF] using ok4.flag
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvBF, bbBF, VVP] using i0
    · simpa [mvBF, bbBF, VVP] using i1
    · simpa [mvBF, bbBF, VVP] using i2
    · simpa [mvBF, bbBF, VVP] using i3
    · simpa [mvBF, bbBF, VVP] using i4
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvBF, bbBF] using bv0
    · simpa [mvBF, bbBF] using bv1
    · simpa [mvBF, bbBF] using bv2
    · simpa [mvBF, bbBF] using bv3
    · simpa [mvBF, bbBF] using bv4
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvBF, bbBF] using l0
    · simpa [mvBF, bbBF] using l1
    · simpa [mvBF, bbBF] using l2
    · simpa [mvBF, bbBF] using l3
    · simpa [mvBF, bbBF] using l4
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvBF, bbBF] using o0
    · simpa [mvBF, bbBF] using o1
    · simpa [mvBF, bbBF] using o2
    · simpa [mvBF, bbBF] using o3
    · simpa [mvBF, bbBF] using o4
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simp [VVP, hFl]; omega
    · simp [VVP, hTl]; omega
    · simp [VVP, hCl]; omega
    · simp [VVP, hDl]; omega
    · simp [VVP, hPl]; omega

set_option maxHeartbeats 4000000 in
/-- `cp::bellman_ford(from, to, cost, dist, parent, n, inf)`: `n - 1` passes of edge relaxation (recording the parents), then `n`
passes marking the vertices reached through a negative cycle with `-inf`. -/
theorem bellman_ford_correct (caller : NState)
    {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 s4 vb4 V4 vsc4 : Nat}
    {m0 m1 m2 : Bool} {vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller s64 s2 vb2 V2 vsc2 false m2 vbuf2) (ok3 : VOKG caller s64 s3 vb3 V3 vsc3 true true vbuf3)
    (ok4 : VOKG caller i32 s4 vb4 V4 vsc4 true true vbuf4)
    (h03 : V0 ≠ V3) (h13 : V1 ≠ V3) (h23 : V2 ≠ V3) (h04 : V0 ≠ V4) (h14 : V1 ≠ V4) (h24 : V2 ≠ V4) (h34 : V3 ≠ V4)
    (F T : List Nat) (Cc D P0 : List Int) (n : Nat) (inf Cb lo : Int)
    (hn1 : 1 ≤ n) (hn : n < 2147483647) (hFl : T.length = F.length) (hCl : Cc.length = F.length)
    (hm : F.length < 2147483647) (hDl : D.length = n) (hPl : P0.length = n) (hP0 : ∀ x ∈ P0, x = -1)
    (hFn : ∀ x ∈ F, x < n) (hTn : ∀ x ∈ T, x < n)
    (b : Bnd inf Cb lo F.length Cc D) (hinf0 : 0 ≤ inf)
    (hloR : -4611686018427387904 ≤ lo - ((n - 1 : Nat) : Int) * ((F.length : Int) * Cb))
    (hloS : -inf < lo - ((n - 1 : Nat) : Int) * ((F.length : Int) * Cb))
    (i0 : vbuf0.items = (F.map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = (T.map (fun x : Nat => (x : Int))).map Value.integer)
    (i2 : vbuf2.items = Cc.map Value.integer) (i3 : vbuf3.items = D.map Value.integer) (i4 : vbuf4.items = P0.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (bv2 : vbuf2.Valid (accepts (.integer s64))) (bv3 : vbuf3.Valid (accepts (.integer s64)))
    (bv4 : vbuf4.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit s64) (l3 : vbuf3.limit = CppVectorBindings.sizeLimit s64)
    (l4 : vbuf4.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) (o3 : vbuf3.owner = V3) (o4 : vbuf4.owner = V4)
    (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (ty1 : e1.resultType = i32)
    (ty2 : e2.resultType = s64) (value1 : e1.denote (envOf caller) = some (n : Int))
    (value2 : e2.denote (envOf caller) = some inf) (hinf : s64.valid inf = true) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (D1 P1 D' P' : List Int),
      prepare caller Proofs.BellmanFordInstance.bellman_ford_std_vector_int.parameters
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.vectorReference s4,.value e1,.value e2] =
        some Sinit ∧
      Proofs.BellmanFordInstance.bellman_ford_std_vector_int.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.vectorReference s4,.value e1,.value e2] =
        .finished (res,Ret.unit) ∧
      D1 = roundsL inf F T Cc F.length (n - 1) D ∧ P1 = roundsPL inf F T Cc F.length (n - 1) D P0 ∧
      (D', P') = markRounds inf F T Cc F.length n (D1, P1) ∧ D1.length = n ∧ P1.length = n ∧ D'.length = n ∧ P'.length = n ∧
      (∀ v, D1.getD v 0 ≠ inf → ∃ w c k, D.getD w 0 ≠ inf ∧ Walk (edgesOf F T Cc F.length) w v c k ∧
        D1.getD v 0 = D.getD w 0 + c) ∧
      ((∀ w v c k, k ≤ n - 1 → Walk (edgesOf F T Cc F.length) w v c k → D.getD w 0 < inf → D.getD w 0 + c < inf) →
        ∀ w v c k, k ≤ n - 1 → D.getD w 0 < inf → Walk (edgesOf F T Cc F.length) w v c k → D1.getD v 0 ≤ D.getD w 0 + c) ∧
      ParInvE inf F T Cc F.length D1 P1 ∧
      (Stable inf F T Cc F.length D1 → D' = D1 ∧ P' = P1) ∧
      ScalarPostM (mvBF V0 V1 V2 V3 V4 vsc0 vsc1 vsc2 vsc3 vsc4 m0 m1 m2 caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h03 h13 h23 h04 h14 h24 h34)
        caller Sinit res (e1.nodes + e2.nodes) ((970 * F.length + 50) * (n - 1) + (970 * F.length + 50) * n + 300)
        caller.scalars.memory (2 * F.length * (n - 1) + 2 * F.length * n) (VVP F T Cc D' P') := by
  have hn32 : n < 2147483648 := by omega
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_bf caller ok0 ok1 ok2 ok3 ok4 e1 e2 (n : Int) inf hs1 hs2 ty1 ty2 value1 value2 (validN n hn32) hinf
  have fwS := fwBF_init caller ok0 ok1 ok2 ok3 ok4 h03 h13 h23 h04 h14 h24 h34 F T Cc D P0 F.length n rfl hFl hCl hDl hPl hm hn
    i0 i1 i2 i3 i4 bv0 bv1 bv2 bv3 bv4 l0 l1 l2 l3 l4 o0 o1 o2 o3 o4
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrps,hrvv,hcost,hneed,hwk⟩ :=
    body_execP (mvBF V0 V1 V2 V3 V4 vsc0 vsc1 vsc2 vsc3 vsc4 m0 m1 m2 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h03 h13 h23 h04 h14 h24 h34) rfl (by simp [mvBF]) (by simp [mvBF])
      (by simp [mvBF]) (by simp [mvBF]) (by simp [mvBF]) F T Cc D P0 (callerP caller) n F.length inf Cb lo hn32 hn hn1 hm hinf hinf0 rfl hFl hCl
      hFn hTn hDl hPl b hloR (F.length + 1 + n + 1) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),(⟨s64,inf⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),(⟨s64,inf⟩ : Cell)],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]⟩ : PS) = gS (callerP caller) [ci n, cs inf] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2
  have hpost := call_vecm_unit (mvBF V0 V1 V2 V3 V4 vsc0 vsc1 vsc2 vsc3 vsc4 m0 m1 m2 caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h03 h13 h23 h04 h14 h24 h34)
    (fun k => decide (k = 3 ∨ k = 4))
    (by intro k hk; have : k = 3 ∨ k = 4 := by simpa using hk
        rcases this with rfl | rfl <;> simp [mvBF])
    caller Proofs.BellmanFordInstance.bellman_ford_std_vector_int
    [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.vectorReference s4,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),(⟨s64,inf⟩ : Cell)])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [body_eqBF5]; exact wr_bodyBF)
    (F.length + 1 + n + 1) rr (by rw [hmk, body_eqBF5]; exact hexec) hret rfl (by omega)
    (by simp [hlenP]) (e1.nodes + e2.nodes) ((970 * F.length + 50) * (n - 1) + (970 * F.length + 50) * n + 300) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  have hsp := bf_spec inf F T Cc D n F.length hFl hTn hDl
  have hle0 : ∀ x ∈ D, x ≤ inf := fun x hx => (b.d0 x hx).2
  have hpar := (rounds_par inf F T Cc F.length n D P0 hFl hTn rfl hFn hDl hPl hle0 (parInv_init inf F T Cc F.length D P0 hP0)
    (n - 1)).1
  have hlen2 : (roundsPL inf F T Cc F.length (n - 1) D P0).length = n := by rw [roundsPL_length, hPl]
  have hneg1 : ∀ x ∈ roundsL inf F T Cc F.length (n - 1) D, x ≠ -inf := by
    intro x hx hxe
    have := roundsL_bound inf Cb lo F T Cc D n F.length rfl hFl hCl hFn hTn hDl b.cb0 b.cc b.d0 (n - 1) x hx
    omega
  refine ⟨Sinit,fuel,res,roundsL inf F T Cc F.length (n - 1) D, roundsPL inf F T Cc F.length (n - 1) D P0,
    (markRounds inf F T Cc F.length n (roundsL inf F T Cc F.length (n - 1) D, roundsPL inf F T Cc F.length (n - 1) D P0)).1,
    (markRounds inf F T Cc F.length n (roundsL inf F T Cc F.length (n - 1) D, roundsPL inf F T Cc F.length (n - 1) D P0)).2,
    hprep,hrun,rfl,rfl,rfl,hsp.1,hlen2,?_,?_,hsp.2.1,hsp.2.2,hpar,?_,?_⟩
  · rw [markRounds_len1]; exact hsp.1
  · rw [markRounds_len2]; exact hlen2
  · intro hst
    have := markRounds_id inf F T Cc F.length n _ (roundsPL inf F T Cc F.length (n - 1) D P0) rfl hFn hsp.1 hst hneg1 n
    rw [this]; exact ⟨rfl, rfl⟩
  · have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
      rw [hrps]
      simp only [gS_mem, callerP, List.append_assoc]
      rw [List.take_append_of_le_length (by simp)]
      exact List.take_length
    rw [hs', hrvv] at post
    exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.BellmanFordCall
