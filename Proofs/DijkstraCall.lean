import Proofs.DijkstraPrepare
import Proofs.DijkstraExec
import Proofs.MultiVecCall

namespace Proofs.DijkstraCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.DijkstraPrepare Proofs.DijkstraExec Proofs.DijkstraScan
open Proofs.DijkstraPMath (ofFnI)
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)

/-- The callee of `dijkstra`: `head`, `target` (`int`), `cost` (`long long`) read-only; `dist` (`long long`) and `done` (`int`) writable. -/
def mvDJ (V0 V1 V2 V3 V4 V5 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 : Nat) (m0 m1 m2 : Bool) (L0 T0 sc N : Nat) (h03 : V0 ≠ V3)
    (h13 : V1 ≠ V3) (h23 : V2 ≠ V3) (h04 : V0 ≠ V4) (h14 : V1 ≠ V4) (h24 : V2 ≠ V4) (h34 : V3 ≠ V4)
    (h05 : V0 ≠ V5) (h15 : V1 ≠ V5) (h25 : V2 ≠ V5) (h35 : V3 ≠ V5) (h45 : V4 ≠ V5) : MV where
  nv := 6
  ty := fun k => if k = 2 ∨ k = 3 then s64 else i32
  wV := fun k => decide (k = 3 ∨ k = 4 ∨ k = 5)
  flag := fun k => if k = 0 then m0 else if k = 1 then m1 else if k = 2 then m2 else true
  R := fun k => if k = 0 then V0 else if k = 1 then V1 else if k = 2 then V2 else if k = 3 then V3 else if k = 4 then V4 else V5
  vsc := fun k => if k = 0 then vsc0 else if k = 1 then vsc1 else if k = 2 then vsc2 else if k = 3 then vsc3
    else if k = 4 then vsc4 else vsc5
  perm := by
    intro k hk
    have : k = 3 ∨ k = 4 ∨ k = 5 := by simpa using hk
    rcases this with rfl | rfl | rfl <;> simp
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk hw
    have : k = 3 ∨ k = 4 ∨ k = 5 := by simpa using hw
    rcases this with rfl | rfl | rfl
    · have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 4 ∨ j = 5 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · simpa using h03
      · simpa using h13
      · simpa using h23
      · simpa using h34.symm
      · simpa using h35.symm
    · have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 5 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · simpa using h04
      · simpa using h14
      · simpa using h24
      · simpa using h34
      · simpa using h45.symm
    · have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 := by omega
      rcases this with rfl | rfl | rfl | rfl | rfl
      · simpa using h05
      · simpa using h15
      · simpa using h25
      · simpa using h35
      · simpa using h45

def bbDJ (b0 b1 b2 b3 b4 b5 : Buffer Value) : Nat → Buffer Value :=
  fun k => if k = 0 then b0 else if k = 1 then b1 else if k = 2 then b2 else if k = 3 then b3 else if k = 4 then b4 else b5

theorem body_eqDJ5 : Proofs.DijkstraInstance.dijkstra_std_vector_int.body = bodyDJ 6 := rfl

theorem wr_bodyDJ : WrM (fun k => decide (k = 3 ∨ k = 4 ∨ k = 5)) (bodyDJ 6) = true := by decide

theorem cases6 (k : Nat) (hk : k < 6) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 := by omega


/-- The frame facts at entry of `dijkstra` (before any work). -/
theorem fwDJ_init (caller : NState)
    {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 s4 vb4 V4 vsc4 s5 vb5 V5 vsc5 : Nat} {m0 m1 m2 : Bool}
    {vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 vbuf5 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller s64 s2 vb2 V2 vsc2 false m2 vbuf2) (ok3 : VOKG caller s64 s3 vb3 V3 vsc3 true true vbuf3)
    (ok4 : VOKG caller i32 s4 vb4 V4 vsc4 true true vbuf4) (ok5 : VOKG caller i32 s5 vb5 V5 vsc5 true true vbuf5)
    (h03 : V0 ≠ V3) (h13 : V1 ≠ V3) (h23 : V2 ≠ V3) (h04 : V0 ≠ V4) (h14 : V1 ≠ V4) (h24 : V2 ≠ V4) (h34 : V3 ≠ V4)
    (h05 : V0 ≠ V5) (h15 : V1 ≠ V5) (h25 : V2 ≠ V5) (h35 : V3 ≠ V5) (h45 : V4 ≠ V5)
    (H T : List Nat) (C Dd : List Int) (Dn : List Nat) (Pp : List Int) (hHl : H.length < 2147483647) (hTl : T.length < 2147483647)
    (hCl : C.length < 2147483647) (hDl : Dd.length < 2147483647) (hNl : Dn.length < 2147483647) (hPl : Pp.length < 2147483647)
    (i0 : vbuf0.items = (H.map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = (T.map (fun x : Nat => (x : Int))).map Value.integer)
    (i2 : vbuf2.items = C.map Value.integer) (i3 : vbuf3.items = Dd.map Value.integer)
    (i4 : vbuf4.items = (Dn.map (fun x : Nat => (x : Int))).map Value.integer) (i5 : vbuf5.items = Pp.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (bv2 : vbuf2.Valid (accepts (.integer s64))) (bv3 : vbuf3.Valid (accepts (.integer s64)))
    (bv4 : vbuf4.Valid (accepts (.integer i32))) (bv5 : vbuf5.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit s64) (l3 : vbuf3.limit = CppVectorBindings.sizeLimit s64)
    (l4 : vbuf4.limit = CppVectorBindings.sizeLimit i32) (l5 : vbuf5.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) (o3 : vbuf3.owner = V3) (o4 : vbuf4.owner = V4) (o5 : vbuf5.owner = V5) :
    FWM (mvDJ V0 V1 V2 V3 V4 V5 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 m0 m1 m2 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h03 h13 h23 h04 h14 h24 h34 h05 h15 h25 h35 h45)
      (VDP H T C Dd Dn Pp) (bbDJ vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 vbuf5) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer i32,false,.root vsc0⟩,⟨V1,.integer i32,false,.root vsc1⟩,⟨V2,.integer s64,false,.root vsc2⟩,
         ⟨V3,.integer s64,true,.root vsc3⟩,⟨V4,.integer i32,true,.root vsc4⟩,⟨V5,.integer i32,true,.root vsc5⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases6 k hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvDJ] using ok0.vtag
    · simpa [mvDJ] using ok1.vtag
    · simpa [mvDJ] using ok2.vtag
    · simpa [mvDJ] using ok3.vtag
    · simpa [mvDJ] using ok4.vtag
    · simpa [mvDJ] using ok5.vtag
  · intro k hk
    rcases cases6 k hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvDJ, bbDJ] using ok0.vfound
    · simpa [mvDJ, bbDJ] using ok1.vfound
    · simpa [mvDJ, bbDJ] using ok2.vfound
    · simpa [mvDJ, bbDJ] using ok3.vfound
    · simpa [mvDJ, bbDJ] using ok4.vfound
    · simpa [mvDJ, bbDJ] using ok5.vfound
  · intro k hk
    rcases cases6 k hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvDJ] using ok0.flag
    · simpa [mvDJ] using ok1.flag
    · simpa [mvDJ] using ok2.flag
    · simpa [mvDJ] using ok3.flag
    · simpa [mvDJ] using ok4.flag
    · simpa [mvDJ] using ok5.flag
  · intro k hk
    rcases cases6 k hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvDJ, bbDJ, VDP] using i0
    · simpa [mvDJ, bbDJ, VDP] using i1
    · simpa [mvDJ, bbDJ, VDP] using i2
    · simpa [mvDJ, bbDJ, VDP] using i3
    · simpa [mvDJ, bbDJ, VDP] using i4
    · simpa [mvDJ, bbDJ, VDP] using i5
  · intro k hk
    rcases cases6 k hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvDJ, bbDJ] using bv0
    · simpa [mvDJ, bbDJ] using bv1
    · simpa [mvDJ, bbDJ] using bv2
    · simpa [mvDJ, bbDJ] using bv3
    · simpa [mvDJ, bbDJ] using bv4
    · simpa [mvDJ, bbDJ] using bv5
  · intro k hk
    rcases cases6 k hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvDJ, bbDJ] using l0
    · simpa [mvDJ, bbDJ] using l1
    · simpa [mvDJ, bbDJ] using l2
    · simpa [mvDJ, bbDJ] using l3
    · simpa [mvDJ, bbDJ] using l4
    · simpa [mvDJ, bbDJ] using l5
  · intro k hk
    rcases cases6 k hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvDJ, bbDJ] using o0
    · simpa [mvDJ, bbDJ] using o1
    · simpa [mvDJ, bbDJ] using o2
    · simpa [mvDJ, bbDJ] using o3
    · simpa [mvDJ, bbDJ] using o4
    · simpa [mvDJ, bbDJ] using o5
  · intro k hk
    rcases cases6 k hk with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [VDP]; omega
    · simp [VDP]; omega
    · simp [VDP]; omega
    · simp [VDP]; omega
    · simp [VDP]; omega
    · simp [VDP]; omega


theorem ofFnI_self (P0 : List Int) (n : Nat) (h : P0.length = n) : ofFnI n (fun j => P0.getD j 0) = P0 := by
  apply List.ext_getElem
  · simp [ofFnI, h]
  · intro j h1 h2
    have hj : j < n := by simpa [ofFnI] using h1
    simp only [ofFnI, List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl

theorem ofFn_self (Dd : List Int) (n : Nat) (inf : Int) (h : Dd.length = n) : ofFn n (fun j => Dd.getD j inf) = Dd := by
  apply List.ext_getElem
  · simp [ofFn, h]
  · intro j h1 h2
    have hj : j < n := by simpa [ofFn] using h1
    simp only [ofFn, List.getElem_map, List.getElem_range]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl

theorem doneOf_nil (n : Nat) : doneOf n [] = List.replicate n 0 := by
  apply List.ext_getElem
  · simp [doneOf]
  · intro j h1 h2
    simp [doneOf]

open Proofs.BellmanFordMath (Sound Walk)
open Proofs.DijkstraMath (Eall dijkstra_spec)

set_option maxHeartbeats 8000000 in
/-- `cp::dijkstra(head, target, cost, dist, done, n, inf)` (array version, `O(n^2 + m)`). -/
theorem dijkstra_correct (caller : NState)
    {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 s4 vb4 V4 vsc4 s5 vb5 V5 vsc5 : Nat} {m0 m1 m2 : Bool}
    {vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 vbuf5 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller s64 s2 vb2 V2 vsc2 false m2 vbuf2) (ok3 : VOKG caller s64 s3 vb3 V3 vsc3 true true vbuf3)
    (ok4 : VOKG caller i32 s4 vb4 V4 vsc4 true true vbuf4) (ok5 : VOKG caller i32 s5 vb5 V5 vsc5 true true vbuf5)
    (h03 : V0 ≠ V3) (h13 : V1 ≠ V3) (h23 : V2 ≠ V3) (h04 : V0 ≠ V4) (h14 : V1 ≠ V4) (h24 : V2 ≠ V4) (h34 : V3 ≠ V4)
    (h05 : V0 ≠ V5) (h15 : V1 ≠ V5) (h25 : V2 ≠ V5) (h35 : V3 ≠ V5) (h45 : V4 ≠ V5)
    (H T : List Nat) (C Dd0 P0 : List Int) (n : Nat) (inf lo : Int) (hn : n < 2147483646) (hTM : T.length < 2147483647)
    (HK : Proofs.TopoSortMath.HeadOK H T n) (hTn : ∀ x ∈ T, x < n) (hCl : C.length = T.length) (hDl : Dd0.length = n) (hPl : P0.length = n)
    (hC0 : ∀ x ∈ C, 0 ≤ x ∧ x ≤ 2305843009213693952) (hinfv : s64.valid inf = true)
    (hlo : -4611686018427387904 ≤ lo) (hinfB : inf ≤ 4611686018427387904) (hbnd : ∀ x ∈ Dd0, lo ≤ x ∧ x ≤ inf)
    (i0 : vbuf0.items = (H.map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = (T.map (fun x : Nat => (x : Int))).map Value.integer)
    (i2 : vbuf2.items = C.map Value.integer) (i3 : vbuf3.items = Dd0.map Value.integer)
    (i4 : vbuf4.items = ((List.replicate n 0).map (fun x : Nat => (x : Int))).map Value.integer)
    (i5 : vbuf5.items = P0.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (bv2 : vbuf2.Valid (accepts (.integer s64))) (bv3 : vbuf3.Valid (accepts (.integer s64)))
    (bv4 : vbuf4.Valid (accepts (.integer i32))) (bv5 : vbuf5.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit s64) (l3 : vbuf3.limit = CppVectorBindings.sizeLimit s64)
    (l4 : vbuf4.limit = CppVectorBindings.sizeLimit i32) (l5 : vbuf5.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) (o3 : vbuf3.owner = V3) (o4 : vbuf4.owner = V4) (o5 : vbuf5.owner = V5)
    (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (ty1 : e1.resultType = i32)
    (ty2 : e2.resultType = s64) (value1 : e1.denote (envOf caller) = some (n : Int))
    (value2 : e2.denote (envOf caller) = some inf) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (f' : Nat → Int) (D' : List Nat) (p' : Nat → Int),
      (f', D') = Proofs.DijkstraMath.djIter inf (outEdges H T C) n (fun j => Dd0.getD j inf) n ∧
      p' = Proofs.DijkstraPMath.pIter inf (outEdges H T C) n (fun j => Dd0.getD j inf) (fun j => P0.getD j 0) n ∧
      prepare caller Proofs.DijkstraInstance.dijkstra_std_vector_int.parameters
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.vectorReference s4,.vectorReference s5,
         .value e1,.value e2] = some Sinit ∧
      Proofs.DijkstraInstance.dijkstra_std_vector_int.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.vectorReference s4,.vectorReference s5,
         .value e1,.value e2] = .finished (res,Ret.unit) ∧
      Sound inf (Eall n (outEdges H T C)) (fun j => Dd0.getD j inf) f' ∧
      ((∀ w y c k, (fun j => Dd0.getD j inf) w < inf → Walk (Eall n (outEdges H T C)) w y c k →
          (fun j => Dd0.getD j inf) w + c < inf) →
        ∀ w y c k, (fun j => Dd0.getD j inf) w < inf → Walk (Eall n (outEdges H T C)) w y c k →
          f' y ≤ (fun j => Dd0.getD j inf) w + c) ∧
      Proofs.DijkstraPMath.ParInv (outEdges H T C) D' f' p' (fun j => P0.getD j 0) ∧
      ScalarPostM (mvDJ V0 V1 V2 V3 V4 V5 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 m0 m1 m2 caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h03 h13 h23 h04 h14 h24 h34 h05 h15 h25 h35 h45)
        caller Sinit res (e1.nodes + e2.nodes) ((320 * n + 420 * T.length + 420) * n + 150) caller.scalars.memory
        ((2 * T.length + 1) * n) (VDP H T C (ofFn n f') (doneOf n D') (ofFnI n p')) := by
  have hn32 : n < 2147483648 := by omega
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_dj caller ok0 ok1 ok2 ok3 ok4 ok5 e1 e2 (n : Int) inf hs1 hs2 ty1 ty2 value1 value2 (validN n hn32) hinfv
  have hHl : H.length < 2147483647 := by rw [HK.len]; omega
  have hDnl : (doneOf n []).length < 2147483647 := by rw [doneOf_length]; omega
  have hDl' : Dd0.length < 2147483647 := by omega
  have hCl' : C.length < 2147483647 := by omega
  have hdoneL : doneOf n [] = List.replicate n 0 := doneOf_nil n
  have hPl' : P0.length < 2147483647 := by omega
  have fwS := fwDJ_init caller ok0 ok1 ok2 ok3 ok4 ok5 h03 h13 h23 h04 h14 h24 h34 h05 h15 h25 h35 h45 H T C Dd0 (doneOf n []) P0 hHl hTM hCl' hDl' hDnl hPl' i0 i1 i2 i3
    (by rw [hdoneL]; exact i4) i5 bv0 bv1 bv2 bv3 bv4 bv5 l0 l1 l2 l3 l4 l5 o0 o1 o2 o3 o4 o5
  rw [← sFrame] at fwS
  obtain ⟨f0, hf0⟩ : ∃ f0 : Nat → Int, f0 = fun j => Dd0.getD j inf := ⟨_, rfl⟩
  obtain ⟨p0, hp0⟩ : ∃ p0 : Nat → Int, p0 = fun j => P0.getD j 0 := ⟨_, rfl⟩
  have hDeq : ofFn n f0 = Dd0 := by rw [hf0]; exact ofFn_self Dd0 n inf hDl
  have hPeq : ofFnI n p0 = P0 := by rw [hp0]; exact ofFnI_self P0 n hPl
  have fwS' : FWM (mvDJ V0 V1 V2 V3 V4 V5 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 m0 m1 m2 caller.frame.state.liveSpace
      caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h03 h13 h23 h04 h14 h24 h34 h05 h15 h25 h35 h45)
      (VDP H T C (ofFn n f0) (doneOf n []) (ofFnI n p0)) (bbDJ vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 vbuf5) 0 Sinit.frame := by
    rw [hDeq, hPeq]; exact fwS
  have hbnd0 : ∀ j, j < n → lo ≤ f0 j ∧ f0 j ≤ inf := by
    intro j hj
    rw [hf0]
    show lo ≤ Dd0.getD j inf ∧ Dd0.getD j inf ≤ inf
    have hm : Dd0.getD j inf ∈ Dd0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact List.getElem_mem _
    exact hbnd _ hm
  have hd0 : ∀ w, f0 w < inf → w < n := by
    intro w hw
    by_cases h : w < n
    · exact h
    · exfalso
      have hw' : Dd0.getD w inf < inf := by rw [hf0] at hw; exact hw
      have : Dd0.getD w inf = inf := getD_oob _ _ _ (by omega)
      omega
  obtain ⟨rr,hexec,hret,hrps,hrvv,hcost,hneed,hwk⟩ :=
    body_exec (mvDJ V0 V1 V2 V3 V4 V5 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 m0 m1 m2 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h03 h13 h23 h04 h14 h24 h34 h05 h15 h25 h35 h45) rfl (by simp [mvDJ]) (by simp [mvDJ])
      (by simp [mvDJ]) (by simp [mvDJ]) (by simp [mvDJ]) (by simp [mvDJ]) H T C (callerP caller) n inf lo f0 p0 hn32 (by omega) HK hTn hTM hCl hC0 hinfv
      hlo hinfB hbnd0 (2 * n + T.length + 6) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),(⟨s64,inf⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),(⟨s64,inf⟩ : Cell)],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]⟩ : PS) = gS (callerP caller) [ci n, Proofs.BellmanFordExec.cs inf] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2
  have hpost := call_vecm_unit (mvDJ V0 V1 V2 V3 V4 V5 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 m0 m1 m2 caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h03 h13 h23 h04 h14 h24 h34 h05 h15 h25 h35 h45)
    (fun k => decide (k = 3 ∨ k = 4 ∨ k = 5))
    (by intro k hk; have : k = 3 ∨ k = 4 ∨ k = 5 := by simpa using hk
        rcases this with rfl | rfl | rfl <;> simp [mvDJ])
    caller Proofs.DijkstraInstance.dijkstra_std_vector_int
    [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.vectorReference s4,.vectorReference s5,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell),(⟨s64,inf⟩ : Cell)])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS' rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [body_eqDJ5]; exact wr_bodyDJ)
    (2 * n + T.length + 6) rr (by rw [hmk, body_eqDJ5]; exact hexec) hret rfl (by omega)
    (by simp [hlenP]) (e1.nodes + e2.nodes) ((320 * n + 420 * T.length + 420) * n + 150) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  have G := graph_of H T C n HK hTn (fun x hx => (hC0 x hx).1)
  have hsp := dijkstra_spec n inf (outEdges H T C) G f0 hd0
  have hpi := Proofs.DijkstraPMath.pIter_inv n inf (outEdges H T C) G f0 hd0 p0 n
  subst hf0
  subst hp0
  refine ⟨Sinit,fuel,res,(Proofs.DijkstraMath.djIter inf (outEdges H T C) n (fun j => Dd0.getD j inf) n).1,
    (Proofs.DijkstraMath.djIter inf (outEdges H T C) n (fun j => Dd0.getD j inf) n).2,
    Proofs.DijkstraPMath.pIter inf (outEdges H T C) n (fun j => Dd0.getD j inf) (fun j => P0.getD j 0) n, rfl, rfl, hprep, hrun,
    hsp.1, hsp.2, hpi, ?_⟩
  · have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
      rw [hrps]
      simp only [gS_mem, callerP, List.append_assoc]
      rw [List.take_append_of_le_length (by simp)]
      exact List.take_length
    rw [hs', hrvv] at post
    exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.DijkstraCall
