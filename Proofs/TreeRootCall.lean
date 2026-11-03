import Proofs.TreeRootPrepare
import Proofs.TreeRootExec
import Proofs.MultiVecCall

namespace Proofs.TreeRootCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.TreeRootPrepare Proofs.TreeRootExec Proofs.TreeRootMath
open Proofs.TopoSortMath (HeadOK)
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)

def VfTR (V0 V1 V2 V3 V4 V5 V6 : Nat) : Nat → Nat := fun k =>
  if k = 0 then V0 else if k = 1 then V1 else if k = 2 then V2 else if k = 3 then V3 else if k = 4 then V4
  else if k = 5 then V5 else V6

/-- The callee of `tree_root`: seven flat vectors (`head`, `target` `int`, `cost` `long long`, `parent`, `depth` `int`,
`cost_depth` `long long`, `stk` `int`); the last four are writable. -/
def mvTR (V0 V1 V2 V3 V4 V5 V6 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 vsc6 : Nat) (m0 m1 m2 : Bool) (L0 T0 sc N : Nat)
    (hd : ∀ j k, j < 7 → k < 7 → j ≠ k → (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) →
      VfTR V0 V1 V2 V3 V4 V5 V6 j ≠ VfTR V0 V1 V2 V3 V4 V5 V6 k) : MV where
  nv := 7
  ty := fun k => if k = 2 ∨ k = 5 then s64 else i32
  wV := fun k => decide (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6)
  flag := fun k => if k = 0 then m0 else if k = 1 then m1 else if k = 2 then m2 else true
  R := VfTR V0 V1 V2 V3 V4 V5 V6
  vsc := fun k => if k = 0 then vsc0 else if k = 1 then vsc1 else if k = 2 then vsc2 else if k = 3 then vsc3
    else if k = 4 then vsc4 else if k = 5 then vsc5 else vsc6
  perm := by
    intro k hk
    have : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by simpa using hk
    rcases this with rfl | rfl | rfl | rfl <;> simp
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk hw
    exact hd j k hj hk hjk (by simpa using hw)

theorem hdTR (V0 V1 V2 V3 V4 V5 V6 : Nat) (h03 : V0 ≠ V3) (h04 : V0 ≠ V4) (h05 : V0 ≠ V5) (h06 : V0 ≠ V6)
    (h13 : V1 ≠ V3) (h14 : V1 ≠ V4) (h15 : V1 ≠ V5) (h16 : V1 ≠ V6)
    (h23 : V2 ≠ V3) (h24 : V2 ≠ V4) (h25 : V2 ≠ V5) (h26 : V2 ≠ V6)
    (h34 : V3 ≠ V4) (h35 : V3 ≠ V5) (h36 : V3 ≠ V6) (h45 : V4 ≠ V5) (h46 : V4 ≠ V6) (h56 : V5 ≠ V6) :
    ∀ j k, j < 7 → k < 7 → j ≠ k → (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6) →
      VfTR V0 V1 V2 V3 V4 V5 V6 j ≠ VfTR V0 V1 V2 V3 V4 V5 V6 k := by
  intro j k hj hk hjk hw
  have s03 := h03.symm; have s04 := h04.symm; have s05 := h05.symm; have s06 := h06.symm
  have s13 := h13.symm; have s14 := h14.symm; have s15 := h15.symm; have s16 := h16.symm
  have s23 := h23.symm; have s24 := h24.symm; have s25 := h25.symm; have s26 := h26.symm
  have s34 := h34.symm; have s35 := h35.symm; have s36 := h36.symm; have s45 := h45.symm; have s46 := h46.symm
  have s56 := h56.symm
  have hj7 : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases hj7 with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rcases hw with rfl | rfl | rfl | rfl <;>
    first | exact absurd rfl hjk | simpa [VfTR] using ‹_›

theorem body_eqTR7 : Proofs.TreeRootInstance.tree_root_std_vector_int.body = bodyTR 7 := rfl

theorem wr_bodyTR : WrM (fun k => decide (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6)) (bodyTR 7) = true := by decide

theorem cases7 (k : Nat) (hk : k < 7) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by omega

theorem valid_of_items (ty : Ty) (L : List Int) (vbuf : Buffer Value) (i : vbuf.items = L.map Value.integer)
    (bv : vbuf.Valid (accepts (.integer ty))) : ∀ x ∈ L, ty.valid x = true := by
  intro x hx
  have h := bv.2.2
  rw [i, List.all_eq_true] at h
  have := h (Value.integer x) (List.mem_map_of_mem hx)
  simpa [accepts] using this

def bbTR (b0 b1 b2 b3 b4 b5 b6 : Buffer Value) : Nat → Buffer Value :=
  fun k => if k = 0 then b0 else if k = 1 then b1 else if k = 2 then b2 else if k = 3 then b3 else if k = 4 then b4
    else if k = 5 then b5 else b6

/-- The frame facts at entry of `tree_root` (before any work). -/
theorem fwTR_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 s4 vb4 V4 vsc4 s5 vb5 V5 vsc5 s6 vb6 V6 vsc6} {m0 m1 m2 : Bool}
    {vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 vbuf5 vbuf6}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0)
    (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller s64 s2 vb2 V2 vsc2 false m2 vbuf2)
    (ok3 : VOKG caller i32 s3 vb3 V3 vsc3 true true vbuf3)
    (ok4 : VOKG caller i32 s4 vb4 V4 vsc4 true true vbuf4)
    (ok5 : VOKG caller s64 s5 vb5 V5 vsc5 true true vbuf5)
    (ok6 : VOKG caller i32 s6 vb6 V6 vsc6 true true vbuf6)
    (h03 : V0 ≠ V3) (h04 : V0 ≠ V4) (h05 : V0 ≠ V5) (h06 : V0 ≠ V6)
    (h13 : V1 ≠ V3) (h14 : V1 ≠ V4) (h15 : V1 ≠ V5) (h16 : V1 ≠ V6)
    (h23 : V2 ≠ V3) (h24 : V2 ≠ V4) (h25 : V2 ≠ V5) (h26 : V2 ≠ V6)
    (h34 : V3 ≠ V4) (h35 : V3 ≠ V5) (h36 : V3 ≠ V6) (h45 : V4 ≠ V5) (h46 : V4 ≠ V6) (h56 : V5 ≠ V6)
    (H T : List Nat) (Cs par dep cd Stk : List Int)
    (hH : H.length < 2147483647) (hT : T.length < 2147483647) (hCs : Cs.length < 2147483647)
    (hP : par.length < 2147483647) (hD : dep.length < 2147483647) (hC : cd.length < 2147483647)
    (hS : Stk.length < 2147483647)
    (i0 : vbuf0.items = (H.map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = (T.map (fun x : Nat => (x : Int))).map Value.integer)
    (i2 : vbuf2.items = Cs.map Value.integer)
    (i3 : vbuf3.items = par.map Value.integer)
    (i4 : vbuf4.items = dep.map Value.integer)
    (i5 : vbuf5.items = cd.map Value.integer)
    (i6 : vbuf6.items = Stk.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32)))
    (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (bv2 : vbuf2.Valid (accepts (.integer s64)))
    (bv3 : vbuf3.Valid (accepts (.integer i32)))
    (bv4 : vbuf4.Valid (accepts (.integer i32)))
    (bv5 : vbuf5.Valid (accepts (.integer s64)))
    (bv6 : vbuf6.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32)
    (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit s64)
    (l3 : vbuf3.limit = CppVectorBindings.sizeLimit i32)
    (l4 : vbuf4.limit = CppVectorBindings.sizeLimit i32)
    (l5 : vbuf5.limit = CppVectorBindings.sizeLimit s64)
    (l6 : vbuf6.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0)
    (o1 : vbuf1.owner = V1)
    (o2 : vbuf2.owner = V2)
    (o3 : vbuf3.owner = V3)
    (o4 : vbuf4.owner = V4)
    (o5 : vbuf5.owner = V5)
    (o6 : vbuf6.owner = V6) :
    FWM (mvTR V0 V1 V2 V3 V4 V5 V6 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 vsc6 m0 m1 m2 caller.frame.state.liveSpace caller.frame.state.storage.work
    (caller.scope + 1) caller.frame.state.storage.objects.length (hdTR V0 V1 V2 V3 V4 V5 V6 h03 h04 h05 h06 h13 h14 h15 h16 h23 h24 h25 h26 h34 h35 h36 h45 h46 h56))
      (VR H T Cs par dep cd Stk) (bbTR vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 vbuf5 vbuf6) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer i32,false,.root vsc0⟩,⟨V1,.integer i32,false,.root vsc1⟩,⟨V2,.integer s64,false,.root vsc2⟩,⟨V3,.integer i32,true,.root vsc3⟩,⟨V4,.integer i32,true,.root vsc4⟩,⟨V5,.integer s64,true,.root vsc5⟩,⟨V6,.integer i32,true,.root vsc6⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases7 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvTR, VfTR] using ok0.vtag
    · simpa [mvTR, VfTR] using ok1.vtag
    · simpa [mvTR, VfTR] using ok2.vtag
    · simpa [mvTR, VfTR] using ok3.vtag
    · simpa [mvTR, VfTR] using ok4.vtag
    · simpa [mvTR, VfTR] using ok5.vtag
    · simpa [mvTR, VfTR] using ok6.vtag
  · intro k hk
    rcases cases7 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvTR, VfTR, bbTR] using ok0.vfound
    · simpa [mvTR, VfTR, bbTR] using ok1.vfound
    · simpa [mvTR, VfTR, bbTR] using ok2.vfound
    · simpa [mvTR, VfTR, bbTR] using ok3.vfound
    · simpa [mvTR, VfTR, bbTR] using ok4.vfound
    · simpa [mvTR, VfTR, bbTR] using ok5.vfound
    · simpa [mvTR, VfTR, bbTR] using ok6.vfound
  · intro k hk
    rcases cases7 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvTR, VfTR] using ok0.flag
    · simpa [mvTR, VfTR] using ok1.flag
    · simpa [mvTR, VfTR] using ok2.flag
    · simpa [mvTR, VfTR] using ok3.flag
    · simpa [mvTR, VfTR] using ok4.flag
    · simpa [mvTR, VfTR] using ok5.flag
    · simpa [mvTR, VfTR] using ok6.flag
  · intro k hk
    rcases cases7 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvTR, VfTR, bbTR, VR] using i0
    · simpa [mvTR, VfTR, bbTR, VR] using i1
    · simpa [mvTR, VfTR, bbTR, VR] using i2
    · simpa [mvTR, VfTR, bbTR, VR] using i3
    · simpa [mvTR, VfTR, bbTR, VR] using i4
    · simpa [mvTR, VfTR, bbTR, VR] using i5
    · simpa [mvTR, VfTR, bbTR, VR] using i6
  · intro k hk
    rcases cases7 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvTR, VfTR, bbTR] using bv0
    · simpa [mvTR, VfTR, bbTR] using bv1
    · simpa [mvTR, VfTR, bbTR] using bv2
    · simpa [mvTR, VfTR, bbTR] using bv3
    · simpa [mvTR, VfTR, bbTR] using bv4
    · simpa [mvTR, VfTR, bbTR] using bv5
    · simpa [mvTR, VfTR, bbTR] using bv6
  · intro k hk
    rcases cases7 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvTR, VfTR, bbTR] using l0
    · simpa [mvTR, VfTR, bbTR] using l1
    · simpa [mvTR, VfTR, bbTR] using l2
    · simpa [mvTR, VfTR, bbTR] using l3
    · simpa [mvTR, VfTR, bbTR] using l4
    · simpa [mvTR, VfTR, bbTR] using l5
    · simpa [mvTR, VfTR, bbTR] using l6
  · intro k hk
    rcases cases7 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simpa [mvTR, VfTR, bbTR] using o0
    · simpa [mvTR, VfTR, bbTR] using o1
    · simpa [mvTR, VfTR, bbTR] using o2
    · simpa [mvTR, VfTR, bbTR] using o3
    · simpa [mvTR, VfTR, bbTR] using o4
    · simpa [mvTR, VfTR, bbTR] using o5
    · simpa [mvTR, VfTR, bbTR] using o6
  · intro k hk
    rcases cases7 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · simp [VR]; omega
    · simp [VR]; omega
    · simp [VR]; omega
    · simp [VR]; omega
    · simp [VR]; omega
    · simp [VR]; omega
    · simp [VR]; omega


theorem getD_lt_of (L : List Nat) (n : Nat) (h : ∀ x ∈ L, x < n) (hn : 0 < n) (q : Nat) : L.getD q 0 < n := by
  by_cases hq : q < L.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
    exact h _ (List.getElem_mem hq)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact hn

theorem getD_natAbs_le (L : List Int) (Cb : Nat) (h : ∀ x ∈ L, x.natAbs ≤ Cb) (q : Nat) : (L.getD q 0).natAbs ≤ Cb := by
  by_cases hq : q < L.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq]
    exact h _ (List.getElem_mem hq)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    simp

theorem getD_neg_of (L : List Int) (n : Nat) (hL : L.length = n) (h : ∀ x ∈ L, x < 0) (v : Nat) (hv : v < n) :
    L.getD v 0 < 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
  exact h _ (List.getElem_mem _)

set_option maxHeartbeats 16000000 in
/-- `cp::tree_root(head, target, cost, parent, depth, cost_depth, stk, root, n)` roots the graph at `root` by a depth-first
search: afterwards `parent`, `depth` and `cost_depth` describe a spanning tree of the vertices reachable from `root`. -/
theorem tree_root_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 s4 vb4 V4 vsc4 s5 vb5 V5 vsc5 s6 vb6 V6 vsc6} {m0 m1 m2 : Bool}
    {vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 vbuf5 vbuf6}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0)
    (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller s64 s2 vb2 V2 vsc2 false m2 vbuf2)
    (ok3 : VOKG caller i32 s3 vb3 V3 vsc3 true true vbuf3)
    (ok4 : VOKG caller i32 s4 vb4 V4 vsc4 true true vbuf4)
    (ok5 : VOKG caller s64 s5 vb5 V5 vsc5 true true vbuf5)
    (ok6 : VOKG caller i32 s6 vb6 V6 vsc6 true true vbuf6)
    (h03 : V0 ≠ V3) (h04 : V0 ≠ V4) (h05 : V0 ≠ V5) (h06 : V0 ≠ V6)
    (h13 : V1 ≠ V3) (h14 : V1 ≠ V4) (h15 : V1 ≠ V5) (h16 : V1 ≠ V6)
    (h23 : V2 ≠ V3) (h24 : V2 ≠ V4) (h25 : V2 ≠ V5) (h26 : V2 ≠ V6)
    (h34 : V3 ≠ V4) (h35 : V3 ≠ V5) (h36 : V3 ≠ V6) (h45 : V4 ≠ V5) (h46 : V4 ≠ V6) (h56 : V5 ≠ V6)
    (H T : List Nat) (Cs par dep cd Stk : List Int) (root n Cb : Nat)
    (hn : n < 2147483646) (hroot : root < n) (HK : HeadOK H T n) (hm : T.length < 2147483647)
    (hCl : Cs.length = T.length) (hTn : ∀ x ∈ T, x < n) (hCb : ∀ x ∈ Cs, x.natAbs ≤ Cb)
    (hCbn : n * Cb < 9223372036854775808)
    (hP : par.length = n) (hD : dep.length = n) (hCd : cd.length = n) (hS : Stk.length = n + 1) (hneg : ∀ x ∈ par, x < 0)
    (i0 : vbuf0.items = (H.map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = (T.map (fun x : Nat => (x : Int))).map Value.integer)
    (i2 : vbuf2.items = Cs.map Value.integer)
    (i3 : vbuf3.items = par.map Value.integer)
    (i4 : vbuf4.items = dep.map Value.integer)
    (i5 : vbuf5.items = cd.map Value.integer)
    (i6 : vbuf6.items = Stk.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32)))
    (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (bv2 : vbuf2.Valid (accepts (.integer s64)))
    (bv3 : vbuf3.Valid (accepts (.integer i32)))
    (bv4 : vbuf4.Valid (accepts (.integer i32)))
    (bv5 : vbuf5.Valid (accepts (.integer s64)))
    (bv6 : vbuf6.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32)
    (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit s64)
    (l3 : vbuf3.limit = CppVectorBindings.sizeLimit i32)
    (l4 : vbuf4.limit = CppVectorBindings.sizeLimit i32)
    (l5 : vbuf5.limit = CppVectorBindings.sizeLimit s64)
    (l6 : vbuf6.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0)
    (o1 : vbuf1.owner = V1)
    (o2 : vbuf2.owner = V2)
    (o3 : vbuf3.owner = V3)
    (o4 : vbuf4.owner = V4)
    (o5 : vbuf5.owner = V5)
    (o6 : vbuf6.owner = V6)
    (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (ty1 : e1.resultType = i32)
    (ty2 : e2.resultType = i32) (value1 : e1.denote (envOf caller) = some (root : Int))
    (value2 : e2.denote (envOf caller) = some (n : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (R : St) (Stk' : List Int),
      prepare caller Proofs.TreeRootInstance.tree_root_std_vector_int.parameters
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.vectorReference s4,
         .vectorReference s5,.vectorReference s6,.value e1,.value e2] = some Sinit ∧
      Proofs.TreeRootInstance.tree_root_std_vector_int.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.vectorReference s4,
         .vectorReference s5,.vectorReference s6,.value e1,.value e2] = .finished (res,Ret.unit) ∧
      R = runL H T Cs n (initSt par dep cd root) ∧ TreeSpec H T Cs n root Cb R ∧
      (∃ F : Nat, Stk'.getD n 0 = (F : Int) ∧ FarSpec H T n root R F) ∧
      ScalarPostM (mvTR V0 V1 V2 V3 V4 V5 V6 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 vsc6 m0 m1 m2 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length (hdTR V0 V1 V2 V3 V4 V5 V6 h03 h04 h05 h06 h13 h14 h15 h16 h23 h24 h25 h26 h34 h35 h36 h45 h46 h56))
        caller Sinit res (e1.nodes + e2.nodes) (720 * n + 820 * T.length + 500) caller.scalars.memory
        (4 * T.length + n + 5) (VR H T Cs R.par R.dep R.cd Stk') := by
  have hn32 : n < 2147483648 := by omega
  have hn0 : 0 < n := by omega
  have hTn' : ∀ q, T.getD q 0 < n := getD_lt_of T n hTn hn0
  have hCb' : ∀ q, (Cs.getD q 0).natAbs ≤ Cb := getD_natAbs_le Cs Cb hCb
  have hneg' : ∀ v, v < n → par.getD v 0 < 0 := getD_neg_of par n hP hneg
  have vp := valid_of_items i32 par vbuf3 i3 bv3
  have vd := valid_of_items i32 dep vbuf4 i4 bv4
  have vc := valid_of_items s64 cd vbuf5 i5 bv5
  have vs := valid_of_items i32 Stk vbuf6 i6 bv6
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_tr caller ok0 ok1 ok2 ok3 ok4 ok5 ok6 e1 e2 (root : Int) (n : Int) hs1 hs2 ty1 ty2 value1 value2
      (validN root (by omega)) (validN n hn32)
  have hHl : H.length < 2147483647 := by rw [HK.len]; omega
  have fwS := fwTR_init caller ok0 ok1 ok2 ok3 ok4 ok5 ok6 h03 h04 h05 h06 h13 h14 h15 h16 h23 h24 h25 h26 h34 h35 h36 h45 h46 h56
    H T Cs par dep cd Stk hHl hm (by omega) (by omega) (by omega) (by omega) (by omega) i0 i1 i2 i3 i4 i5 i6
    bv0 bv1 bv2 bv3 bv4 bv5 bv6 l0 l1 l2 l3 l4 l5 l6 o0 o1 o2 o3 o4 o5 o6
  rw [← sFrame] at fwS
  obtain ⟨rr,g2',hexec,hret,hrps,hst,hrvv,hCx,hIv,hGI,hFS,hFlt,hcost,hneed,hwk⟩ :=
    body_exec (mvTR V0 V1 V2 V3 V4 V5 V6 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 vsc6 m0 m1 m2 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length (hdTR V0 V1 V2 V3 V4 V5 V6 h03 h04 h05 h06 h13 h14 h15 h16 h23 h24 h25 h26 h34 h35 h36 h45 h46 h56)) rfl (by simp [mvTR]) (by simp [mvTR]) (by simp [mvTR])
      (by simp [mvTR]) (by simp [mvTR]) (by simp [mvTR]) (by simp [mvTR]) H T Cs par dep cd Stk n root Cb HK (callerP caller)
      (by omega) hroot (by omega) hm hCl hTn' hCb' hCbn hP hD hCd hS hneg' vp vd vc vs (T.length + 2 + n + 1) (Nat.le_refl _)
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
  have hpost := call_vecm_unit (mvTR V0 V1 V2 V3 V4 V5 V6 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 vsc6 m0 m1 m2 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length (hdTR V0 V1 V2 V3 V4 V5 V6 h03 h04 h05 h06 h13 h14 h15 h16 h23 h24 h25 h26 h34 h35 h36 h45 h46 h56))
    (fun k => decide (k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6))
    (by intro k hk; have : k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 := by simpa using hk
        rcases this with rfl | rfl | rfl | rfl <;> simp [mvTR])
    caller Proofs.TreeRootInstance.tree_root_std_vector_int
    [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.vectorReference s4,
     .vectorReference s5,.vectorReference s6,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨i32,(root : Int)⟩ : Cell),(⟨i32,(n : Int)⟩ : Cell)])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [body_eqTR7]; exact wr_bodyTR)
    (T.length + 2 + n + 1) rr (by rw [hmk, body_eqTR7]; exact hexec) hret rfl (by omega)
    (by simp [hlenP]) (e1.nodes + e2.nodes) (720 * n + 820 * T.length + 500) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  have hspec := tree_root_spec2 H T Cs n root Cb hTn' hCb' par dep cd hroot hP hD hCd hneg'
  have hfin := runL_final_S H T Cs n root Cb hTn' hCb' par dep cd hroot hP hD hCd hneg'
  have hSnil : g2'.st.S = [] := by rw [hst]; exact hfin.1
  refine ⟨Sinit,fuel,res,g2'.st,g2'.Stk,hprep,hrun,hst,?_,?_,?_⟩
  · rw [hst]; exact hspec
  · exact ⟨g2'.F, hFS, far_spec H T Cs n root Cb hTn' g2'.st g2'.D g2'.F hIv hGI hSnil⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.TreeRootCall
