import Proofs.MatMulPrepare
import Proofs.DijkstraOldExec
import Proofs.MultiVecCall

namespace Proofs.DijkstraOldCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.DijkstraOldExec Proofs.DijkstraOldScan
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)

/-- The callee of `dijkstra`: `head`, `target` (`int`), `cost` (`long long`) read-only; `dist` (`long long`) and `done` (`int`) writable. -/
def mvDJ (V0 V1 V2 V3 V4 vsc0 vsc1 vsc2 vsc3 vsc4 : Nat) (m0 m1 m2 : Bool) (L0 T0 sc N : Nat) (h03 : V0 ≠ V3)
    (h13 : V1 ≠ V3) (h23 : V2 ≠ V3) (h04 : V0 ≠ V4) (h14 : V1 ≠ V4) (h24 : V2 ≠ V4) (h34 : V3 ≠ V4) : MV where
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

def bbDJ (b0 b1 b2 b3 b4 : Buffer Value) : Nat → Buffer Value :=
  fun k => if k = 0 then b0 else if k = 1 then b1 else if k = 2 then b2 else if k = 3 then b3 else b4


theorem wr_bodyDJ : WrM (fun k => decide (k = 3 ∨ k = 4)) (bodyDJ 5) = true := by decide

theorem cases5 (k : Nat) (hk : k < 5) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega


/-- The frame facts at entry of `dijkstra` (before any work). -/
theorem fwDJ_init (caller : NState)
    {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 s4 vb4 V4 vsc4 : Nat} {m0 m1 m2 : Bool}
    {vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller s64 s2 vb2 V2 vsc2 false m2 vbuf2) (ok3 : VOKG caller s64 s3 vb3 V3 vsc3 true true vbuf3)
    (ok4 : VOKG caller i32 s4 vb4 V4 vsc4 true true vbuf4)
    (h03 : V0 ≠ V3) (h13 : V1 ≠ V3) (h23 : V2 ≠ V3) (h04 : V0 ≠ V4) (h14 : V1 ≠ V4) (h24 : V2 ≠ V4) (h34 : V3 ≠ V4)
    (H T : List Nat) (C Dd : List Int) (Dn : List Nat) (hHl : H.length < 2147483647) (hTl : T.length < 2147483647)
    (hCl : C.length < 2147483647) (hDl : Dd.length < 2147483647) (hNl : Dn.length < 2147483647)
    (i0 : vbuf0.items = (H.map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = (T.map (fun x : Nat => (x : Int))).map Value.integer)
    (i2 : vbuf2.items = C.map Value.integer) (i3 : vbuf3.items = Dd.map Value.integer)
    (i4 : vbuf4.items = (Dn.map (fun x : Nat => (x : Int))).map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32))) (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (bv2 : vbuf2.Valid (accepts (.integer s64))) (bv3 : vbuf3.Valid (accepts (.integer s64)))
    (bv4 : vbuf4.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit s64) (l3 : vbuf3.limit = CppVectorBindings.sizeLimit s64)
    (l4 : vbuf4.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) (o3 : vbuf3.owner = V3) (o4 : vbuf4.owner = V4) :
    FWM (mvDJ V0 V1 V2 V3 V4 vsc0 vsc1 vsc2 vsc3 vsc4 m0 m1 m2 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h03 h13 h23 h04 h14 h24 h34)
      (VD H T C Dd Dn) (bbDJ vbuf0 vbuf1 vbuf2 vbuf3 vbuf4) 0
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
    · simpa [mvDJ] using ok0.vtag
    · simpa [mvDJ] using ok1.vtag
    · simpa [mvDJ] using ok2.vtag
    · simpa [mvDJ] using ok3.vtag
    · simpa [mvDJ] using ok4.vtag
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvDJ, bbDJ] using ok0.vfound
    · simpa [mvDJ, bbDJ] using ok1.vfound
    · simpa [mvDJ, bbDJ] using ok2.vfound
    · simpa [mvDJ, bbDJ] using ok3.vfound
    · simpa [mvDJ, bbDJ] using ok4.vfound
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvDJ] using ok0.flag
    · simpa [mvDJ] using ok1.flag
    · simpa [mvDJ] using ok2.flag
    · simpa [mvDJ] using ok3.flag
    · simpa [mvDJ] using ok4.flag
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvDJ, bbDJ, VD] using i0
    · simpa [mvDJ, bbDJ, VD] using i1
    · simpa [mvDJ, bbDJ, VD] using i2
    · simpa [mvDJ, bbDJ, VD] using i3
    · simpa [mvDJ, bbDJ, VD] using i4
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvDJ, bbDJ] using bv0
    · simpa [mvDJ, bbDJ] using bv1
    · simpa [mvDJ, bbDJ] using bv2
    · simpa [mvDJ, bbDJ] using bv3
    · simpa [mvDJ, bbDJ] using bv4
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvDJ, bbDJ] using l0
    · simpa [mvDJ, bbDJ] using l1
    · simpa [mvDJ, bbDJ] using l2
    · simpa [mvDJ, bbDJ] using l3
    · simpa [mvDJ, bbDJ] using l4
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simpa [mvDJ, bbDJ] using o0
    · simpa [mvDJ, bbDJ] using o1
    · simpa [mvDJ, bbDJ] using o2
    · simpa [mvDJ, bbDJ] using o3
    · simpa [mvDJ, bbDJ] using o4
  · intro k hk
    rcases cases5 k hk with rfl | rfl | rfl | rfl | rfl
    · simp [VD]; omega
    · simp [VD]; omega
    · simp [VD]; omega
    · simp [VD]; omega
    · simp [VD]; omega


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

end Proofs.DijkstraOldCall
