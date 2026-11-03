import Proofs.TreeFullDpPrepare
import Proofs.TreeFullDpTd
import Proofs.MultiVecCallB

namespace Proofs.TreeFullDpCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCallB
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.TreeFullDpPrepare
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (cs)
open Proofs.TreeFullDpBody Proofs.TreeFullDpExec Proofs.TreeFullDpTd Proofs.TreeDpAlg Proofs.TreeDpSpec Proofs.TreeDpMath

/-- Selection of one of nine values by index. -/
def sel9 {α : Type} (a0 a1 a2 a3 a4 a5 a6 a7 a8 : α) : Nat → α := fun k =>
  if k = 0 then a0 else if k = 1 then a1 else if k = 2 then a2 else if k = 3 then a3 else if k = 4 then a4
  else if k = 5 then a5 else if k = 6 then a6 else if k = 7 then a7 else a8

theorem cases9 (k : Nat) (hk : k < 9) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 := by omega

/-- The callee of `tree_full_dp`: `head`, `target`, `parent`, `ord` (read-only `int` vectors) and `dp`, `pre`, `suf`, `up`,
`full` (writable `long long` vectors). -/
def mvFD (V0 V1 V2 V3 V4 V5 V6 V7 V8 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 vsc6 vsc7 vsc8 : Nat) (m0 m1 m2 m3 : Bool)
    (L0 T0 sc N : Nat)
    (hd : ∀ j k, j < 9 → k < 9 → j ≠ k → 4 ≤ k → sel9 V0 V1 V2 V3 V4 V5 V6 V7 V8 j ≠ sel9 V0 V1 V2 V3 V4 V5 V6 V7 V8 k) : MV where
  nv := 9
  ty := fun k => if k < 4 then i32 else s64
  wV := fun k => decide (4 ≤ k)
  flag := fun k => if k = 0 then m0 else if k = 1 then m1 else if k = 2 then m2 else if k = 3 then m3 else true
  R := sel9 V0 V1 V2 V3 V4 V5 V6 V7 V8
  vsc := sel9 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 vsc6 vsc7 vsc8
  perm := by
    intro k hk
    have : 4 ≤ k := by simpa using hk
    simp [show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, show k ≠ 3 by omega]
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk hw
    exact hd j k hj hk hjk (by simpa using hw)

def bbFD (b0 b1 b2 b3 b4 b5 b6 b7 b8 : Buffer Value) : Nat → Buffer Value := sel9 b0 b1 b2 b3 b4 b5 b6 b7 b8

theorem body_eqFD9 : Proofs.TreeFullDpInstance.tree_full_dp_std_vector_int.body = bodyFD 9 := rfl

theorem wr_bodyFD : WrM (fun k => decide (4 ≤ k)) (bodyFD 9) = true := by decide


theorem fwFD_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 s4 vb4 V4 vsc4 s5 vb5 V5 vsc5 s6 vb6 V6 vsc6 s7 vb7 V7 vsc7 s8 vb8 V8 vsc8 : Nat} {m0 m1 m2 m3 : Bool}
    {vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 vbuf5 vbuf6 vbuf7 vbuf8 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0)
    (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 false m2 vbuf2)
    (ok3 : VOKG caller i32 s3 vb3 V3 vsc3 false m3 vbuf3)
    (ok4 : VOKG caller s64 s4 vb4 V4 vsc4 true true vbuf4)
    (ok5 : VOKG caller s64 s5 vb5 V5 vsc5 true true vbuf5)
    (ok6 : VOKG caller s64 s6 vb6 V6 vsc6 true true vbuf6)
    (ok7 : VOKG caller s64 s7 vb7 V7 vsc7 true true vbuf7)
    (ok8 : VOKG caller s64 s8 vb8 V8 vsc8 true true vbuf8)
    (hdist : ∀ j k, j < 9 → k < 9 → j ≠ k → 4 ≤ k → sel9 V0 V1 V2 V3 V4 V5 V6 V7 V8 j ≠ sel9 V0 V1 V2 V3 V4 V5 V6 V7 V8 k)
    (head target : List Nat) (parent : List Int) (ord : List Nat) (dp0 pre0 suf0 up0 fu0 : List Int)
    (hs : head.length < 2147483647 ∧ target.length < 2147483647 ∧ parent.length < 2147483647 ∧ ord.length < 2147483647 ∧
      dp0.length < 2147483647 ∧ pre0.length < 2147483647 ∧ suf0.length < 2147483647 ∧ up0.length < 2147483647 ∧
      fu0.length < 2147483647)
    (i0 : vbuf0.items = (head.map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = (target.map (fun x : Nat => (x : Int))).map Value.integer)
    (i2 : vbuf2.items = parent.map Value.integer)
    (i3 : vbuf3.items = (ord.map (fun x : Nat => (x : Int))).map Value.integer)
    (i4 : vbuf4.items = dp0.map Value.integer)
    (i5 : vbuf5.items = pre0.map Value.integer)
    (i6 : vbuf6.items = suf0.map Value.integer)
    (i7 : vbuf7.items = up0.map Value.integer)
    (i8 : vbuf8.items = fu0.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32)))
    (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (bv2 : vbuf2.Valid (accepts (.integer i32)))
    (bv3 : vbuf3.Valid (accepts (.integer i32)))
    (bv4 : vbuf4.Valid (accepts (.integer s64)))
    (bv5 : vbuf5.Valid (accepts (.integer s64)))
    (bv6 : vbuf6.Valid (accepts (.integer s64)))
    (bv7 : vbuf7.Valid (accepts (.integer s64)))
    (bv8 : vbuf8.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32)
    (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32)
    (l3 : vbuf3.limit = CppVectorBindings.sizeLimit i32)
    (l4 : vbuf4.limit = CppVectorBindings.sizeLimit s64)
    (l5 : vbuf5.limit = CppVectorBindings.sizeLimit s64)
    (l6 : vbuf6.limit = CppVectorBindings.sizeLimit s64)
    (l7 : vbuf7.limit = CppVectorBindings.sizeLimit s64)
    (l8 : vbuf8.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0)
    (o1 : vbuf1.owner = V1)
    (o2 : vbuf2.owner = V2)
    (o3 : vbuf3.owner = V3)
    (o4 : vbuf4.owner = V4)
    (o5 : vbuf5.owner = V5)
    (o6 : vbuf6.owner = V6)
    (o7 : vbuf7.owner = V7)
    (o8 : vbuf8.owner = V8)
    :
    FWM (mvFD V0 V1 V2 V3 V4 V5 V6 V7 V8 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 vsc6 vsc7 vsc8 m0 m1 m2 m3 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length hdist)
      (VA ⟨head.map (fun x : Nat => (x : Int)), target.map (fun x : Nat => (x : Int)), parent, ord.map (fun x : Nat => (x : Int)), dp0, pre0, suf0, up0, fu0⟩) (bbFD vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 vbuf5 vbuf6 vbuf7 vbuf8 ) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer i32,false,.root vsc0⟩,
         ⟨V1,.integer i32,false,.root vsc1⟩,
         ⟨V2,.integer i32,false,.root vsc2⟩,
         ⟨V3,.integer i32,false,.root vsc3⟩,
         ⟨V4,.integer s64,true,.root vsc4⟩,
         ⟨V5,.integer s64,true,.root vsc5⟩,
         ⟨V6,.integer s64,true,.root vsc6⟩,
         ⟨V7,.integer s64,true,.root vsc7⟩,
         ⟨V8,.integer s64,true,.root vsc8⟩]⟩ : Frame) := by
  obtain ⟨s0l, s1l, s2l, s3l, s4l, s5l, s6l, s7l, s8l⟩ := hs
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases9 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | simpa [mvFD, bbFD, VA, sel9] using ok0.vtag | simpa [mvFD, bbFD, VA, sel9] using ok1.vtag | simpa [mvFD, bbFD, VA, sel9] using ok2.vtag | simpa [mvFD, bbFD, VA, sel9] using ok3.vtag | simpa [mvFD, bbFD, VA, sel9] using ok4.vtag | simpa [mvFD, bbFD, VA, sel9] using ok5.vtag | simpa [mvFD, bbFD, VA, sel9] using ok6.vtag | simpa [mvFD, bbFD, VA, sel9] using ok7.vtag | simpa [mvFD, bbFD, VA, sel9] using ok8.vtag
  · intro k hk
    rcases cases9 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | simpa [mvFD, bbFD, VA, sel9] using ok0.vfound | simpa [mvFD, bbFD, VA, sel9] using ok1.vfound | simpa [mvFD, bbFD, VA, sel9] using ok2.vfound | simpa [mvFD, bbFD, VA, sel9] using ok3.vfound | simpa [mvFD, bbFD, VA, sel9] using ok4.vfound | simpa [mvFD, bbFD, VA, sel9] using ok5.vfound | simpa [mvFD, bbFD, VA, sel9] using ok6.vfound | simpa [mvFD, bbFD, VA, sel9] using ok7.vfound | simpa [mvFD, bbFD, VA, sel9] using ok8.vfound
  · intro k hk
    rcases cases9 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | simpa [mvFD, bbFD, VA, sel9] using ok0.flag | simpa [mvFD, bbFD, VA, sel9] using ok1.flag | simpa [mvFD, bbFD, VA, sel9] using ok2.flag | simpa [mvFD, bbFD, VA, sel9] using ok3.flag | simpa [mvFD, bbFD, VA, sel9] using ok4.flag | simpa [mvFD, bbFD, VA, sel9] using ok5.flag | simpa [mvFD, bbFD, VA, sel9] using ok6.flag | simpa [mvFD, bbFD, VA, sel9] using ok7.flag | simpa [mvFD, bbFD, VA, sel9] using ok8.flag
  · intro k hk
    rcases cases9 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | simpa [mvFD, bbFD, VA, sel9] using i0 | simpa [mvFD, bbFD, VA, sel9] using i1 | simpa [mvFD, bbFD, VA, sel9] using i2 | simpa [mvFD, bbFD, VA, sel9] using i3 | simpa [mvFD, bbFD, VA, sel9] using i4 | simpa [mvFD, bbFD, VA, sel9] using i5 | simpa [mvFD, bbFD, VA, sel9] using i6 | simpa [mvFD, bbFD, VA, sel9] using i7 | simpa [mvFD, bbFD, VA, sel9] using i8
  · intro k hk
    rcases cases9 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | simpa [mvFD, bbFD, sel9] using bv0 | simpa [mvFD, bbFD, sel9] using bv1 | simpa [mvFD, bbFD, sel9] using bv2 | simpa [mvFD, bbFD, sel9] using bv3 | simpa [mvFD, bbFD, sel9] using bv4 | simpa [mvFD, bbFD, sel9] using bv5 | simpa [mvFD, bbFD, sel9] using bv6 | simpa [mvFD, bbFD, sel9] using bv7 | simpa [mvFD, bbFD, sel9] using bv8
  · intro k hk
    rcases cases9 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | simpa [mvFD, bbFD, sel9] using l0 | simpa [mvFD, bbFD, sel9] using l1 | simpa [mvFD, bbFD, sel9] using l2 | simpa [mvFD, bbFD, sel9] using l3 | simpa [mvFD, bbFD, sel9] using l4 | simpa [mvFD, bbFD, sel9] using l5 | simpa [mvFD, bbFD, sel9] using l6 | simpa [mvFD, bbFD, sel9] using l7 | simpa [mvFD, bbFD, sel9] using l8
  · intro k hk
    rcases cases9 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | simpa [mvFD, bbFD, sel9] using o0 | simpa [mvFD, bbFD, sel9] using o1 | simpa [mvFD, bbFD, sel9] using o2 | simpa [mvFD, bbFD, sel9] using o3 | simpa [mvFD, bbFD, sel9] using o4 | simpa [mvFD, bbFD, sel9] using o5 | simpa [mvFD, bbFD, sel9] using o6 | simpa [mvFD, bbFD, sel9] using o7 | simpa [mvFD, bbFD, sel9] using o8
  · intro k hk
    rcases cases9 k hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [VA, mvFD, sel9] <;> omega

set_option maxHeartbeats 16000000 in
/-- `cp::tree_full_dp<DpHeight<long long>>(head, target, parent, ord, dp, pre, suf, up, full, root, n)`. -/
theorem tree_full_dp_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 s3 vb3 V3 vsc3 s4 vb4 V4 vsc4 s5 vb5 V5 vsc5 s6 vb6 V6 vsc6 s7 vb7 V7 vsc7 s8 vb8 V8 vsc8 : Nat} {m0 m1 m2 m3 : Bool}
    {vbuf0 vbuf1 vbuf2 vbuf3 vbuf4 vbuf5 vbuf6 vbuf7 vbuf8 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0)
    (ok1 : VOKG caller i32 s1 vb1 V1 vsc1 false m1 vbuf1)
    (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 false m2 vbuf2)
    (ok3 : VOKG caller i32 s3 vb3 V3 vsc3 false m3 vbuf3)
    (ok4 : VOKG caller s64 s4 vb4 V4 vsc4 true true vbuf4)
    (ok5 : VOKG caller s64 s5 vb5 V5 vsc5 true true vbuf5)
    (ok6 : VOKG caller s64 s6 vb6 V6 vsc6 true true vbuf6)
    (ok7 : VOKG caller s64 s7 vb7 V7 vsc7 true true vbuf7)
    (ok8 : VOKG caller s64 s8 vb8 V8 vsc8 true true vbuf8)
    (hdist : ∀ j k, j < 9 → k < 9 → j ≠ k → 4 ≤ k → sel9 V0 V1 V2 V3 V4 V5 V6 V7 V8 j ≠ sel9 V0 V1 V2 V3 V4 V5 V6 V7 V8 k)
    (head target : List Nat) (parent : List Int) (ord : List Nat) (dp0 pre0 suf0 up0 fu0 : List Int) (n root : Nat)
    (M : TS head target parent ord n root)
    (hlen : head.length = n + 1) (hmono : ∀ v, v < n → head.getD v 0 ≤ head.getD (v + 1) 0)
    (hlast : head.getD n 0 = target.length) (tlen : target.length < 2147483647)
    (tlt : ∀ q, q < target.length → target.getD q 0 < n) (nb : n + 2 < 2147483648) (palen : parent.length = n)
    (pav : ∀ w, w < n → 0 ≤ parent.getD w 0 ∧ parent.getD w 0 < n) (odlen : ord.length = n) (odlt : ∀ x ∈ ord, x < n)
    (hdl : dp0.length = n) (hpl : pre0.length = target.length) (hsl : suf0.length = target.length)
    (hul : up0.length = n) (hfl : fu0.length = n)
    (hdp : ∀ x, 0 ≤ dp0.getD x 0 ∧ dp0.getD x 0 ≤ n) (hup : ∀ x, 0 ≤ up0.getD x 0 ∧ up0.getD x 0 ≤ n)
    (i0 : vbuf0.items = (head.map (fun x : Nat => (x : Int))).map Value.integer)
    (i1 : vbuf1.items = (target.map (fun x : Nat => (x : Int))).map Value.integer)
    (i2 : vbuf2.items = parent.map Value.integer)
    (i3 : vbuf3.items = (ord.map (fun x : Nat => (x : Int))).map Value.integer)
    (i4 : vbuf4.items = dp0.map Value.integer)
    (i5 : vbuf5.items = pre0.map Value.integer)
    (i6 : vbuf6.items = suf0.map Value.integer)
    (i7 : vbuf7.items = up0.map Value.integer)
    (i8 : vbuf8.items = fu0.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer i32)))
    (bv1 : vbuf1.Valid (accepts (.integer i32)))
    (bv2 : vbuf2.Valid (accepts (.integer i32)))
    (bv3 : vbuf3.Valid (accepts (.integer i32)))
    (bv4 : vbuf4.Valid (accepts (.integer s64)))
    (bv5 : vbuf5.Valid (accepts (.integer s64)))
    (bv6 : vbuf6.Valid (accepts (.integer s64)))
    (bv7 : vbuf7.Valid (accepts (.integer s64)))
    (bv8 : vbuf8.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32)
    (l1 : vbuf1.limit = CppVectorBindings.sizeLimit i32)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32)
    (l3 : vbuf3.limit = CppVectorBindings.sizeLimit i32)
    (l4 : vbuf4.limit = CppVectorBindings.sizeLimit s64)
    (l5 : vbuf5.limit = CppVectorBindings.sizeLimit s64)
    (l6 : vbuf6.limit = CppVectorBindings.sizeLimit s64)
    (l7 : vbuf7.limit = CppVectorBindings.sizeLimit s64)
    (l8 : vbuf8.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0)
    (o1 : vbuf1.owner = V1)
    (o2 : vbuf2.owner = V2)
    (o3 : vbuf3.owner = V3)
    (o4 : vbuf4.owner = V4)
    (o5 : vbuf5.owner = V5)
    (o6 : vbuf6.owner = V6)
    (o7 : vbuf7.owner = V7)
    (o8 : vbuf8.owner = V8)
    (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (ty1 : e1.resultType = i32)
    (ty2 : e2.resultType = i32) (value1 : e1.denote (envOf caller) = some (root : Int))
    (value2 : e2.denote (envOf caller) = some (n : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (a' : Arr) (F' U' : List Int),
      prepare caller Proofs.TreeFullDpInstance.tree_full_dp_std_vector_int.parameters
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.vectorReference s4,.vectorReference s5,.vectorReference s6,.vectorReference s7,.vectorReference s8,.value e1,.value e2] = some Sinit ∧
      Proofs.TreeFullDpInstance.tree_full_dp_std_vector_int.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.vectorReference s4,.vectorReference s5,.vectorReference s6,.vectorReference s7,.vectorReference s8,.value e1,.value e2] = .finished (res,Ret.unit) ∧
      (∀ v, v < n → ∃ f, Ef M0 head target f (pp parent n root v) v = some (a'.dp.getD v 0)) ∧
      (∀ w, w < n → w ≠ root → ∃ f, Ef M0 head target f w (par parent w) = some (U'.getD w 0)) ∧
      (∀ v, v < n → ∃ f, Ef M0 head target f n v = some (F'.getD v 0)) ∧
      ScalarPostMB 1000 (mvFD V0 V1 V2 V3 V4 V5 V6 V7 V8 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 vsc6 vsc7 vsc8 m0 m1 m2 m3 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length hdist)
        caller Sinit res (e1.nodes + e2.nodes) (5500 * target.length + 2400 * n + 700) caller.scalars.memory
        (5 * target.length + 5 * n + 8) (VA { a' with fu := F', up := U' }) := by
  have hrn := M.rootlt
  have hrk : root < 2147483648 := by omega
  have hn32 : n < 2147483648 := by omega
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_fd caller ok0 ok1 ok2 ok3 ok4 ok5 ok6 ok7 ok8 e1 e2 (root : Int) (n : Int) hs1 hs2 ty1 ty2 value1 value2 (validN root hrk) (validN n hn32)
  have fwS := fwFD_init caller ok0 ok1 ok2 ok3 ok4 ok5 ok6 ok7 ok8 hdist head target parent ord dp0 pre0 suf0 up0 fu0
    ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩ i0 i1 i2 i3 i4 i5 i6 i7 i8 bv0 bv1 bv2 bv3 bv4 bv5 bv6 bv7 bv8 l0 l1 l2 l3 l4 l5 l6 l7 l8 o0 o1 o2 o3 o4 o5 o6 o7 o8
  rw [← sFrame] at fwS
  obtain ⟨rr,a',F',U',hexec,hret,hrps,hrvv,B0,hupB,I,hcost,hneed,hwk⟩ :=
    body_exec (mvFD V0 V1 V2 V3 V4 V5 V6 V7 V8 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 vsc6 vsc7 vsc8 m0 m1 m2 m3 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length hdist) rfl (by simp [mvFD]) (by simp [mvFD])
      (by simp [mvFD]) (by simp [mvFD]) (by simp [mvFD]) (by simp [mvFD]) (by simp [mvFD]) (by simp [mvFD]) (by simp [mvFD])
      (callerP caller) head target parent ord n root M ⟨head.map (fun x : Nat => (x : Int)), target.map (fun x : Nat => (x : Int)), parent, ord.map (fun x : Nat => (x : Int)), dp0, pre0, suf0, up0, fu0⟩
      ⟨rfl, rfl, rfl, rfl, hlen, hmono, hlast, tlen, tlt, nb, palen, pav, odlen, odlt⟩ ⟨hdl, hpl, hsl, hul, hfl⟩ hdp hup
      (2 * n + target.length + 6) (Nat.le_refl _)
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
  have hpost := call_vecm_unitB 1000 (mvFD V0 V1 V2 V3 V4 V5 V6 V7 V8 vsc0 vsc1 vsc2 vsc3 vsc4 vsc5 vsc6 vsc7 vsc8 m0 m1 m2 m3 caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length hdist)
    (fun k => decide (4 ≤ k))
    (by intro k hk; have : 4 ≤ k := by simpa using hk
        simp [mvFD, show k ≠ 0 by omega, show k ≠ 1 by omega, show k ≠ 2 by omega, show k ≠ 3 by omega, this])
    caller Proofs.TreeFullDpInstance.tree_full_dp_std_vector_int
    [.vectorReference s0,.vectorReference s1,.vectorReference s2,.vectorReference s3,.vectorReference s4,.vectorReference s5,.vectorReference s6,.vectorReference s7,.vectorReference s8,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨i32,(root : Int)⟩ : Cell),(⟨i32,(n : Int)⟩ : Cell)])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [body_eqFD9]; exact wr_bodyFD)
    (2 * n + target.length + 6) rr (by rw [hmk, body_eqFD9]; exact hexec) hret rfl (by omega)
    (by simp [hlenP]) (e1.nodes + e2.nodes) (5500 * target.length + 2400 * n + 700) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  have hfc := full_correct M a' F' U' B0 I
  refine ⟨Sinit,fuel,res,a',F',U',hprep,hrun,hfc.1,hfc.2.1,hfc.2.2,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.TreeFullDpCall
