import Proofs.CompressExec
import Proofs.MatMulPrepare
import Proofs.MultiVecCall

namespace Proofs.CompressPrepare
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare
open Proofs.CompressExec
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.MultiVecCall

theorem prepare_cmp (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 : Nat} {m0 : Bool}
    {vbuf0 vbuf1 vbuf2 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 true true vbuf2) :
    ∃ Sinit, prepare caller Proofs.SortUtilInstance.compress_std_vector_long_long.parameters
          [.vectorReference s0,.vectorReference s1,.vectorReference s2] = some Sinit ∧
        Sinit.slots = [.vector 0,.vector 1,.vector 2] ∧ Sinit.scalars.memory = callerP caller ∧
        Sinit.scalars.bindings = [] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          [⟨V0,.integer s64,false,.root vsc0⟩,⟨V1,.integer s64,true,.root vsc1⟩,⟨V2,.integer i32,true,.root vsc2⟩]⟩ ∧
        Sinit.scalars.work = caller.scalars.work + 7 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller s64 false ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => absurd h (by decide))
  have rv1 := resolve_vref (caller.charge 1 1) s64 true ok1.slot ok1.binding ok1.valid ok1.vtag ok1.vfound ok1.lengths
    ok1.flag ok1.perm (fun h => rfl)
  have rv2 := resolve_vref ((caller.charge 1 1).charge 1 1) i32 true ok2.slot ok2.binding ok2.valid ok2.vtag ok2.vfound
    ok2.lengths ok2.flag ok2.perm (fun h => rfl)
  have hp : Proofs.SortUtilInstance.compress_std_vector_long_long.parameters = [.vector s64 false,.vector s64 true,.vector i32 true] := rfl
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := m0)
    (vbuf := vbuf0) s64 false ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  have b1 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer s64,false,.root vsc0⟩]⟩ : Frame)
    (V := V1) (vsc := vsc1) (m := true) (vbuf := vbuf1) s64 true ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
  have b2 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer s64,false,.root vsc0⟩,
    ⟨V1,.integer s64,true,.root vsc1⟩]⟩ : Frame)
    (V := V2) (vsc := vsc2) (m := true) (vbuf := vbuf2) i32 true ok2.valid ok2.vtag ok2.vfound ok2.lengths ok2.flag ok2.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons] at b0 b1 b2
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, rv1, rv2]
  simp [b0, b1, b2, bindAll, bindOne, CppState.bindArgument, callerP, NState.observe, CppState.State.observe]
  constructor
  · simp [NState.charge, NState.observe, CppState.State.observe]
  · simp [NState.charge, NState.observe, CppState.State.observe]

theorem prepare_vvv (caller : NState) (prog : NProgram)
    (hp : prog.parameters = [.vector s64 false,.vector s64 true,.vector i32 true]) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 : Nat} {m0 : Bool}
    {vbuf0 vbuf1 vbuf2 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 true true vbuf2) :
    ∃ Sinit, prepare caller prog.parameters
          [.vectorReference s0,.vectorReference s1,.vectorReference s2] = some Sinit ∧
        Sinit.slots = [.vector 0,.vector 1,.vector 2] ∧ Sinit.scalars.memory = callerP caller ∧
        Sinit.scalars.bindings = [] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,
          [⟨V0,.integer s64,false,.root vsc0⟩,⟨V1,.integer s64,true,.root vsc1⟩,⟨V2,.integer i32,true,.root vsc2⟩]⟩ ∧
        Sinit.scalars.work = caller.scalars.work + 7 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  have rv0 := resolve_vref caller s64 false ok0.slot ok0.binding ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
    (fun h => absurd h (by decide))
  have rv1 := resolve_vref (caller.charge 1 1) s64 true ok1.slot ok1.binding ok1.valid ok1.vtag ok1.vfound ok1.lengths
    ok1.flag ok1.perm (fun h => rfl)
  have rv2 := resolve_vref ((caller.charge 1 1).charge 1 1) i32 true ok2.slot ok2.binding ok2.valid ok2.vtag ok2.vfound
    ok2.lengths ok2.flag ok2.perm (fun h => rfl)
  have b0 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[]⟩ : Frame) (V := V0) (vsc := vsc0) (m := m0)
    (vbuf := vbuf0) s64 false ok0.valid ok0.vtag ok0.vfound ok0.lengths ok0.flag ok0.perm
  have b1 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer s64,false,.root vsc0⟩]⟩ : Frame)
    (V := V1) (vsc := vsc1) (m := true) (vbuf := vbuf1) s64 true ok1.valid ok1.vtag ok1.vfound ok1.lengths ok1.flag ok1.perm
  have b2 := bindRoot_g (⟨caller.frame.state,caller.frame.rootWritable,[⟨V0,.integer s64,false,.root vsc0⟩,
    ⟨V1,.integer s64,true,.root vsc1⟩]⟩ : Frame)
    (V := V2) (vsc := vsc2) (m := true) (vbuf := vbuf2) i32 true ok2.valid ok2.vtag ok2.vfound ok2.lengths ok2.flag ok2.perm
  simp only [Frame.addBinding, List.nil_append, List.length_nil, List.length_cons] at b0 b1 b2
  rw [hp]
  simp [prepare, ok0.valid, resolveAll, rv0, rv1, rv2]
  simp [b0, b1, b2, bindAll, bindOne, CppState.bindArgument, callerP, NState.observe, CppState.State.observe]
  constructor
  · simp [NState.charge, NState.observe, CppState.State.observe]
  · simp [NState.charge, NState.observe, CppState.State.observe]



theorem cases3 (k : Nat) (hk : k < 3) : k = 0 ∨ k = 1 ∨ k = 2 := by omega

/-- The callee of `compress`: `x` (read only, `long long`), `unzip` (`long long`) and `cmp` (`int`), both writable. -/
def mvCm (V0 V1 V2 vsc0 vsc1 vsc2 : Nat) (m0 : Bool) (L0 T0 sc N : Nat)
    (h01 : V0 ≠ V1) (h02 : V0 ≠ V2) (h12 : V1 ≠ V2) : MV where
  nv := 3
  ty := fun k => if k = 2 then i32 else s64
  wV := fun k => decide (k ≠ 0)
  flag := fun k => if k = 0 then m0 else true
  R := fun k => if k = 0 then V0 else if k = 1 then V1 else V2
  vsc := fun k => if k = 0 then vsc0 else if k = 1 then vsc1 else vsc2
  perm := by
    intro k hk
    have : k ≠ 0 := by simpa using hk
    simp [this]
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk hw
    have hk0 : k ≠ 0 := by simpa using hw
    have hj3 : j < 3 := hj
    have hk3 : k < 3 := hk
    have : (j = 0 ∧ k = 1) ∨ (j = 0 ∧ k = 2) ∨ (j = 1 ∧ k = 2) ∨ (j = 2 ∧ k = 1) := by omega
    rcases this with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa using h01
    · simpa using h02
    · simpa using h12
    · simpa using h12.symm

def bbCm (b0 b1 b2 : Buffer Value) : Nat → Buffer Value := fun k => if k = 0 then b0 else if k = 1 then b1 else b2

/-- The frame facts at entry of `compress` (before any work). -/
theorem fwC_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 s2 vb2 V2 vsc2 : Nat} {m0 : Bool}
    {vbuf0 vbuf1 vbuf2 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (ok2 : VOKG caller i32 s2 vb2 V2 vsc2 true true vbuf2) (h01 : V0 ≠ V1) (h02 : V0 ≠ V2) (h12 : V1 ≠ V2)
    (X U Y : List Int) (n : Nat) (hn : n < 2147483647) (hlX : X.length = n) (hlU : U.length = n) (hlY : Y.length = n)
    (i0 : vbuf0.items = X.map Value.integer) (i1 : vbuf1.items = U.map Value.integer)
    (i2 : vbuf2.items = Y.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (bv2 : vbuf2.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (l2 : vbuf2.limit = CppVectorBindings.sizeLimit i32)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) (o2 : vbuf2.owner = V2) :
    FWM (mvCm V0 V1 V2 vsc0 vsc1 vsc2 m0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length h01 h02 h12)
      (V3 X U Y) (bbCm vbuf0 vbuf1 vbuf2) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer s64,false,.root vsc0⟩,⟨V1,.integer s64,true,.root vsc1⟩,⟨V2,.integer i32,true,.root vsc2⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvCm] using ok0.vtag
    · simpa [mvCm] using ok1.vtag
    · simpa [mvCm] using ok2.vtag
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvCm, bbCm] using ok0.vfound
    · simpa [mvCm, bbCm] using ok1.vfound
    · simpa [mvCm, bbCm] using ok2.vfound
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvCm] using ok0.flag
    · simpa [mvCm] using ok1.flag
    · simpa [mvCm] using ok2.flag
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvCm, bbCm, V3] using i0
    · simpa [mvCm, bbCm, V3] using i1
    · simpa [mvCm, bbCm, V3] using i2
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvCm, bbCm] using bv0
    · simpa [mvCm, bbCm] using bv1
    · simpa [mvCm, bbCm] using bv2
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvCm, bbCm] using l0
    · simpa [mvCm, bbCm] using l1
    · simpa [mvCm, bbCm] using l2
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simpa [mvCm, bbCm] using o0
    · simpa [mvCm, bbCm] using o1
    · simpa [mvCm, bbCm] using o2
  · intro k hk
    rcases cases3 k hk with rfl | rfl | rfl
    · simp [V3]; omega
    · simp [V3]; omega
    · simp [V3]; omega


end Proofs.CompressPrepare
