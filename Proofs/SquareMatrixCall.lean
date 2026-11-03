import Proofs.SquareMatrixPrepare
import Proofs.SquareMatrixEw
import Proofs.SquareMatrixZero
import Proofs.SquareMatrixId
import Proofs.SquareMatrixNeg
import Proofs.SquareMatrixEq
import Proofs.MultiVecCall
import Proofs.MatPowCall

namespace Proofs.SquareMatrixCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.SquareMatrixPrepare
open Proofs.InvGcdExec (VO)
open Proofs.TreeArcCostsExec (VC)
open Proofs.BellmanFordExec (cs)
open Proofs.ForLoop (ci)
open Proofs.SquareMatrixEw (AllU EwInv)
open Proofs.SquareMatrixZero (ZInv)
open Proofs.SquareMatrixId (IdInv)
open Proofs.SquareMatrixNeg (NInv)

/-- The callee of `mat_zero` / `mat_identity`: one writable `unsigned long long` vector. -/
def mvSQ1 (V0 vsc0 : Nat) (L0 T0 sc N : Nat) : MV where
  nv := 1
  ty := fun _ => u64
  wV := fun _ => true
  flag := fun _ => true
  R := fun _ => V0
  vsc := fun _ => vsc0
  perm := by intro k hk; rfl
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by intro j k hj hk hjk hw; exact absurd hjk (by simp at hj hk; omega)

theorem fwSQ1_init (caller : NState) {s0 vb0 V0 vsc0 : Nat} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller u64 s0 vb0 V0 vsc0 true true vbuf0) (O : List Int) (hO : O.length < 2147483647)
    (i0 : vbuf0.items = O.map Value.integer) (bv0 : vbuf0.Valid (accepts (.integer u64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit u64) (o0 : vbuf0.owner = V0) :
    FWM (mvSQ1 V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) (VO O) (fun _ => vbuf0) 0
      (⟨caller.frame.state, caller.frame.rootWritable, [⟨V0,.integer u64,true,.root vsc0⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  all_goals
    intro k hk
    have : k = 0 := by simp [mvSQ1] at hk; omega
    subst this
  · simpa [mvSQ1] using ok0.vtag
  · simpa [mvSQ1] using ok0.vfound
  · simpa [mvSQ1] using ok0.flag
  · simpa [mvSQ1, VO] using i0
  · simpa [mvSQ1] using bv0
  · simpa [mvSQ1] using l0
  · simpa [mvSQ1] using o0
  · simp [VO]; omega

/-- The callee of `mat_add_assign` / `mat_sub_assign`: `a` (writable) and `b` (read-only), both `unsigned long long` vectors. -/
def mvSQ2 (V0 V1 vsc0 vsc1 : Nat) (m1 : Bool) (L0 T0 sc N : Nat) (h01 : V0 ≠ V1) : MV where
  nv := 2
  ty := fun _ => u64
  wV := fun k => decide (k = 0)
  flag := fun k => if k = 0 then true else m1
  R := fun k => if k = 0 then V0 else V1
  vsc := fun k => if k = 0 then vsc0 else vsc1
  perm := by
    intro k hk
    have : k = 0 := by simpa using hk
    subst this; simp
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk hw
    have : k = 0 := by simpa using hw
    subst this
    have : j = 1 := by omega
    subst this
    simpa using h01.symm

theorem cases2s (k : Nat) (hk : k < 2) : k = 0 ∨ k = 1 := by omega

theorem fwSQ2_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m1 : Bool}
    {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller u64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller u64 s1 vb1 V1 vsc1 false m1 vbuf1)
    (h01 : V0 ≠ V1) (A B : List Int) (hA : A.length < 2147483647) (hB : B.length < 2147483647)
    (i0 : vbuf0.items = A.map Value.integer) (i1 : vbuf1.items = B.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer u64))) (bv1 : vbuf1.Valid (accepts (.integer u64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit u64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit u64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) :
    FWM (mvSQ2 V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01)
      (VC A B) (fun k => if k = 0 then vbuf0 else vbuf1) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer u64,true,.root vsc0⟩,⟨V1,.integer u64,false,.root vsc1⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases2s k hk with rfl | rfl
    · simpa [mvSQ2] using ok0.vtag
    · simpa [mvSQ2] using ok1.vtag
  · intro k hk
    rcases cases2s k hk with rfl | rfl
    · simpa [mvSQ2] using ok0.vfound
    · simpa [mvSQ2] using ok1.vfound
  · intro k hk
    rcases cases2s k hk with rfl | rfl
    · simpa [mvSQ2] using ok0.flag
    · simpa [mvSQ2] using ok1.flag
  · intro k hk
    rcases cases2s k hk with rfl | rfl
    · simpa [mvSQ2, VC] using i0
    · simpa [mvSQ2, VC] using i1
  · intro k hk
    rcases cases2s k hk with rfl | rfl
    · simpa [mvSQ2] using bv0
    · simpa [mvSQ2] using bv1
  · intro k hk
    rcases cases2s k hk with rfl | rfl
    · simpa [mvSQ2] using l0
    · simpa [mvSQ2] using l1
  · intro k hk
    rcases cases2s k hk with rfl | rfl
    · simpa [mvSQ2] using o0
    · simpa [mvSQ2] using o1
  · intro k hk
    rcases cases2s k hk with rfl | rfl
    · simp [VC]; omega
    · simp [VC]; omega


set_option maxHeartbeats 16000000 in
/-- `cp::mat_add_assign(a, b, n)` sets `a[i] = a[i] + b[i] (mod 2^64)` for `i < n * n`. -/
theorem mat_add_correct (caller : NState) (n : Nat) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m1 : Bool} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller u64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller u64 s1 vb1 V1 vsc1 false m1 vbuf1)
    (h01 : V0 ≠ V1) (A B : List Int) (hn : n < 2147483648) (hnn : n * n < 2147483648)
    (hmA : n * n ≤ A.length) (hmB : n * n ≤ B.length) (hA : AllU A) (hB : AllU B)
    (hAl : A.length < 2147483647) (hBl : B.length < 2147483647)
    (i0 : vbuf0.items = A.map Value.integer) (i1 : vbuf1.items = B.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer u64))) (bv1 : vbuf1.Valid (accepts (.integer u64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit u64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit u64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1)
    (e1 : NExpr) (hs1 : e1.scalarOnly = true) (ty1 : e1.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (n : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.SquareMatrixInstance.mat_add_assign_std_vector_unsigned_long_long.parameters [.vectorReference s0,.vectorReference s1,.value e1] = some Sinit ∧
      Proofs.SquareMatrixInstance.mat_add_assign_std_vector_unsigned_long_long.callFuel fuel caller [.vectorReference s0,.vectorReference s1,.value e1] = .finished (res,Ret.unit) ∧
      ∃ Vf : List Int, EwInv .add A B (n * n) Vf ∧
        ScalarPostM (mvSQ2 V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01)
          caller Sinit res e1.nodes (600 * (n * n) + 200) caller.scalars.memory (n * n) (VC Vf B) := by
  have vn : i32.valid (n : Int) = true := Proofs.TopoSortExec.i32v n hn
  obtain ⟨t1,g1,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    prepare_ew caller ok0 ok1 e1 (n : Int) hs1 ty1 value1 vn
  have fwS := fwSQ2_init caller ok0 ok1 h01 A B hAl hBl i0 i1 bv0 bv1 l0 l1 o0 o1
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,⟨cl,hrps⟩,Vf,hrvv,hIf,hcost,hneed,hwk⟩ :=
    Proofs.SquareMatrixEw.body_execEw (mvSQ2 V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01) rfl rfl rfl (callerP caller) .add n A B hnn hn hmA hmB hA hB (n * n + 3) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)],
      [⟨(callerP caller).length,true⟩]⟩ : PS) = gS (callerP caller) [ci n] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hpost := call_vecm_unit (mvSQ2 V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01)
    (fun k => decide (k = 0))
    (by intro k hk; have : k = 0 := by simpa using hk
        subst this; simp [mvSQ2])
    caller Proofs.SquareMatrixInstance.mat_add_assign_std_vector_unsigned_long_long
    [.vectorReference s0,.vectorReference s1,.value e1] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)])
    [⟨(callerP caller).length,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [Proofs.SquareMatrixEw.body_eqAdd]; exact (by decide : WrM (fun k => decide (k = 0)) (Proofs.SquareMatrixEw.bodyEW 2 .add) = true))
    _ rr (by rw [hmk, Proofs.SquareMatrixEw.body_eqAdd]; exact hexec) hret rfl (by omega) (by simp [hlenP])
    e1.nodes (600 * (n * n) + 200) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,Vf,hIf,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

set_option maxHeartbeats 16000000 in
/-- `cp::mat_sub_assign(a, b, n)` sets `a[i] = a[i] - b[i] (mod 2^64)` for `i < n * n`. -/
theorem mat_sub_correct (caller : NState) (n : Nat) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m1 : Bool} {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller u64 s0 vb0 V0 vsc0 true true vbuf0) (ok1 : VOKG caller u64 s1 vb1 V1 vsc1 false m1 vbuf1)
    (h01 : V0 ≠ V1) (A B : List Int) (hn : n < 2147483648) (hnn : n * n < 2147483648)
    (hmA : n * n ≤ A.length) (hmB : n * n ≤ B.length) (hA : AllU A) (hB : AllU B)
    (hAl : A.length < 2147483647) (hBl : B.length < 2147483647)
    (i0 : vbuf0.items = A.map Value.integer) (i1 : vbuf1.items = B.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer u64))) (bv1 : vbuf1.Valid (accepts (.integer u64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit u64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit u64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1)
    (e1 : NExpr) (hs1 : e1.scalarOnly = true) (ty1 : e1.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (n : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.SquareMatrixInstance.mat_sub_assign_std_vector_unsigned_long_long.parameters [.vectorReference s0,.vectorReference s1,.value e1] = some Sinit ∧
      Proofs.SquareMatrixInstance.mat_sub_assign_std_vector_unsigned_long_long.callFuel fuel caller [.vectorReference s0,.vectorReference s1,.value e1] = .finished (res,Ret.unit) ∧
      ∃ Vf : List Int, EwInv .sub A B (n * n) Vf ∧
        ScalarPostM (mvSQ2 V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01)
          caller Sinit res e1.nodes (600 * (n * n) + 200) caller.scalars.memory (n * n) (VC Vf B) := by
  have vn : i32.valid (n : Int) = true := Proofs.TopoSortExec.i32v n hn
  obtain ⟨t1,g1,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    prepare_sub caller ok0 ok1 e1 (n : Int) hs1 ty1 value1 vn
  have fwS := fwSQ2_init caller ok0 ok1 h01 A B hAl hBl i0 i1 bv0 bv1 l0 l1 o0 o1
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,⟨cl,hrps⟩,Vf,hrvv,hIf,hcost,hneed,hwk⟩ :=
    Proofs.SquareMatrixEw.body_execEw (mvSQ2 V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01) rfl rfl rfl (callerP caller) .sub n A B hnn hn hmA hmB hA hB (n * n + 3) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)],
      [⟨(callerP caller).length,true⟩]⟩ : PS) = gS (callerP caller) [ci n] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hpost := call_vecm_unit (mvSQ2 V0 V1 vsc0 vsc1 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01)
    (fun k => decide (k = 0))
    (by intro k hk; have : k = 0 := by simpa using hk
        subst this; simp [mvSQ2])
    caller Proofs.SquareMatrixInstance.mat_sub_assign_std_vector_unsigned_long_long
    [.vectorReference s0,.vectorReference s1,.value e1] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)])
    [⟨(callerP caller).length,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [Proofs.SquareMatrixEw.body_eqSub]; exact (by decide : WrM (fun k => decide (k = 0)) (Proofs.SquareMatrixEw.bodyEW 2 .sub) = true))
    _ rr (by rw [hmk, Proofs.SquareMatrixEw.body_eqSub]; exact hexec) hret rfl (by omega) (by simp [hlenP])
    e1.nodes (600 * (n * n) + 200) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,Vf,hIf,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

set_option maxHeartbeats 16000000 in
/-- `cp::mat_zero(a, n)` sets `a[i] = 0` for `i < n * n`. -/
theorem mat_zero_correct (caller : NState) (n : Nat) {s0 vb0 V0 vsc0 : Nat} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller u64 s0 vb0 V0 vsc0 true true vbuf0) (A : List Int) (hn : n < 2147483648)
    (hnn : n * n < 2147483648) (hmA : n * n ≤ A.length) (hAl : A.length < 2147483647)
    (i0 : vbuf0.items = A.map Value.integer) (bv0 : vbuf0.Valid (accepts (.integer u64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit u64) (o0 : vbuf0.owner = V0)
    (e1 : NExpr) (hs1 : e1.scalarOnly = true) (ty1 : e1.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (n : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.SquareMatrixInstance.mat_zero_std_vector_unsigned_long_long.parameters [.vectorReference s0,.value e1] = some Sinit ∧
      Proofs.SquareMatrixInstance.mat_zero_std_vector_unsigned_long_long.callFuel fuel caller [.vectorReference s0,.value e1] = .finished (res,Ret.unit) ∧
      ∃ Vf : List Int, ZInv A (n * n) Vf ∧
        ScalarPostM (mvSQ1 V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
          caller Sinit res e1.nodes (500 * (n * n) + 200) caller.scalars.memory (n * n) (VO Vf) := by
  have vn : i32.valid (n : Int) = true := Proofs.TopoSortExec.i32v n hn
  obtain ⟨t1,g1,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    prepare_zero caller ok0 e1 (n : Int) hs1 ty1 value1 vn
  have fwS := fwSQ1_init caller ok0 A hAl i0 bv0 l0 o0
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,⟨cl,hrps⟩,Vf,hrvv,hIf,hcost,hneed,hwk⟩ :=
    Proofs.SquareMatrixZero.body_execZero (mvSQ1 V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length) rfl rfl (callerP caller) n A hnn hn hmA (n * n + 3) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)],
      [⟨(callerP caller).length,true⟩]⟩ : PS) = gS (callerP caller) [ci n] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hpost := call_vecm_unit (mvSQ1 V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
    (fun _ => true)
    (by intro k hk; exact ⟨rfl, rfl⟩)
    caller Proofs.SquareMatrixInstance.mat_zero_std_vector_unsigned_long_long
    [.vectorReference s0,.value e1] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)])
    [⟨(callerP caller).length,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [Proofs.SquareMatrixZero.body_eqZero]; exact (by decide : WrM (fun _ => true) (Proofs.SquareMatrixZero.bodyZero 1) = true))
    _ rr (by rw [hmk, Proofs.SquareMatrixZero.body_eqZero]; exact hexec) hret rfl (by omega) (by simp [hlenP])
    e1.nodes (500 * (n * n) + 200) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,Vf,hIf,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

set_option maxHeartbeats 16000000 in
/-- `cp::mat_negate(a, n)` sets `a[i] = (0 - a[i]) mod 2^64` for `i < n * n`. -/
theorem mat_negate_correct (caller : NState) (n : Nat) {s0 vb0 V0 vsc0 : Nat} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller u64 s0 vb0 V0 vsc0 true true vbuf0) (A : List Int) (hn : n < 2147483648)
    (hnn : n * n < 2147483648) (hmA : n * n ≤ A.length) (hAl : A.length < 2147483647)
    (i0 : vbuf0.items = A.map Value.integer) (bv0 : vbuf0.Valid (accepts (.integer u64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit u64) (o0 : vbuf0.owner = V0) (hA : AllU A)
    (e1 : NExpr) (hs1 : e1.scalarOnly = true) (ty1 : e1.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (n : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.SquareMatrixInstance.mat_negate_std_vector_unsigned_long_long.parameters [.vectorReference s0,.value e1] = some Sinit ∧
      Proofs.SquareMatrixInstance.mat_negate_std_vector_unsigned_long_long.callFuel fuel caller [.vectorReference s0,.value e1] = .finished (res,Ret.unit) ∧
      ∃ Vf : List Int, NInv A (n * n) Vf ∧
        ScalarPostM (mvSQ1 V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
          caller Sinit res e1.nodes (600 * (n * n) + 200) caller.scalars.memory (n * n) (VO Vf) := by
  have vn : i32.valid (n : Int) = true := Proofs.TopoSortExec.i32v n hn
  obtain ⟨t1,g1,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    prepare_neg caller ok0 e1 (n : Int) hs1 ty1 value1 vn
  have fwS := fwSQ1_init caller ok0 A hAl i0 bv0 l0 o0
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,⟨cl,hrps⟩,Vf,hrvv,hIf,hcost,hneed,hwk⟩ :=
    Proofs.SquareMatrixNeg.body_execNeg (mvSQ1 V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length) rfl rfl (callerP caller) n A hnn hn hmA hA (n * n + 3) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)],
      [⟨(callerP caller).length,true⟩]⟩ : PS) = gS (callerP caller) [ci n] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hpost := call_vecm_unit (mvSQ1 V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
    (fun _ => true)
    (by intro k hk; exact ⟨rfl, rfl⟩)
    caller Proofs.SquareMatrixInstance.mat_negate_std_vector_unsigned_long_long
    [.vectorReference s0,.value e1] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)])
    [⟨(callerP caller).length,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [Proofs.SquareMatrixNeg.body_eqNeg]; exact (by decide : WrM (fun _ => true) (Proofs.SquareMatrixNeg.bodyNeg 1) = true))
    _ rr (by rw [hmk, Proofs.SquareMatrixNeg.body_eqNeg]; exact hexec) hret rfl (by omega) (by simp [hlenP])
    e1.nodes (600 * (n * n) + 200) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,Vf,hIf,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

set_option maxHeartbeats 16000000 in
/-- `cp::mat_identity(a, n)` sets `a[i * n + j] = (i == j)` for `i, j < n`. -/
theorem mat_identity_correct (caller : NState) (n : Nat) {s0 vb0 V0 vsc0 : Nat} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller u64 s0 vb0 V0 vsc0 true true vbuf0) (A : List Int) (hn : n < 2147483648)
    (hnn : n * n < 2147483648) (hmA : n * n ≤ A.length) (hAl : A.length < 2147483647)
    (i0 : vbuf0.items = A.map Value.integer) (bv0 : vbuf0.Valid (accepts (.integer u64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit u64) (o0 : vbuf0.owner = V0)
    (e1 : NExpr) (hs1 : e1.scalarOnly = true) (ty1 : e1.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (n : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.SquareMatrixInstance.mat_identity_std_vector_unsigned_long_long.parameters [.vectorReference s0,.value e1] = some Sinit ∧
      Proofs.SquareMatrixInstance.mat_identity_std_vector_unsigned_long_long.callFuel fuel caller [.vectorReference s0,.value e1] = .finished (res,Ret.unit) ∧
      ∃ Vf : List Int, IdInv n A (n * n) Vf ∧
        ScalarPostM (mvSQ1 V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
          caller Sinit res e1.nodes ((900 * n + 200) * n + 200) caller.scalars.memory ((2 * n + 2) * n + 1) (VO Vf) := by
  have vn : i32.valid (n : Int) = true := Proofs.TopoSortExec.i32v n hn
  obtain ⟨t1,g1,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    prepare_id caller ok0 e1 (n : Int) hs1 ty1 value1 vn
  have fwS := fwSQ1_init caller ok0 A hAl i0 bv0 l0 o0
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrps,Vf,hrvv,hIf,hcost,hneed,hwk⟩ :=
    Proofs.SquareMatrixId.body_execId (mvSQ1 V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length) rfl rfl (callerP caller) n A hnn hmA (2 * n + 7) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)],
      [⟨(callerP caller).length,true⟩]⟩ : PS) = gS (callerP caller) [ci n] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hpost := call_vecm_unit (mvSQ1 V0 vsc0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
    (fun _ => true)
    (by intro k hk; exact ⟨rfl, rfl⟩)
    caller Proofs.SquareMatrixInstance.mat_identity_std_vector_unsigned_long_long
    [.vectorReference s0,.value e1] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)])
    [⟨(callerP caller).length,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [Proofs.SquareMatrixId.body_eqId]; exact (by decide : WrM (fun _ => true) (Proofs.SquareMatrixId.bodyId 1) = true))
    _ rr (by rw [hmk, Proofs.SquareMatrixId.body_eqId]; exact hexec) hret rfl (by omega) (by simp [hlenP])
    e1.nodes ((900 * n + 200) * n + 200) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,Vf,hIf,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

/-- The callee of `mat_equal`: `a` and `b` (both read-only), `unsigned long long` vectors. -/
def mvSQ0 (V0 V1 vsc0 vsc1 : Nat) (m0 m1 : Bool) (L0 T0 sc N : Nat) : MV where
  nv := 2
  ty := fun _ => u64
  wV := fun _ => false
  flag := fun k => if k = 0 then m0 else m1
  R := fun k => if k = 0 then V0 else V1
  vsc := fun k => if k = 0 then vsc0 else vsc1
  perm := by intro k hk; exact absurd hk (by simp)
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by intro j k hj hk hjk hw; exact absurd hw (by simp)

theorem fwSQ0_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m0 m1 : Bool}
    {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller u64 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller u64 s1 vb1 V1 vsc1 false m1 vbuf1)
    (A B : List Int) (hA : A.length < 2147483647) (hB : B.length < 2147483647)
    (i0 : vbuf0.items = A.map Value.integer) (i1 : vbuf1.items = B.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer u64))) (bv1 : vbuf1.Valid (accepts (.integer u64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit u64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit u64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) :
    FWM (mvSQ0 V0 V1 vsc0 vsc1 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length)
      (VC A B) (fun k => if k = 0 then vbuf0 else vbuf1) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer u64,false,.root vsc0⟩,⟨V1,.integer u64,false,.root vsc1⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases2s k hk with rfl | rfl
    · simpa [mvSQ0] using ok0.vtag
    · simpa [mvSQ0] using ok1.vtag
  · intro k hk
    rcases cases2s k hk with rfl | rfl
    · simpa [mvSQ0] using ok0.vfound
    · simpa [mvSQ0] using ok1.vfound
  · intro k hk
    rcases cases2s k hk with rfl | rfl
    · simpa [mvSQ0] using ok0.flag
    · simpa [mvSQ0] using ok1.flag
  · intro k hk
    rcases cases2s k hk with rfl | rfl
    · simpa [mvSQ0, VC] using i0
    · simpa [mvSQ0, VC] using i1
  · intro k hk
    rcases cases2s k hk with rfl | rfl
    · simpa [mvSQ0] using bv0
    · simpa [mvSQ0] using bv1
  · intro k hk
    rcases cases2s k hk with rfl | rfl
    · simpa [mvSQ0] using l0
    · simpa [mvSQ0] using l1
  · intro k hk
    rcases cases2s k hk with rfl | rfl
    · simpa [mvSQ0] using o0
    · simpa [mvSQ0] using o1
  · intro k hk
    rcases cases2s k hk with rfl | rfl
    · simp [VC]; omega
    · simp [VC]; omega

open Classical in
set_option maxHeartbeats 16000000 in
/-- `cp::mat_equal(a, b, n)` returns whether `a[i] == b[i]` for all `i < n * n`. -/
theorem mat_equal_correct (caller : NState) (n : Nat) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m0 m1 : Bool}
    {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller u64 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller u64 s1 vb1 V1 vsc1 false m1 vbuf1)
    (A B : List Int) (hn : n < 2147483648) (hnn : n * n < 2147483648)
    (hmA : n * n ≤ A.length) (hmB : n * n ≤ B.length) (hA : AllU A) (hB : AllU B)
    (hAl : A.length < 2147483647) (hBl : B.length < 2147483647)
    (i0 : vbuf0.items = A.map Value.integer) (i1 : vbuf1.items = B.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer u64))) (bv1 : vbuf1.Valid (accepts (.integer u64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit u64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit u64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1)
    (e1 : NExpr) (hs1 : e1.scalarOnly = true) (ty1 : e1.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (n : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.SquareMatrixInstance.mat_equal_std_vector_unsigned_long_long.parameters [.vectorReference s0,.vectorReference s1,.value e1] = some Sinit ∧
      Proofs.SquareMatrixInstance.mat_equal_std_vector_unsigned_long_long.callFuel fuel caller [.vectorReference s0,.vectorReference s1,.value e1] =
        .finished (res,.scalar (if ∀ j, j < n * n → A.getD j 0 = B.getD j 0 then 1 else 0)) ∧
      ScalarPostM (mvSQ0 V0 V1 vsc0 vsc1 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
        caller Sinit res e1.nodes (600 * (n * n) + 300) caller.scalars.memory 0 (VC A B) := by
  have vn : i32.valid (n : Int) = true := Proofs.TopoSortExec.i32v n hn
  obtain ⟨t1,g1,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    prepare_eq caller ok0 ok1 e1 (n : Int) hs1 ty1 value1 vn
  have fwS := fwSQ0_init caller ok0 ok1 A B hAl hBl i0 i1 bv0 bv1 l0 l1 o0 o1
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,⟨cl,hrps⟩,hrvv,hcost,hneed,hwk⟩ :=
    Proofs.SquareMatrixEq.body_execEq (mvSQ0 V0 V1 vsc0 vsc1 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length) rfl rfl rfl (callerP caller) n A B hnn hn hmA hmB hA hB (n * n + 3) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)],
      [⟨(callerP caller).length,true⟩]⟩ : PS) = gS (callerP caller) [ci n] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hv : bT.valid (if ∀ j, j < n * n → A.getD j 0 = B.getD j 0 then (1 : Int) else 0) = true := by
    split <;> decide
  have hpost := call_vecm (mvSQ0 V0 V1 vsc0 vsc1 m0 m1 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
    (fun _ => false) (by intro k hk; exact absurd hk (by simp))
    caller Proofs.SquareMatrixInstance.mat_equal_std_vector_unsigned_long_long
    [.vectorReference s0,.vectorReference s1,.value e1] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)])
    [⟨(callerP caller).length,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base
    (by rw [Proofs.SquareMatrixEq.body_eqEq]; exact (by decide : WrM (fun _ => false) (Proofs.SquareMatrixEq.bodyEQ 2) = true))
    (n * n + 3) rr (by rw [hmk, Proofs.SquareMatrixEq.body_eqEq]; exact hexec) _ hret bT rfl hv (by omega) (by simp [hlenP])
    e1.nodes (600 * (n * n) + 300) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

end Proofs.SquareMatrixCall
