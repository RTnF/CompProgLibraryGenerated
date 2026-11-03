import Proofs.TreeArcCostsPrepare
import Proofs.TreeArcCostsExec
import Proofs.MultiVecCall

namespace Proofs.TreeArcCostsCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.TreeArcCostsPrepare Proofs.TreeArcCostsExec
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)

/-- The callee of `tree_arc_costs<long long>`: two `long long` vectors, the last one writable. -/
def mvAC (V0 V1 vsc0 vsc1 : Nat) (m0 : Bool) (L0 T0 sc N : Nat) (h01 : V0 ≠ V1) : MV where
  nv := 2
  ty := fun _ => s64
  wV := fun k => decide (k = 1)
  flag := fun k => if k = 0 then m0 else true
  R := fun k => if k = 0 then V0 else V1
  vsc := fun k => if k = 0 then vsc0 else vsc1
  perm := by
    intro k hk
    have : k = 1 := by simpa using hk
    subst this; simp
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by
    intro j k hj hk hjk hw
    have : k = 1 := by simpa using hw
    subst this
    have : j = 0 := by omega
    subst this
    simpa using h01

def bbAC (b0 b1 : Buffer Value) : Nat → Buffer Value :=
  fun k => if k = 0 then b0 else b1

theorem wr_bodyAC : WrM (fun k => decide (k = 1)) (bodyAC 2) = true := by decide

theorem cases2 (k : Nat) (hk : k < 2) : k = 0 ∨ k = 1 := by omega

theorem fwAC_init (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m0 : Bool}
    {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (h01 : V0 ≠ V1) (C AC : List Int) (hC : C.length < 2147483647) (hAC : AC.length < 2147483647)
    (i0 : vbuf0.items = C.map Value.integer) (i1 : vbuf1.items = AC.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1) :
    FWM (mvAC V0 V1 vsc0 vsc1 m0 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01)
      (VC C AC) (bbAC vbuf0 vbuf1) 0
      (⟨caller.frame.state, caller.frame.rootWritable,
        [⟨V0,.integer s64,false,.root vsc0⟩,⟨V1,.integer s64,true,.root vsc1⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvAC] using ok0.vtag
    · simpa [mvAC] using ok1.vtag
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvAC, bbAC] using ok0.vfound
    · simpa [mvAC, bbAC] using ok1.vfound
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvAC] using ok0.flag
    · simpa [mvAC] using ok1.flag
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvAC, bbAC, VC] using i0
    · simpa [mvAC, bbAC, VC] using i1
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvAC, bbAC] using bv0
    · simpa [mvAC, bbAC] using bv1
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvAC, bbAC] using l0
    · simpa [mvAC, bbAC] using l1
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simpa [mvAC, bbAC] using o0
    · simpa [mvAC, bbAC] using o1
  · intro k hk
    rcases cases2 k hk with rfl | rfl
    · simp [VC]; omega
    · simp [VC]; omega

set_option maxHeartbeats 8000000 in
/-- `cp::tree_arc_costs<long long>(cost, ac, m)` writes `cost[i]` to `ac[2 * i]` and `ac[2 * i + 1]`. -/
theorem tree_arc_costs_correct (caller : NState) {s0 vb0 V0 vsc0 s1 vb1 V1 vsc1 : Nat} {m0 : Bool}
    {vbuf0 vbuf1 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 false m0 vbuf0) (ok1 : VOKG caller s64 s1 vb1 V1 vsc1 true true vbuf1)
    (h01 : V0 ≠ V1) (C AC : List Int) (m : Nat) (hm : m < 536870912) (hC : m ≤ C.length)
    (hAC : 2 * m ≤ AC.length) (hC2 : C.length < 2147483647) (hAC2 : AC.length < 2147483647)
    (hCv : ∀ x ∈ C, s64.valid x = true)
    (i0 : vbuf0.items = C.map Value.integer) (i1 : vbuf1.items = AC.map Value.integer)
    (bv0 : vbuf0.Valid (accepts (.integer s64))) (bv1 : vbuf1.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (l1 : vbuf1.limit = CppVectorBindings.sizeLimit s64)
    (o0 : vbuf0.owner = V0) (o1 : vbuf1.owner = V1)
    (e1 : NExpr) (hs1 : e1.scalarOnly = true) (ty1 : e1.resultType = i32) (value1 : e1.denote (envOf caller) = some (m : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.TreeArcCostsInstance.tree_arc_costs_std_vector_long_long.parameters
        [.vectorReference s0,.vectorReference s1,.value e1] = some Sinit ∧
      Proofs.TreeArcCostsInstance.tree_arc_costs_std_vector_long_long.callFuel fuel caller
        [.vectorReference s0,.vectorReference s1,.value e1] = .finished (res,Ret.unit) ∧
      ScalarPostM (mvAC V0 V1 vsc0 vsc1 m0 caller.frame.state.liveSpace caller.frame.state.storage.work
        (caller.scope + 1) caller.frame.state.storage.objects.length h01)
        caller Sinit res e1.nodes (220 * m + 100) caller.scalars.memory (2 * m)
        (VC C (ACt C AC m)) := by
  have hm32 : m < 2147483648 := by omega
  obtain ⟨t1,g1,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    prepare_ta caller ok0 ok1 e1 (m : Int) hs1 ty1 value1 (validN m hm32)
  have fwS := fwAC_init caller ok0 ok1 h01 C AC hC2 hAC2 i0 i1 bv0 bv1 l0 l1 o0 o1
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,⟨cs,hrps⟩,hcost,hneed,hwk⟩ :=
    body_exec (mvAC V0 V1 vsc0 vsc1 m0 caller.frame.state.liveSpace caller.frame.state.storage.work
      (caller.scope + 1) caller.frame.state.storage.objects.length h01) rfl rfl rfl C AC (callerP caller) m
    hm hC hAC hCv (m + 1) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(m : Int)⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(m : Int)⟩ : Cell)], [⟨(callerP caller).length,true⟩]⟩ : PS) =
      gS (callerP caller) [ci m] := by
    simp [gS]
  have gw := g1.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw
  have hpost := call_vecm_unit (mvAC V0 V1 vsc0 vsc1 m0 caller.frame.state.liveSpace
      caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length h01)
    (fun k => decide (k = 1))
    (by intro k hk; have : k = 1 := by simpa using hk
        subst this; simp [mvAC])
    caller Proofs.TreeArcCostsInstance.tree_arc_costs_std_vector_long_long
    [.vectorReference s0,.vectorReference s1,.value e1] Sinit
    (callerP caller ++ [(⟨i32,(m : Int)⟩ : Cell)]) [⟨(callerP caller).length,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [body_eqAC]; exact wr_bodyAC)
    (m + 1) rr (by rw [hmk, body_eqAC]; exact hexec) hret rfl (by omega) (by simp [hlenP]) e1.nodes (220 * m + 100) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv] at post
  exact post.relax (Nat.le_refl _) (Nat.le_refl _) hwk

end Proofs.TreeArcCostsCall
