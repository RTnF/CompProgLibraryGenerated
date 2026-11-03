import Proofs.TreeDistancePrepare
import Proofs.TreeDistanceExec
import Proofs.MultiVecCall

namespace Proofs.TreeDistanceCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.TreeDistancePrepare Proofs.TreeDistanceExec
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)

/-- The contents of the only vector. -/
def VD (D : List Int) : Nat → List Int := fun k => if k = 0 then D else []

/-- The callee of `tree_distance`: one read-only `long long` vector. -/
def mvTD (V0 vsc0 : Nat) (m0 : Bool) (L0 T0 sc N : Nat) : MV where
  nv := 1
  ty := fun _ => s64
  wV := fun _ => false
  flag := fun _ => m0
  R := fun _ => V0
  vsc := fun _ => vsc0
  perm := by intro k hk; simp at hk
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by intro j k hj hk hjk hw; simp at hw

theorem wr_bodyTD : WrM (fun _ => false) (bodyTD 1) = true := by simp [WrM]

theorem fwTD_init (caller : NState) {s0 vb0 V0 vsc0 : Nat} {m0 : Bool} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 false m0 vbuf0) (D : List Int) (hD : D.length < 2147483647)
    (i0 : vbuf0.items = D.map Value.integer) (bv0 : vbuf0.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (o0 : vbuf0.owner = V0) :
    FWM (mvTD V0 vsc0 m0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) (VD D) (fun _ => vbuf0) 0
      (⟨caller.frame.state, caller.frame.rootWritable, [⟨V0,.integer s64,false,.root vsc0⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    have : k = 0 := by simp [mvTD] at hk; omega
    subst this
    simpa [mvTD] using ok0.vtag
  · intro k hk
    have : k = 0 := by simp [mvTD] at hk; omega
    subst this
    simpa [mvTD] using ok0.vfound
  · intro k hk
    have : k = 0 := by simp [mvTD] at hk; omega
    subst this
    simpa [mvTD] using ok0.flag
  · intro k hk
    have : k = 0 := by simp [mvTD] at hk; omega
    subst this
    simpa [mvTD, VD] using i0
  · intro k hk
    have : k = 0 := by simp [mvTD] at hk; omega
    subst this
    simpa [mvTD] using bv0
  · intro k hk
    have : k = 0 := by simp [mvTD] at hk; omega
    subst this
    simpa [mvTD] using l0
  · intro k hk
    have : k = 0 := by simp [mvTD] at hk; omega
    subst this
    simpa [mvTD] using o0
  · intro k hk
    have : k = 0 := by simp [mvTD] at hk; omega
    subst this
    simp [VD]; omega

set_option maxHeartbeats 8000000 in
/-- `cp::tree_distance<long long>(cost_depth, u, v, lca)` returns `cost_depth[u] + cost_depth[v] - cost_depth[lca] * 2`. -/
theorem tree_distance_correct (caller : NState) {s0 vb0 V0 vsc0 : Nat} {m0 : Bool} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller s64 s0 vb0 V0 vsc0 false m0 vbuf0) (D : List Int) (u v l : Nat)
    (hu : u < D.length) (hv : v < D.length) (hl : l < D.length) (hD : D.length < 2147483647)
    (hDv : ∀ x ∈ D, s64.valid x = true)
    (hab : s64.valid (D.getD u 0 + D.getD v 0) = true) (hc2 : s64.valid (D.getD l 0 * 2) = true)
    (hfin : s64.valid (D.getD u 0 + D.getD v 0 - D.getD l 0 * 2) = true)
    (i0 : vbuf0.items = D.map Value.integer) (bv0 : vbuf0.Valid (accepts (.integer s64)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit s64) (o0 : vbuf0.owner = V0)
    (e1 e2 e3 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (u : Int)) (value2 : e2.denote (envOf caller) = some (v : Int))
    (value3 : e3.denote (envOf caller) = some (l : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.TreeDistanceInstance.tree_distance_std_vector_long_long.parameters
        [.vectorReference s0,.value e1,.value e2,.value e3] = some Sinit ∧
      Proofs.TreeDistanceInstance.tree_distance_std_vector_long_long.callFuel fuel caller
        [.vectorReference s0,.value e1,.value e2,.value e3] =
        .finished (res,.scalar (D.getD u 0 + D.getD v 0 - D.getD l 0 * 2)) ∧
      ScalarPostM (mvTD V0 vsc0 m0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) caller Sinit res (e1.nodes + e2.nodes + e3.nodes) 200
        caller.scalars.memory 0 (VD D) := by
  have hu32 : u < 2147483648 := by omega
  have hv32 : v < 2147483648 := by omega
  have hl32 : l < 2147483648 := by omega
  obtain ⟨t1,t2,t3,g1,g2,g3,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_td caller ok0 e1 e2 e3 (u : Int) (v : Int) (l : Int) hs1 hs2 hs3 ty1 ty2 ty3 value1 value2 value3
      (validN u hu32) (validN v hv32) (validN l hl32)
  have fwS := fwTD_init caller ok0 D hD i0 bv0 l0 o0
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,⟨cs,hrps⟩,hcost,hneed,hwk⟩ :=
    body_exec (mvTD V0 vsc0 m0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) rfl rfl D (VD D) (by simp [VD]) (callerP caller) u v l hu hv hl
      (by show D.length < 2147483648; omega) hDv hab hc2 hfin 1
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(u : Int)⟩ : Cell),(⟨i32,(v : Int)⟩ : Cell),(⟨i32,(l : Int)⟩ : Cell)]).take
      caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(u : Int)⟩ : Cell),(⟨i32,(v : Int)⟩ : Cell),(⟨i32,(l : Int)⟩ : Cell)],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]⟩ : PS) =
      gS (callerP caller) [ci u, ci v, ci l] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  have gw3 := g3.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2 gw3
  have hpost := call_vecm (mvTD V0 vsc0 m0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) (fun _ => false)
    (by intro k hk; simp at hk)
    caller Proofs.TreeDistanceInstance.tree_distance_std_vector_long_long
    [.vectorReference s0,.value e1,.value e2,.value e3] Sinit
    (callerP caller ++ [(⟨i32,(u : Int)⟩ : Cell),(⟨i32,(v : Int)⟩ : Cell),(⟨i32,(l : Int)⟩ : Cell)])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [body_eqTD]; exact wr_bodyTD)
    1 rr (by rw [hmk, body_eqTD]; exact hexec) _ hret s64 rfl hfin (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes + e3.nodes) 200 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv, hwk] at post
  exact post

end Proofs.TreeDistanceCall
