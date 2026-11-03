import Proofs.TreeFindRootPrepare
import Proofs.TreeFindRootExec
import Proofs.MultiVecCall

namespace Proofs.TreeFindRootCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.TreeFindRootPrepare Proofs.TreeFindRootExec
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (M31)

/-- The callee of `tree_find_root`: one read-only `int` vector. -/
def mvFR (V0 vsc0 : Nat) (m0 : Bool) (L0 T0 sc N : Nat) : MV where
  nv := 1
  ty := fun _ => i32
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

theorem wr_bodyFR : WrM (fun _ => false) (bodyFR 1) = true := by decide

theorem fwFR_init (caller : NState) {s0 vb0 V0 vsc0 : Nat} {m0 : Bool} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (Pr : List Int) (hP : Pr.length < 2147483647)
    (i0 : vbuf0.items = Pr.map Value.integer) (bv0 : vbuf0.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (o0 : vbuf0.owner = V0) :
    FWM (mvFR V0 vsc0 m0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) (VP Pr) (fun _ => vbuf0) 0
      (⟨caller.frame.state, caller.frame.rootWritable, [⟨V0,.integer i32,false,.root vsc0⟩]⟩ : Frame) := by
  refine ⟨ok0.valid, ok0.lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok0.strict owner k h
    show k < caller.scope + 1
    omega
  · intro k hk
    have : k = 0 := by simp [mvFR] at hk; omega
    subst this
    simpa [mvFR] using ok0.vtag
  · intro k hk
    have : k = 0 := by simp [mvFR] at hk; omega
    subst this
    simpa [mvFR] using ok0.vfound
  · intro k hk
    have : k = 0 := by simp [mvFR] at hk; omega
    subst this
    simpa [mvFR] using ok0.flag
  · intro k hk
    have : k = 0 := by simp [mvFR] at hk; omega
    subst this
    simpa [mvFR, VP] using i0
  · intro k hk
    have : k = 0 := by simp [mvFR] at hk; omega
    subst this
    simpa [mvFR] using bv0
  · intro k hk
    have : k = 0 := by simp [mvFR] at hk; omega
    subst this
    simpa [mvFR] using l0
  · intro k hk
    have : k = 0 := by simp [mvFR] at hk; omega
    subst this
    simpa [mvFR] using o0
  · intro k hk
    have : k = 0 := by simp [mvFR] at hk; omega
    subst this
    simp [VP]; omega

set_option maxHeartbeats 8000000 in
/-- `cp::tree_find_root(parent, n)` returns the last index `i < n` with `parent[i] == i` or `parent[i] < 0`, or `-1`. -/
theorem tree_find_root_correct (caller : NState) {s0 vb0 V0 vsc0 : Nat} {m0 : Bool} {vbuf0 : Buffer Value}
    (ok0 : VOKG caller i32 s0 vb0 V0 vsc0 false m0 vbuf0) (Pr : List Int) (n : Nat) (hn : n < 2147483647)
    (hPl : n ≤ Pr.length) (hP2 : Pr.length < 2147483647) (hPv : ∀ x ∈ Pr, i32.valid x = true)
    (i0 : vbuf0.items = Pr.map Value.integer) (bv0 : vbuf0.Valid (accepts (.integer i32)))
    (l0 : vbuf0.limit = CppVectorBindings.sizeLimit i32) (o0 : vbuf0.owner = V0)
    (e1 : NExpr) (hs1 : e1.scalarOnly = true) (ty1 : e1.resultType = i32) (value1 : e1.denote (envOf caller) = some (n : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.TreeFindRootInstance.tree_find_root.parameters [.vectorReference s0,.value e1] = some Sinit ∧
      Proofs.TreeFindRootInstance.tree_find_root.callFuel fuel caller [.vectorReference s0,.value e1] =
        .finished (res,.scalar (rootT Pr n)) ∧
      ScalarPostM (mvFR V0 vsc0 m0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) caller Sinit res e1.nodes (220 * n + 200) caller.scalars.memory 0 (VP Pr) := by
  have hn32 : n < 2147483648 := by omega
  obtain ⟨t1,g1,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak,sPeakT⟩ :=
    prepare_fr caller ok0 e1 (n : Int) hs1 ty1 value1 (validN n hn32)
  have fwS := fwFR_init caller ok0 Pr hP2 i0 bv0 l0 o0
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,⟨cs,hrps⟩,hcost,hneed,hwk⟩ :=
    body_exec (mvFR V0 vsc0 m0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) rfl rfl Pr (callerP caller) n hn32 hn hPl hPv (n + 2) (Nat.le_refl _)
  have hvalid : i32.valid (rootT Pr n) = true := by
    rcases rootT_range Pr n with h | h
    · rw [h]; decide
    · exact i32_valid_of_int _ (by omega)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)], [⟨(callerP caller).length,true⟩]⟩ : PS) =
      gS (callerP caller) [ci n] := by
    simp [gS]
  have gw := g1.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw
  have hpost := call_vecm (mvFR V0 vsc0 m0 caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) (fun _ => false)
    (by intro k hk; simp at hk)
    caller Proofs.TreeFindRootInstance.tree_find_root [.vectorReference s0,.value e1] Sinit
    (callerP caller ++ [(⟨i32,(n : Int)⟩ : Cell)]) [⟨(callerP caller).length,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok0.base (by rw [body_eqFR]; exact wr_bodyFR)
    (n + 2) rr (by rw [hmk, body_eqFR]; exact hexec) _ hret i32 rfl hvalid (by omega) (by simp [hlenP])
    e1.nodes (220 * n + 200) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv, hwk] at post
  exact post

end Proofs.TreeFindRootCall
