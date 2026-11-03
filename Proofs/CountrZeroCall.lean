import Proofs.CountrZeroPrepare
import Proofs.CountrZeroExec
import Proofs.MultiVecCall

namespace Proofs.CountrZeroCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCall
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.CountrZeroPrepare Proofs.CountrZeroExec
open Proofs.BellmanFordExec (cs)
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)

/-- The callee of `countr_zero_u64`: no vectors. -/
def mvCZ (L0 T0 sc N : Nat) : MV where
  nv := 0
  ty := fun _ => u64
  wV := fun _ => false
  flag := fun _ => false
  R := fun _ => 0
  vsc := fun _ => 0
  perm := by intro k hk; simp at hk
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by intro j k hj hk hjk hw; simp at hw

theorem wr_bodyCZ : WrM (fun _ => false) (bodyCZ 0) = true := by decide

theorem fwCZ_init (caller : NState) (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope) :
    FWM (mvCZ caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) (fun _ => []) (fun _ => (⟨0, [], 0, 0, 0⟩ : Buffer Value)) 0
      (⟨caller.frame.state, caller.frame.rootWritable, []⟩ : Frame) := by
  refine ⟨valid, lengths, rfl, rfl, ?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := strict owner k h
    show k < caller.scope + 1
    omega
  all_goals (intro k hk; simp [mvCZ] at hk)

set_option maxHeartbeats 8000000 in
/-- `cp::countr_zero_u64(n)` returns the number of trailing zero bits of `n` (64 for `n = 0`). -/
theorem countr_zero_u64_correct (caller : NState) (e1 : NExpr) (n : Nat) (hs1 : e1.scalarOnly = true)
    (ty1 : e1.resultType = u64) (d1 : e1.denote (envOf caller) = some (n : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) (hn : n < 18446744073709551616) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.CountrZeroInstance.countr_zero_u64.parameters [.value e1] = some Sinit ∧
      Proofs.CountrZeroInstance.countr_zero_u64.callFuel fuel caller [.value e1] = .finished (res,.scalar ((cz 64 n : Nat) : Int)) ∧
      (n ≠ 0 → 2 ^ cz 64 n ∣ n ∧ ¬ 2 ^ (cz 64 n + 1) ∣ n) ∧ (n = 0 → cz 64 n = 64) ∧
      ScalarPostM (mvCZ caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length)
        caller Sinit res e1.nodes 13100 caller.scalars.memory 0 (fun _ => []) := by
  have vn : u64.valid (n : Int) = true := Proofs.DoublingNested.u64_valid_nat n hn
  obtain ⟨t1,g1,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_ta caller e1 (n : Int) hs1 ty1 d1 valid vn
  have fwS := fwCZ_init caller valid lengths strict
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,⟨cl,hrps⟩,hcost,hneed,hwk⟩ :=
    body_exec (mvCZ caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) rfl (callerP caller) (fun _ => []) n hn 66 (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨u64,(n : Int)⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨u64,(n : Int)⟩ : Cell)], [⟨(callerP caller).length,true⟩]⟩ : PS) =
      gS (callerP caller) [cu n] := by
    simp [gS]
  have gw := g1.2.2.1
  try simp [NState.charge, NState.observe, CppState.State.observe] at gw
  have hv : i32.valid ((cz 64 n : Nat) : Int) = true := by
    have := cz_le 64 n
    exact Proofs.TopoSortExec.i32v _ (by show cz 64 n < 2147483648; omega)
  have hpost := call_vecm (mvCZ caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) (fun _ => false) (by intro k hk; simp at hk)
    caller Proofs.CountrZeroInstance.countr_zero_u64 [.value e1] Sinit
    (callerP caller ++ [(⟨u64,(n : Int)⟩ : Cell)]) [⟨(callerP caller).length,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) base (by rw [body_eqCZ]; exact wr_bodyCZ)
    66 rr (by rw [hmk, body_eqCZ]; exact hexec) _ hret i32 rfl hv (by omega) (by simp [hlenP])
    e1.nodes 13100 (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_,?_,?_⟩
  · intro hne
    exact cz_spec 64 n hne (by exact_mod_cast hn)
  · intro h0; subst h0; exact cz_zero 64
  · have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
      rw [hrps]
      simp only [gS_mem, callerP, List.append_assoc]
      rw [List.take_append_of_le_length (by simp)]
      exact List.take_length
    rw [hs', hrvv] at post
    exact post.relax (Nat.le_refl _) (Nat.le_refl _) (by omega)

end Proofs.CountrZeroCall
