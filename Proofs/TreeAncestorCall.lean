import Proofs.TreeAncestorPrepare
import Proofs.TreeAncestorExec

namespace Proofs.TreeAncestorCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVecN Proofs.MultiKitN Proofs.MultiVecCallN
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.NestedReadOnly
open Proofs.Vector2dSumCall (NOKG rowsVV rowsVV_row bbV)
open Proofs.TreeAncestorPrepare Proofs.TreeAncestorExec
open Proofs.TreeAncestorMath (TabOK ancQ itr tab bits anc_spec)
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (M31)

def mvTA (V vsc : Nat) (m : Bool) (rows : List (List Int)) (L0 T0 sc N : Nat) : MV where
  nv := 1
  ty := fun _ => i32
  wV := fun _ => false
  flag := fun _ => m
  R := fun _ => V
  vsc := fun _ => vsc
  perm := by intro k hk; simp at hk
  L0 := L0
  T0 := T0
  sc := sc
  N := N
  distinct := by intro j k hj hk hjk hw; simp at hw
  flat := fun _ => false
  wflat := by intro k hk; simp at hk
  wN := fun _ => false
  permN := by intro k hk; simp at hk
  wNnest := by intro k hk; simp at hk
  wrows := fun _ => rows.length
  nvSmall := by decide
  rfree := by intro j k i hj hk hf; simp at hf
  nfree := by
    intro k k' i i' hk hk' hf hf' hi hi' hne
    have hk0 : k = 0 := by simpa using hk
    have hk1 : k' = 0 := by simpa using hk'
    subst hk0; subst hk1
    have : i ≠ i' := by rcases hne with h | h; exact absurd rfl h; exact h
    show V + 1 + i ≠ V + 1 + i'
    omega
  nroot := by intro k k' i hk hk' hf hf' hi; show V ≠ V + 1 + i; omega
  wfree := by intro j k hj hk hw; simp at hw

theorem fwTA_init (caller : NState) {vslot vb V vsc : Nat} {rows : List (List Int)} {wb m : Bool}
    (ok : NOKG caller i32 vslot vb V vsc rows wb m) (hR : rows.length < 4294967296)
    (hs2 : ∀ i (h : i < rows.length), (rows[i]).length < 2^64) :
    FWM (mvTA V vsc m rows caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length) (rowsVV rows) bbV 0
      (⟨caller.frame.state, caller.frame.rootWritable, [⟨V,.vector (.integer i32),false,.root vsc⟩]⟩ : Frame) := by
  refine ⟨ok.valid, ok.lengths, rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro owner k h
    have := ok.strict owner k h
    show k < caller.scope + 1
    omega
  · simp [bindOf, mvTA]
  · intro k hk hf; simp [mvTA] at hf
  · intro k hk hf; simp [mvTA] at hf
  · intro k hk hf; simp [mvTA] at hf
  · intro k hk hf; simp [mvTA] at hf
  · intro k hk hf; simp [mvTA] at hf
  · intro k hk hf; simp [mvTA] at hf
  · intro k hk hf; simp [mvTA] at hf
  · intro k hk hf; simp [mvTA] at hf
  · intro k hk hn
    have hk0 : k = 0 := by simp [mvTA] at hk; omega
    subst hk0
    refine ⟨by simp [mvTA]; omega, ?_, ok.graph, ok.flag, ?_⟩
    · intro i hi
      simp only [mvTA] at hi
      rw [rowsVV_row rows hR i hi]; exact hs2 i hi
    · intro i hi
      simp only [mvTA] at hi
      rw [rowsVV_row rows hR i hi]; exact ok.rowsStore i hi

theorem wr_bodyAN : WrM (fun _ => false) (bodyAN 1) = true := by simp [WrM]

set_option maxHeartbeats 16000000 in
/-- `cp::tree_ancestor(anc, v, i)` returns the `i`-th ancestor `f^[i] v`, when the table `anc` holds the `2^k`-th ancestors of
the function `f`. -/
theorem tree_ancestor_correct (caller : NState) {vslot vb V vsc : Nat} {T : List (List Nat)} {wb m : Bool}
    (ok : NOKG caller i32 vslot vb V vsc (T.map (fun r => r.map (fun x : Nat => (x : Int)))) wb m)
    (f : Nat → Nat) (N i v : Nat) (hN : N < 2147483648) (hi : i < 1073741824) (H : TabOK T f N i) (hv : v < N)
    (hT : T.length < 2147483647) (hL : ∀ r ∈ T, r.length < 2147483647)
    (e1 e2 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (ty1 : e1.resultType = i32)
    (ty2 : e2.resultType = i32) (value1 : e1.denote (envOf caller) = some (v : Int))
    (value2 : e2.denote (envOf caller) = some (i : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.TreeAncestorInstance.tree_ancestor.parameters
        [.vectorReference vslot,.value e1,.value e2] = some Sinit ∧
      Proofs.TreeAncestorInstance.tree_ancestor.callFuel fuel caller [.vectorReference vslot,.value e1,.value e2] =
        .finished (res,.scalar ((itr f i v : Nat) : Int)) ∧ itr f i v < N ∧
      ScalarPostM (mvTA V vsc m (T.map (fun r => r.map (fun x : Nat => (x : Int)))) caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
        caller Sinit res (e1.nodes + e2.nodes) (210 * bits i + 300) caller.scalars.memory 0
        (rowsVV (T.map (fun r => r.map (fun x : Nat => (x : Int))))) := by
  have hNM : N < M31 := hN
  have hvM : v < 2147483648 := by omega
  have hiM : i < 2147483648 := by omega
  generalize hRW : T.map (fun r : List Nat => r.map (fun x : Nat => (x : Int))) = rows at ok ⊢
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_ta caller ok e1 e2 (v : Int) (i : Int) hs1 hs2 ty1 ty2 value1 value2 (validN v hvM) (validN i hiM)
  have hlen : rows.length = T.length := by rw [← hRW]; simp
  have hR' : rows.length < 4294967296 := by rw [hlen]; omega
  have hs2' : ∀ k (h : k < rows.length), (rows[k]).length < 2 ^ 64 := by
    intro k h
    subst hRW
    have hk : k < T.length := by simpa using h
    have := hL (T[k]) (List.getElem_mem hk)
    simp only [List.getElem_map, List.length_map]
    have h64 : (2147483647 : Nat) < 2 ^ 64 := by norm_num
    omega
  have fwS := fwTA_init caller ok hR' hs2'
  rw [← sFrame] at fwS
  have hrowsE : ∀ t, t < rows.length → rowsVV rows (rowKey 0 t) = (T.getD t []).map (fun x : Nat => (x : Int)) := by
    intro t ht
    rw [rowsVV_row _ hR' t ht]
    subst hRW
    have ht' : t < T.length := by simpa using ht
    simp [List.getD_eq_getElem?_getD, ht']
  have hwrE : ∀ k, 2 ^ k ≤ i → k < rows.length := by
    intro k hk
    rw [hlen]
    obtain ⟨_, _, h3⟩ := H k hk v hv
    by_contra hge
    have : T.getD k [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [this] at h3
    simp at h3
  obtain ⟨rr,k',j',hexec,hret,hrps,hrvv,hcost,hneed,hwk⟩ :=
    body_exec (mvTA V vsc m rows caller.frame.state.liveSpace
      caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length) rfl rfl rfl T f N i v
    (rowsVV rows) (callerP caller) hNM hi H hv hrowsE hwrE (i + 2) (Nat.le_refl _)
  have hspec := anc_spec T f N i v H hv
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(v : Int)⟩ : Cell),(⟨i32,(i : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(v : Int)⟩ : Cell),(⟨i32,(i : Int)⟩ : Cell)],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]⟩ : PS) = gS (callerP caller) [ci v, ci i] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2
  have hfin : itr f i v < N := by rw [← hspec.1]; exact hspec.2
  have hpost := call_vecm (mvTA V vsc m rows caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length) (fun _ => false)
    (by intro k hk; simp at hk)
    caller Proofs.TreeAncestorInstance.tree_ancestor [.vectorReference vslot,.value e1,.value e2] Sinit
    (callerP caller ++ [(⟨i32,(v : Int)⟩ : Cell),(⟨i32,(i : Int)⟩ : Cell)])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok.base (by rw [body_eqAN]; exact wr_bodyAN)
    (i + 2) rr (by rw [hmk, body_eqAN]; exact hexec) ((ancQ T i 0 v : Nat) : Int) hret i32 rfl
    (validN _ (by have := hspec.2; omega)) (by omega) (by simp [hlenP]) (e1.nodes + e2.nodes) (210 * bits i + 300) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  rw [hspec.1] at hrun
  refine ⟨Sinit,fuel,res,hprep,hrun,hfin,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv, hwk] at post
  exact post

end Proofs.TreeAncestorCall
