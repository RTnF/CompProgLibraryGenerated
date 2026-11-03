import Proofs.TreeLcaPrepare
import Proofs.TreeLcaExec
import Proofs.TreeAncestorCall

namespace Proofs.TreeLcaCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVecN Proofs.MultiKitN Proofs.MultiVecCallN
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.NestedReadOnly
open Proofs.Vector2dSumCall (NOKG rowsVV rowsVV_row bbV)
open Proofs.TreeAncestorCall (mvTA fwTA_init)
open Proofs.TreeLcaPrepare Proofs.TreeLcaExec
open Proofs.TreeAncestorMath (tab itr)
open Proofs.TreeLcaMath (TabAll TreeF descA lca_spec)
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec (M31)

theorem wr_bodyLC : WrM (fun _ => false) (bodyLC 1) = true := by simp [WrM]

set_option maxHeartbeats 16000000 in
/-- `cp::tree_lca_same_depth(anc, u, v, depth)` returns the vertex where the trajectories of `u` and `v` (of the same depth
`depth` in a rooted tree) first meet. -/
theorem tree_lca_same_depth_correct (caller : NState) {vslot vb V vsc : Nat} {T : List (List Nat)} {wb m : Bool}
    (ok : NOKG caller i32 vslot vb V vsc (T.map (fun r => r.map (fun x : Nat => (x : Int)))) wb m)
    (f : Nat → Nat) (N root K u v dep : Nat) (d : Nat → Nat) (TF : TreeF f N root d)
    (hN : N < 2147483648) (hu : u < N) (hv : v < N) (hdu : d u = dep) (hdv : d v = dep) (hdep : dep < 1073741824)
    (hK : dep < 2 ^ (K + 1)) (hK30 : K < 30) (H : TabAll T f N K) (hKT : K + 1 ≤ T.length)
    (hT : T.length < 2147483647) (hL : ∀ r ∈ T, r.length < 2147483647)
    (e1 e2 e3 : NExpr) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true)
    (ty1 : e1.resultType = i32) (ty2 : e2.resultType = i32) (ty3 : e3.resultType = i32)
    (value1 : e1.denote (envOf caller) = some (u : Int)) (value2 : e2.denote (envOf caller) = some (v : Int))
    (value3 : e3.denote (envOf caller) = some (dep : Int)) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState) (w : Nat),
      prepare caller Proofs.TreeLcaInstance.tree_lca_same_depth.parameters
        [.vectorReference vslot,.value e1,.value e2,.value e3] = some Sinit ∧
      Proofs.TreeLcaInstance.tree_lca_same_depth.callFuel fuel caller
        [.vectorReference vslot,.value e1,.value e2,.value e3] = .finished (res,.scalar (w : Int)) ∧ w < N ∧
      (∃ k, itr f k u = w ∧ itr f k v = w ∧ ∀ s, s < k → itr f s u ≠ itr f s v) ∧
      ScalarPostM (mvTA V vsc m (T.map (fun r => r.map (fun x : Nat => (x : Int)))) caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length)
        caller Sinit res (e1.nodes + e2.nodes + e3.nodes) (300 * (K + 1) + 500) caller.scalars.memory 0
        (rowsVV (T.map (fun r => r.map (fun x : Nat => (x : Int))))) := by
  have hNM : N < M31 := hN
  have huM : u < 2147483648 := by omega
  have hvM : v < 2147483648 := by omega
  have hdM : dep < 2147483648 := by omega
  generalize hRW : T.map (fun r : List Nat => r.map (fun x : Nat => (x : Int))) = rows at ok ⊢
  obtain ⟨t1,t2,t3,g1,g2,g3,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_lc caller ok e1 e2 e3 (u : Int) (v : Int) (dep : Int) hs1 hs2 hs3 ty1 ty2 ty3 value1 value2 value3
      (validN u huM) (validN v hvM) (validN dep hdM)
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
  obtain ⟨rr,w,top',hexec,hret,hdt,htopK,hw1,hw2,hwN,hrvv,⟨cs,hrps⟩,hcost,hneed,hwk⟩ :=
    body_exec (mvTA V vsc m rows caller.frame.state.liveSpace
      caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length) rfl rfl rfl T f N K u v dep
    (rowsVV rows) (callerP caller) hNM hu hv hdep hK H hK30 hrowsE (by show K + 1 ≤ rows.length; omega) (dep + 40) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(u : Int)⟩ : Cell),(⟨i32,(v : Int)⟩ : Cell),(⟨i32,(dep : Int)⟩ : Cell)]).take
      caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(u : Int)⟩ : Cell),(⟨i32,(v : Int)⟩ : Cell),(⟨i32,(dep : Int)⟩ : Cell)],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]⟩ : PS) =
      gS (callerP caller) [ci u, ci v, ci dep] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  have gw2 := g2.2.2.1
  have gw3 := g3.2.2.1
  simp [NState.charge, NState.observe, CppState.State.observe] at gw1 gw2 gw3
  have hwM : w < 2147483648 := by omega
  have hpost := call_vecm (mvTA V vsc m rows caller.frame.state.liveSpace
        caller.frame.state.storage.work (caller.scope + 1) caller.frame.state.storage.objects.length) (fun _ => false)
    (by intro k hk; simp at hk)
    caller Proofs.TreeLcaInstance.tree_lca_same_depth [.vectorReference vslot,.value e1,.value e2,.value e3] Sinit
    (callerP caller ++ [(⟨i32,(u : Int)⟩ : Cell),(⟨i32,(v : Int)⟩ : Cell),(⟨i32,(dep : Int)⟩ : Cell)])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) ok.base (by rw [body_eqLC]; exact wr_bodyLC)
    (dep + 40) rr (by rw [hmk, body_eqLC]; exact hexec) (w : Int) hret i32 rfl (validN _ hwM) (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes + e3.nodes) (300 * (K + 1) + 500) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  have hmeet : ∃ k, itr f k u = w ∧ itr f k v = w ∧ ∀ s, s < k → itr f s u ≠ itr f s v := by
    by_cases huv : u = v
    · subst huv
      exact ⟨0, by rw [hw1 rfl]; rfl, by rw [hw1 rfl]; rfl, fun s hs => absurd hs (by omega)⟩
    · have hHK : TabAll T f N top' := fun k hk' x hx => H k (by omega) x hx
      obtain ⟨k, hk1, hk2, hk3⟩ := lca_spec T f N root d TF u v top' hu hv (by rw [hdu, hdv]) (by rw [hdu]; exact hdt) hHK huv
      exact ⟨k, by rw [hw2 huv, hk3], by rw [← hk1, hw2 huv, hk3], hk2⟩
  refine ⟨Sinit,fuel,res,w,hprep,hrun,hwN,hmeet,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv, hwk] at post
  exact post

end Proofs.TreeLcaCall
