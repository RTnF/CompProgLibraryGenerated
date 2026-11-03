import Proofs.IsPrimePrepare
import Proofs.IsPrimeFun
import Proofs.CountrZeroCall
import Proofs.MultiVecCallB

namespace Proofs.IsPrimeCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.MultiVecCallB
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall Proofs.DoublingPrologue Proofs.DoublingCall
open Proofs.QuotientFrame Proofs.Mod61Body Proofs.VecCall Proofs.CppNestedFacts Proofs.ScalarCall Proofs.VecWriteCall
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.MatMulPrepare Proofs.IsPrimePrepare
open Proofs.CountrZeroCall (mvCZ fwCZ_init)
open Proofs.IsPrimeBody Proofs.IsPrimeExec Proofs.IsPrimeWit Proofs.IsPrimeTop Proofs.IsPrimeRun Proofs.IsPrimeFun Proofs.IsPrimeSpec
open Proofs.PowModStep (Sk)
open Proofs.ForLoop (ci)
open Proofs.LowerBoundIndexCall (validN)

theorem wr_isp : WrM (fun _ => false) (isBodyT 0) = true := by decide

theorem mrb_le37 (i : Nat) : mrb i ≤ 37 := by unfold mrb; repeat' (first | split | omega)
theorem wr_mul : WrM (fun _ => false) (mulBody 0 0 (.sequence (.primitive (.ret (vU 0 3))) Sk)) = true := by decide
theorem wr_pow : WrM (fun _ => false) (powBody 0 0 (.sequence (.primitive (.ret (vU 0 3))) Sk)) = true := by decide
theorem wr_base : WrM (fun _ => false) (mrBaseBody 0) = true := by decide
theorem wr_wit : WrM (fun _ => false) (witBodyB 0 0) = true := by decide
theorem body_eqWitB : Proofs.IsPrimeInstance.mr_witness.body = witBodyB 0 0 := body_eqWit



set_option maxHeartbeats 16000000 in
theorem mul_mod_u64_correct (caller : NState) (e1 e2 e3 : NExpr) (a b m : Nat) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true)
    (ty1 : e1.resultType = u64)
    (ty2 : e2.resultType = u64)
    (ty3 : e3.resultType = u64) (d1 : e1.denote (envOf caller) = some (a : Int)) (d2 : e2.denote (envOf caller) = some (b : Int)) (d3 : e3.denote (envOf caller) = some (m : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) (ha : a < m) (hb : b < m) (hm : m < 18446744073709551616) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.IsPrimeInstance.mul_mod_u64.parameters [.value e1, .value e2, .value e3] = some Sinit ∧
      Proofs.IsPrimeInstance.mul_mod_u64.callFuel fuel caller [.value e1, .value e2, .value e3] = .finished (res,.scalar (((a * b) % m : Nat) : Int)) ∧
      True ∧
      ScalarPostMB 1200 (mvCZ caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length)
        caller Sinit res (e1.nodes + e2.nodes + e3.nodes) (64 * 420 + 400 + 600) caller.scalars.memory 0 (fun _ => []) := by
  have vn1 : u64.valid (a : Int) = true := Proofs.DoublingNested.u64_valid_nat a (by omega)
  have vn2 : u64.valid (b : Int) = true := Proofs.DoublingNested.u64_valid_nat b (by omega)
  have vn3 : u64.valid (m : Int) = true := Proofs.DoublingNested.u64_valid_nat m (by omega)
  obtain ⟨t1,t2,t3,g1,g2,g3,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_mul caller valid e1 e2 e3 (a : Int) (b : Int) (m : Int) hs1 hs2 hs3 ty1 ty2 ty3 d1 d2 d3 vn1 vn2 vn3
  have fwS := fwCZ_init caller valid lengths strict
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,⟨cl,hrps⟩,hcost,hneed,hwk⟩ :=
    mul_fun (mvCZ caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) (callerP caller) a b m ha hb (by exact hm) (fun _ => []) 65 (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨u64,(a : Int)⟩ : Cell),(⟨u64,(b : Int)⟩ : Cell),(⟨u64,(m : Int)⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨u64,(a : Int)⟩ : Cell),(⟨u64,(b : Int)⟩ : Cell),(⟨u64,(m : Int)⟩ : Cell)], [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]⟩ : PS) =
      gS (callerP caller) [cu a, cu b, cu m] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  try simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have gw2 := g2.2.2.1
  try simp [NState.charge, NState.observe, CppState.State.observe] at gw2
  have gw3 := g3.2.2.1
  try simp [NState.charge, NState.observe, CppState.State.observe] at gw3
  have hv : u64.valid (((a * b) % m : Nat) : Int) = true := (Proofs.DoublingNested.u64_valid_nat ((a * b) % m) (by have := Nat.mod_lt (a * b) (show 0 < m by omega); omega))
  have hpost := call_vecmB 1200 (mvCZ caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) (fun _ => false) (by intro k hk; simp at hk)
    caller Proofs.IsPrimeInstance.mul_mod_u64 [.value e1, .value e2, .value e3] Sinit
    (callerP caller ++ [(⟨u64,(a : Int)⟩ : Cell),(⟨u64,(b : Int)⟩ : Cell),(⟨u64,(m : Int)⟩ : Cell)]) [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]
    hprep (by rw [sSlots]; simp [slN, ssl, List.range_succ, mvCZ]) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) base (by rw [body_eqMul]; exact wr_mul)
    65 rr (by rw [hmk, body_eqMul]; exact hexec) _ hret u64 rfl hv (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes + e3.nodes) (64 * 420 + 400 + 600) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,trivial,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv, hwk] at post
  exact post

set_option maxHeartbeats 16000000 in
theorem pow_mod_u64_correct (caller : NState) (e1 e2 e3 : NExpr) (x y m : Nat) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true)
    (ty1 : e1.resultType = u64)
    (ty2 : e2.resultType = u64)
    (ty3 : e3.resultType = u64) (d1 : e1.denote (envOf caller) = some (x : Int)) (d2 : e2.denote (envOf caller) = some (y : Int)) (d3 : e3.denote (envOf caller) = some (m : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) (hx : x < m) (hm2 : 2 ≤ m) (hm : m < 18446744073709551616) (hy : y < 18446744073709551616) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.IsPrimeInstance.pow_mod_u64.parameters [.value e1, .value e2, .value e3] = some Sinit ∧
      Proofs.IsPrimeInstance.pow_mod_u64.callFuel fuel caller [.value e1, .value e2, .value e3] = .finished (res,.scalar (((x ^ y) % m : Nat) : Int)) ∧
      True ∧
      ScalarPostMB 1200 (mvCZ caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length)
        caller Sinit res (e1.nodes + e2.nodes + e3.nodes) (64 * CPW 0 + 400 + 600) caller.scalars.memory 0 (fun _ => []) := by
  have vn1 : u64.valid (x : Int) = true := Proofs.DoublingNested.u64_valid_nat x (by omega)
  have vn2 : u64.valid (y : Int) = true := Proofs.DoublingNested.u64_valid_nat y (by omega)
  have vn3 : u64.valid (m : Int) = true := Proofs.DoublingNested.u64_valid_nat m (by omega)
  obtain ⟨t1,t2,t3,g1,g2,g3,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_pow caller valid e1 e2 e3 (x : Int) (y : Int) (m : Int) hs1 hs2 hs3 ty1 ty2 ty3 d1 d2 d3 vn1 vn2 vn3
  have fwS := fwCZ_init caller valid lengths strict
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,⟨cl,hrps⟩,hcost,hneed,hwk⟩ :=
    pow_fun (mvCZ caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) (callerP caller) x y m hx hm2 (by exact hm) (by exact hy) (fun _ => []) 129 (by omega)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨u64,(x : Int)⟩ : Cell),(⟨u64,(y : Int)⟩ : Cell),(⟨u64,(m : Int)⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨u64,(x : Int)⟩ : Cell),(⟨u64,(y : Int)⟩ : Cell),(⟨u64,(m : Int)⟩ : Cell)], [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]⟩ : PS) =
      gS (callerP caller) [cu x, cu y, cu m] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  try simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have gw2 := g2.2.2.1
  try simp [NState.charge, NState.observe, CppState.State.observe] at gw2
  have gw3 := g3.2.2.1
  try simp [NState.charge, NState.observe, CppState.State.observe] at gw3
  have hv : u64.valid (((x ^ y) % m : Nat) : Int) = true := (Proofs.DoublingNested.u64_valid_nat ((x ^ y) % m) (by have := Nat.mod_lt (x ^ y) (show 0 < m by omega); omega))
  have hpost := call_vecmB 1200 (mvCZ caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) (fun _ => false) (by intro k hk; simp at hk)
    caller Proofs.IsPrimeInstance.pow_mod_u64 [.value e1, .value e2, .value e3] Sinit
    (callerP caller ++ [(⟨u64,(x : Int)⟩ : Cell),(⟨u64,(y : Int)⟩ : Cell),(⟨u64,(m : Int)⟩ : Cell)]) [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]
    hprep (by rw [sSlots]; simp [slN, ssl, List.range_succ, mvCZ]) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) base (by rw [body_eqPowMod]; exact wr_pow)
    129 rr (by rw [hmk, body_eqPowMod]; exact hexec) _ hret u64 rfl hv (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes + e3.nodes) (64 * CPW 0 + 400 + 600) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,trivial,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv, hwk] at post
  exact post

set_option maxHeartbeats 16000000 in
theorem mr_base_correct (caller : NState) (e1 : NExpr) (i : Nat) (hs1 : e1.scalarOnly = true)
    (ty1 : e1.resultType = i32) (d1 : e1.denote (envOf caller) = some (i : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) (hi : i < 2147483648) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.IsPrimeInstance.mr_base.parameters [.value e1] = some Sinit ∧
      Proofs.IsPrimeInstance.mr_base.callFuel fuel caller [.value e1] = .finished (res,.scalar ((mrb i : Nat) : Int)) ∧
      (mrb i = if i = 0 then 2 else if i = 1 then 3 else if i = 2 then 5 else if i = 3 then 7 else if i = 4 then 11 else if i = 5 then 13 else if i = 6 then 17 else if i = 7 then 19 else if i = 8 then 23 else if i = 9 then 29 else if i = 10 then 31 else 37) ∧
      ScalarPostMB 1200 (mvCZ caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length)
        caller Sinit res (e1.nodes) (800 + 600) caller.scalars.memory 0 (fun _ => []) := by
  have vn1 : i32.valid (i : Int) = true := Proofs.IsPrimeExec.i32vn i (by omega)
  obtain ⟨t1,g1,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_base caller valid e1 (i : Int) hs1 ty1 d1 vn1
  have fwS := fwCZ_init caller valid lengths strict
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,⟨cl,hrps⟩,hcost,hneed,hwk⟩ :=
    base_fun (mvCZ caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) (callerP caller) i hi (fun _ => []) 10 
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨i32,(i : Int)⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨i32,(i : Int)⟩ : Cell)], [⟨(callerP caller).length,true⟩]⟩ : PS) =
      gS (callerP caller) [cI i] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  try simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have hv : u64.valid ((mrb i : Nat) : Int) = true := (Proofs.DoublingNested.u64_valid_nat (mrb i) (by have := mrb_le37 i; omega))
  have hpost := call_vecmB 1200 (mvCZ caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) (fun _ => false) (by intro k hk; simp at hk)
    caller Proofs.IsPrimeInstance.mr_base [.value e1] Sinit
    (callerP caller ++ [(⟨i32,(i : Int)⟩ : Cell)]) [⟨(callerP caller).length,true⟩]
    hprep (by rw [sSlots]; simp [slN, ssl, List.range_succ, mvCZ]) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) base (by rw [body_eqBase]; exact wr_base)
    10 rr (by rw [hmk, body_eqBase]; exact hexec) _ hret u64 rfl hv (by omega) (by simp [hlenP])
    (e1.nodes) (800 + 600) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,rfl,?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv, hwk] at post
  exact post

set_option maxHeartbeats 16000000 in
theorem mr_witness_correct (caller : NState) (e1 e2 e3 e4 : NExpr) (n d r a : Nat) (hs1 : e1.scalarOnly = true) (hs2 : e2.scalarOnly = true) (hs3 : e3.scalarOnly = true) (hs4 : e4.scalarOnly = true)
    (ty1 : e1.resultType = u64)
    (ty2 : e2.resultType = u64)
    (ty3 : e3.resultType = i32)
    (ty4 : e4.resultType = u64) (d1 : e1.denote (envOf caller) = some (n : Int)) (d2 : e2.denote (envOf caller) = some (d : Int)) (d3 : e3.denote (envOf caller) = some (r : Int)) (d4 : e4.denote (envOf caller) = some (a : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) (hn : 2 ≤ n) (hnm : n < 18446744073709551616) (hr : r < 2147483640) (ha : a < n) (hd : d < 18446744073709551616) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.IsPrimeInstance.mr_witness.parameters [.value e1, .value e2, .value e3, .value e4] = some Sinit ∧
      Proofs.IsPrimeInstance.mr_witness.callFuel fuel caller [.value e1, .value e2, .value e3, .value e4] = .finished (res,.scalar (if mrwx n r (a ^ d % n) then 1 else 0 : Int)) ∧
      (n - 1 = d * 2 ^ r → 0 < a → mrwx n r (a ^ d % n) = true → ¬ Proofs.Fermat.IsPrime n) ∧
      ScalarPostMB 1200 (mvCZ caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length)
        caller Sinit res (e1.nodes + e2.nodes + e3.nodes + e4.nodes) (64 * CPW 0 + CWr r + 2100 + 600) caller.scalars.memory 0 (fun _ => []) := by
  have vn1 : u64.valid (n : Int) = true := Proofs.DoublingNested.u64_valid_nat n (by omega)
  have vn2 : u64.valid (d : Int) = true := Proofs.DoublingNested.u64_valid_nat d (by omega)
  have vn3 : i32.valid (r : Int) = true := Proofs.IsPrimeExec.i32vn r (by omega)
  have vn4 : u64.valid (a : Int) = true := Proofs.DoublingNested.u64_valid_nat a (by omega)
  obtain ⟨t1,t2,t3,t4,g1,g2,g3,g4,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_wit caller valid e1 e2 e3 e4 (n : Int) (d : Int) (r : Int) (a : Int) hs1 hs2 hs3 hs4 ty1 ty2 ty3 ty4 d1 d2 d3 d4 vn1 vn2 vn3 vn4
  have fwS := fwCZ_init caller valid lengths strict
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,⟨cl,hrps⟩,hcost,hneed,hwk⟩ :=
    wit_fun (mvCZ caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) (callerP caller) n d r a hn hnm hr ha hd (fun _ => []) (r + 200) (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨u64,(n : Int)⟩ : Cell),(⟨u64,(d : Int)⟩ : Cell),(⟨i32,(r : Int)⟩ : Cell),(⟨u64,(a : Int)⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨u64,(n : Int)⟩ : Cell),(⟨u64,(d : Int)⟩ : Cell),(⟨i32,(r : Int)⟩ : Cell),(⟨u64,(a : Int)⟩ : Cell)], [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩]⟩ : PS) =
      gS (callerP caller) [cu n, cu d, cI r, cu a] := by
    simp [gS, List.range_succ]
  have gw1 := g1.2.2.1
  try simp [NState.charge, NState.observe, CppState.State.observe] at gw1
  have gw2 := g2.2.2.1
  try simp [NState.charge, NState.observe, CppState.State.observe] at gw2
  have gw3 := g3.2.2.1
  try simp [NState.charge, NState.observe, CppState.State.observe] at gw3
  have gw4 := g4.2.2.1
  try simp [NState.charge, NState.observe, CppState.State.observe] at gw4
  have hv : bT.valid (if mrwx n r (a ^ d % n) then 1 else 0 : Int) = true := (by cases mrwx n r (a ^ d % n) <;> decide)
  have hpost := call_vecmB 1200 (mvCZ caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) (fun _ => false) (by intro k hk; simp at hk)
    caller Proofs.IsPrimeInstance.mr_witness [.value e1, .value e2, .value e3, .value e4] Sinit
    (callerP caller ++ [(⟨u64,(n : Int)⟩ : Cell),(⟨u64,(d : Int)⟩ : Cell),(⟨i32,(r : Int)⟩ : Cell),(⟨u64,(a : Int)⟩ : Cell)]) [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩,⟨(callerP caller).length+3,true⟩]
    hprep (by rw [sSlots]; simp [slN, ssl, List.range_succ, mvCZ]) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) base (by rw [body_eqWitB]; exact wr_wit)
    (r + 200) rr (by rw [hmk, body_eqWitB]; exact hexec) _ hret bT rfl hv (by omega) (by simp [hlenP])
    (e1.nodes + e2.nodes + e3.nodes + e4.nodes) (64 * CPW 0 + CWr r + 2100 + 600) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,(fun hnd ha0 hw hp => by have := Proofs.IsPrimeMr.mrwx_prime n d r a hp ha0 ha hnd; rw [this] at hw; exact absurd hw (by simp)),?_⟩
  have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [gS_mem, callerP, List.append_assoc]
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_length
  rw [hs', hrvv, hwk] at post
  exact post

set_option maxHeartbeats 16000000 in
/-- `cp::is_prime(n)` returns `ispSpec n`: `true` for every prime; for a composite `n`, `false` provided the first twelve primes
form a Miller-Rabin witness set (`MRWitnessSet`, a published computation that is not proved here). -/
theorem is_prime_correct (caller : NState) (e1 : NExpr) (n : Nat) (hs1 : e1.scalarOnly = true)
    (ty1 : e1.resultType = u64) (d1 : e1.denote (envOf caller) = some (n : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) (hn : n < 18446744073709551616) :
    ∃ (Sinit : NState) (fuel : Nat) (res : NState),
      prepare caller Proofs.IsPrimeInstance.is_prime.parameters [.value e1] = some Sinit ∧
      Proofs.IsPrimeInstance.is_prime.callFuel fuel caller [.value e1] =
        .finished (res,.scalar (if ispSpec n then 1 else 0)) ∧
      (Proofs.Fermat.IsPrime n → ispSpec n = true) ∧ (MRWitnessSet → ispSpec n = true → Proofs.Fermat.IsPrime n) ∧
      ScalarPostMB 1200 (mvCZ caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
        caller.frame.state.storage.objects.length)
        caller Sinit res e1.nodes (TOPC + 400) caller.scalars.memory 0 (fun _ => []) := by
  have vn : u64.valid (n : Int) = true := Proofs.DoublingNested.u64_valid_nat n hn
  obtain ⟨t1,g1,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeakT,sPeak⟩ :=
    prepare_isp caller valid e1 (n : Int) hs1 ty1 d1 vn
  have fwS := fwCZ_init caller valid lengths strict
  rw [← sFrame] at fwS
  obtain ⟨rr,hexec,hret,hrvv,⟨cl,hrps⟩,hcost,hneed,hwk⟩ :=
    is_prime_fun (mvCZ caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) (callerP caller) n hn (fun _ => []) 400 (Nat.le_refl _)
  have hlenP : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨u64,(n : Int)⟩ : Cell)]).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hmk : (⟨callerP caller ++ [(⟨u64,(n : Int)⟩ : Cell)], [⟨(callerP caller).length,true⟩]⟩ : PS) =
      gS (callerP caller) [cu n] := by
    simp [gS]
  have gw := g1.2.2.1
  try simp [NState.charge, NState.observe, CppState.State.observe] at gw
  have hv : bT.valid (if ispSpec n then 1 else 0 : Int) = true := by cases ispSpec n <;> decide
  have hpost := call_vecmB 1200 (mvCZ caller.frame.state.liveSpace caller.frame.state.storage.work (caller.scope + 1)
      caller.frame.state.storage.objects.length) (fun _ => false) (by intro k hk; simp at hk)
    caller Proofs.IsPrimeInstance.is_prime [.value e1] Sinit
    (callerP caller ++ [(⟨u64,(n : Int)⟩ : Cell)]) [⟨(callerP caller).length,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope (by rw [sFrame]) (by rw [sFrame]) fwS rfl rfl rfl rfl
    (by omega) (by simp [hlenP]; omega) (by rw [takeM]) base (by rw [body_eqIsPrime]; exact wr_isp)
    400 rr (by rw [hmk, body_eqIsPrime]; exact hexec) _ hret bT rfl hv (by omega) (by simp [hlenP])
    e1.nodes (TOPC + 400) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_,?_,?_⟩
  · exact ispSpec_prime n hn
  · intro H h
    exact ispSpec_true_prime H n hn h
  · have hs' : rr.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
      rw [hrps]
      simp only [gS_mem, callerP, List.append_assoc]
      rw [List.take_append_of_le_length (by simp)]
      exact List.take_length
    rw [hs', hrvv, hwk] at post
    exact post

end Proofs.IsPrimeCall
