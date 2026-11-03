import Proofs.PowModStep
import Proofs.Generated.PowMod
import Proofs.Mod61Call
import Proofs.ScalarStraight

namespace Proofs.PowModCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.PowModStep Proofs.StraightLine
open Proofs.QuotientSearch Proofs.Mod61Body Proofs.DoublingNested
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.ScalarStraight

theorem body_eq : Proofs.PowModInstance.pow_mod.body =
    .sequence (.primitive (.declare u64 true initR)) (.sequence (.primitive (.declare u64 true initB))
      (.sequence (.primitive (.declare u64 true initE)) (.sequence LoopCmd
        (.sequence (.primitive (.ret (.variable u64 3))) Sk)))) := rfl


theorem env3 (P : List Cell) (base exp m : Nat) (hb : base < 18446744073709551616) (he : exp < 18446744073709551616)
    (hm : m < 18446744073709551616) :
    penv (mk P [base,exp,m]) 0 u64 = some (base : Int) ∧ penv (mk P [base,exp,m]) 1 u64 = some (exp : Int) ∧
    penv (mk P [base,exp,m]) 2 u64 = some (m : Int) := by
  have hv : ∀ x ∈ [base,exp,m], x < 18446744073709551616 := by
    intro x hx; simp at hx; omega
  have k := penv_mk P [base,exp,m] hv
  exact ⟨k 0 (by simp),k 1 (by simp),k 2 (by simp)⟩

theorem body_exec (P : List Cell) (base exp m : Nat) (hb : base < 18446744073709551616) (he : exp < 18446744073709551616)
    (hm : 0 < m) (hm' : m ≤ 4294967296) :
    ∃ r1 bF, pexec 70 Proofs.PowModInstance.pow_mod.body (mk P [base,exp,m]) = some r1 ∧
      r1.ret = some ((pw m 64 (1 % m) (base % m) exp : Nat) : Int) ∧ r1.cost ≤ 3000 ∧ r1.need ≤ P.length+12+40 ∧
      r1.ps = mk P (sv base exp m (pw m 64 (1 % m) (base % m) exp) bF 0) := by
  obtain ⟨e0,e1,e2⟩ := env3 P base exp m hb he (by omega)
  have d1 := initR_value (penv (mk P [base,exp,m])) m hm (by omega) e2
  have x1 : 1 % m < 18446744073709551616 := by have := Nat.mod_le 1 m; omega
  have s1 := mk_decl P [base,exp,m] initR (1 % m) x1 d1
  have hv4 : ∀ y ∈ [base,exp,m,1 % m], y < 18446744073709551616 := by
    intro y hy; simp at hy; omega
  have k4 := penv_mk P [base,exp,m,1 % m] hv4
  have d2 := initB_value (penv (mk P [base,exp,m,1 % m])) base m hm hb (k4 0 (by simp)) (k4 2 (by simp))
  have x2 : base % m < 18446744073709551616 := by have := Nat.mod_le base m; omega
  have s2 := mk_decl P [base,exp,m,1 % m] initB (base % m) x2 d2
  have hv5 : ∀ y ∈ [base,exp,m,1 % m,base % m], y < 18446744073709551616 := by
    intro y hy; simp at hy; omega
  have k5 := penv_mk P [base,exp,m,1 % m,base % m] hv5
  have d3 := initE_value (penv (mk P [base,exp,m,1 % m,base % m])) exp (k5 1 (by simp))
  have s3 := mk_decl P [base,exp,m,1 % m,base % m] initE exp he d3
  have hok : Ok base exp m (1 % m) (base % m) exp :=
    ⟨hb,he,hm,hm',Nat.mod_lt _ hm,Nat.mod_lt _ hm,he⟩
  have hexp : exp < 2^64 := by simpa using he
  obtain ⟨rl,bF,hl,hlps,hbF,hlret,hlcost,hlneed⟩ := loop_exec P 64 70 (by omega) hok hexp
  have hrFlt : pw m 64 (1 % m) (base % m) exp < m := by
    rw [pw_spec m hm 64 _ _ _ hexp (Nat.mod_lt _ hm)]; exact Nat.mod_lt _ hm
  have hokF : Ok base exp m (pw m 64 (1 % m) (base % m) exp) bF 0 := ⟨hb,he,hm,hm',hrFlt,hbF,by omega⟩
  obtain ⟨_,_,_,e3,_,_⟩ := env_sv P hokF
  have hp : pstmt (.ret (.variable u64 3)) (mk P (sv base exp m (pw m 64 (1 % m) (base % m) exp) bF 0)) =
      some ⟨mk P (sv base exp m (pw m 64 (1 % m) (base % m) exp) bF 0),some ((pw m 64 (1 % m) (base % m) exp : Nat) : Int),
        (NExpr.variable u64 3).nodes+1,P.length+12+(NExpr.variable u64 3).nodes+2⟩ := by
    simp only [pstmt,Bind.bind,Option.bind,den_variable,e3,mk_size]
    rfl
  have p4 := seq_ret (fu := 70) (b := Sk) (a := .primitive (.ret (.variable u64 3))) (by rw [pexec_prim]; exact hp) rfl
  rw [← hlps] at p4
  have p3 := seq_some hl hlret p4
  have h3 := pexec_prim 70 (.declare u64 true initE) (mk P [base,exp,m,1 % m,base % m])
  rw [s3] at h3
  have p2 := seq_some h3 rfl p3
  have h2 := pexec_prim 70 (.declare u64 true initB) (mk P [base,exp,m,1 % m])
  rw [s2] at h2
  have p1 := seq_some h2 rfl p2
  have h1 := pexec_prim 70 (.declare u64 true initR) (mk P [base,exp,m])
  rw [s1] at h1
  have p0 := seq_some h1 rfl p1
  rw [← body_eq] at p0
  refine ⟨_,bF,p0,rfl,?_,?_,hlps⟩
  · simp [NExpr.nodes] at *
    omega
  · simp [NExpr.nodes,mk_size] at *
    omega


theorem pow_mod_spec (b e m : Nat) (hm : 0 < m) (he : e < 2^64) : pw m 64 (1 % m) (b % m) e = b^e % m := by
  rw [pw_spec m hm 64 _ _ _ he (Nat.mod_lt _ hm)]
  rcases Nat.lt_or_ge 1 m with h | h
  · rw [Nat.mod_eq_of_lt h, Nat.one_mul, ← Nat.pow_mod]
  · have : m = 1 := by omega
    subst this
    simp [Nat.mod_one]

theorem prepare_pow_mod_int (caller : NState) (e1 e2 e3 : NExpr) (v1 v2 v3 : Int) (h1 : e1.scalarOnly = true)
    (h2 : e2.scalarOnly = true) (h3 : e3.scalarOnly = true) (t1ty : e1.resultType = u64) (t2ty : e2.resultType = u64)
    (t3ty : e3.resultType = u64) (d1 : e1.denote (envOf caller) = some v1) (d2 : e2.denote (envOf caller) = some v2)
    (d3 : e3.denote (envOf caller) = some v3)
    (valid : caller.frame.state.wellFormed = true) (n1 : u64.valid v1 = true) (n2 : u64.valid v2 = true)
    (n3 : u64.valid v3 = true) :
    ∃ t1 t2 t3, Good caller t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧ Good t2 t3 e3.nodes e3.nodes ∧
      ∃ Sinit, prepare caller Proofs.PowModInstance.pow_mod.parameters [.value e1,.value e2,.value e3] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1,.scalar 2] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨u64,v1⟩,⟨u64,v2⟩,⟨u64,v3⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,
          ⟨(callerP caller).length+2,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = t3.scalars.work+4 ∧ t3.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 caller v1 h1 d1
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 h2 (by rw [envOf_core g1.1]; exact d2)
  obtain ⟨t3,ran3,g3⟩ := scalar_eval e3 t2 v3 h3 (by rw [envOf_core g2.1, envOf_core g1.1]; exact d3)
  refine ⟨t1,t2,t3,g1,g2,g3,?_⟩
  have frameT : t3.frame = caller.frame := by rw [g3.1.1,g2.1.1,g1.1.1]
  have fs : t3.frame.state = caller.frame.state := by rw [frameT]
  have fr : t3.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t3.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t3.scalars.memory = caller.scalars.memory := by
    have a := g3.1.2.2.2.1; have b := g2.1.2.2.2.1; have c := g1.1.2.2.2.1; rw [a,b,c]
  have hbind : t3.scalars.bindings = caller.scalars.bindings := by
    have a := g3.1.2.2.2.2.1; have b := g2.1.2.2.2.2.1; have c := g1.1.2.2.2.2.1; rw [a,b,c]
  have hbase : t3.scalars.baseMemory = caller.scalars.baseMemory := by
    have a := g3.1.2.2.2.2.2; have b := g2.1.2.2.2.2.2; have c := g1.1.2.2.2.2.2; rw [a,b,c]
  have res1 : resolve caller (.scalar u64 false true) (.value e1) = some (t1,.scalar u64 true v1) := by
    simp [resolve,t1ty,ran1]
  have res2 : resolve t1 (.scalar u64 false true) (.value e2) = some (t2,.scalar u64 true v2) := by
    simp [resolve,t2ty,ran2]
  have res3 : resolve t2 (.scalar u64 false true) (.value e3) = some (t3,.scalar u64 true v3) := by
    simp [resolve,t3ty,ran3]
  have hparams : Proofs.PowModInstance.pow_mod.parameters =
      [.scalar u64 false true,.scalar u64 false true,.scalar u64 false true] := rfl
  rw [hparams]
  simp [prepare,valid,resolveAll,res1,res2,res3]
  simp [fs,fr,fb,hmem,hbind,hbase,bindAll,bindOne,CppState.bindArgument,n1,n2,n3,callerP,
    NState.observe,CppState.State.observe]
  exact ⟨by omega,Nat.le_max_left _ _⟩


set_option maxHeartbeats 4000000 in
theorem pow_mod_correct (caller : NState) (bE eE mE : NExpr) (b e m : Nat) (hs1 : bE.scalarOnly = true)
    (hs2 : eE.scalarOnly = true) (hs3 : mE.scalarOnly = true) (ty1 : bE.resultType = u64) (ty2 : eE.resultType = u64)
    (ty3 : mE.resultType = u64) (d1 : bE.denote (envOf caller) = some (b : Int))
    (d2 : eE.denote (envOf caller) = some (e : Int)) (d3 : mE.denote (envOf caller) = some (m : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) (hb : b < 18446744073709551616)
    (he : e < 18446744073709551616) (hm : 0 < m) (hm' : m ≤ 4294967296) :
    ∃ Sinit fuel res, prepare caller Proofs.PowModInstance.pow_mod.parameters [.value bE,.value eE,.value mE] = some Sinit ∧
      Proofs.PowModInstance.pow_mod.callFuel fuel caller [.value bE,.value eE,.value mE] =
        .finished (res,.scalar ((b^e % m : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res (bE.nodes+eE.nodes+mE.nodes) 3010 caller.scalars.memory := by
  obtain ⟨t1,t2,t3,g1,g2,g3,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_pow_mod_int caller bE eE mE (b : Int) (e : Int) (m : Int) hs1 hs2 hs3 ty1 ty2 ty3 d1 d2 d3 valid
      (u64_lt b hb) (u64_lt e he) (u64_lt m (by omega))
  have hexp : e < 2^64 := by simpa using he
  obtain ⟨r,bF,hexec,hret,hcost,hneed,hrps⟩ := body_exec (callerP caller) b e m hb he hm hm'
  have spC : caller.scalars.peak ≤ Sinit.scalars.peak := by
    have a1 := g1.2.2.2.2.1; have a2 := g2.2.2.2.2.1; have a3 := g3.2.2.2.2.1
    omega
  have hpw := pow_mod_spec b e m hm hexp
  have hlt : b^e % m < m := Nat.mod_lt _ hm
  have hmk : (⟨callerP caller ++ [(⟨u64,(b : Int)⟩ : Cell),(⟨u64,(e : Int)⟩ : Cell),(⟨u64,(m : Int)⟩ : Cell)],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]⟩ : PS) =
      mk (callerP caller) [b,e,m] := by
    simp [mk,cm,bmd,List.range_succ]
  have hbody : Scalar Proofs.PowModInstance.pow_mod.body = true := by decide
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨u64,(b : Int)⟩ : Cell),(⟨u64,(e : Int)⟩ : Cell),(⟨u64,(m : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hpost := call_scalar caller Proofs.PowModInstance.pow_mod (.value bE :: .value eE :: [.value mE]) Sinit
    (callerP caller ++ [(⟨u64,(b : Int)⟩ : Cell),(⟨u64,(e : Int)⟩ : Cell),(⟨u64,(m : Int)⟩ : Cell)])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩,⟨(callerP caller).length+2,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame spC
    (by simp [hlen]; omega) (by rw [takeM]) valid lengths strict base hbody 70 r
    (by rw [hmk]; exact hexec) ((pw m 64 (1 % m) (b % m) e : Nat) : Int) hret u64 rfl
    (by rw [hpw]; exact u64_lt _ (by omega)) (by omega) (by simp [hlen])
    (bE.nodes+eE.nodes+mE.nodes) 3010 (by
      have a1 := g1.2.2.1; have a2 := g2.2.2.1; have a3 := g3.2.2.1
      omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,?_,?_⟩
  · rw [hpw] at hrun; exact hrun
  · have hs : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
      rw [hrps]
      simp only [mk_mem, callerP, List.append_assoc]
      exact List.take_left
    rw [hs] at post; exact post

end Proofs.PowModCall
