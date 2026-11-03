import Proofs.PowModCall
import Proofs.PexecKit
import Proofs.Generated.GcdU64

namespace Proofs.GcdU64Call
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.PowModStep Proofs.StraightLine
open Proofs.QuotientSearch Proofs.Mod61Body Proofs.DoublingNested
open Proofs.CppState (Cell)
open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.ScalarStraight

abbrev gC : NExpr := .binary bl .ne (.variable u64 1) c0E
abbrev gRem : NExpr := .divrem u64 true (.variable u64 0) (.variable u64 1)
abbrev gA0 : NStmt := .assign 0 u64 (.variable u64 1)
abbrev gA1 : NStmt := .assign 1 u64 (.variable u64 2)
abbrev gBody : Command := .sequence (.scope (.sequence (.primitive (.declare u64 true gRem))
  (.sequence (.primitive gA0) (.sequence (.primitive gA1) Sk)))) Sk
abbrev gLoop : Command := .whileLoop gC gBody

theorem body_eq : Proofs.GcdU64Instance.gcd_u64.body =
    .sequence gLoop (.sequence (.primitive (.ret (.variable u64 0))) Sk) := rfl

theorem take_mk_mem (P : List Cell) (vs ws : List Nat) :
    (mk P (vs ++ ws)).mem.take (mk P vs).mem.length = (mk P vs).mem := by
  simp [mk, cm, List.map_append, List.take_append]
  exact List.take_of_length_le (by omega)

theorem take_mk_bs (P : List Cell) (vs ws : List Nat) :
    (mk P (vs ++ ws)).bs.take (mk P vs).bs.length = (mk P vs).bs := by
  simp [mk, bmd, ← List.map_take, List.take_range]

theorem gC_value (env : Nat → Ty → Option Int) (b : Nat) (h1 : env 1 u64 = some (b : Int)) :
    gC.denote env = some (if b = 0 then 0 else 1) := by
  rw [den_binary,den_variable,h1,c0_value]
  simp only [Option.bind_some,binaryValue]
  by_cases z : b = 0
  · subst z; simpa using Ty.convert_of_valid bl 0 (by simp [Ty.valid])
  · have : ((b : Int) != 0) = true := by simp [z]
    simp only [this,if_true,z,if_false]
    exact Ty.convert_of_valid bl 1 (by simp [Ty.valid])

theorem gRem_value (P : List Cell) (a b : Nat) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616)
    (hb0 : b ≠ 0) : gRem.denote (penv (mk P [a,b])) = some ((a % b : Nat) : Int) := by
  have hv : ∀ x ∈ [a,b], x < 18446744073709551616 := by intro x hx; simp at hx; omega
  have k := penv_mk P [a,b] hv
  rw [den_divrem, den_variable, den_variable, k 0 (by simp), k 1 (by simp)]
  exact rem_value a b (by omega) ha

theorem g_iter (P : List Cell) (a b : Nat) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616)
    (hb0 : b ≠ 0) (fu : Nat) :
    ∃ r1, pexec fu gBody (mk P [a,b]) = some r1 ∧ r1.ps = mk P [b, a % b] ∧ r1.ret = none ∧
      r1.cost ≤ 30 ∧ r1.need ≤ P.length + 12 := by
  have hmod : a % b < 18446744073709551616 := by have := Nat.mod_le a b; omega
  have hv2 : ∀ x ∈ [a,b], x < 18446744073709551616 := by intro x hx; simp at hx; omega
  have d1 := mk_decl P [a,b] gRem (a % b) hmod (gRem_value P a b ha hb hb0)
  have hv3 : ∀ x ∈ [a,b,a % b], x < 18446744073709551616 := by intro x hx; simp at hx; omega
  have k3 := penv_mk P [a,b,a % b] hv3
  have a0 := mk_assign P [a,b,a % b] 0 (by simp) (.variable u64 1) b hb hv3 (by rw [den_variable]; exact k3 1 (by simp))
  have hv4 : ∀ x ∈ [b,b,a % b], x < 18446744073709551616 := by intro x hx; simp at hx; omega
  have k4 := penv_mk P [b,b,a % b] hv4
  have a1 := mk_assign P [b,b,a % b] 1 (by simp) (.variable u64 2) (a % b) hmod hv4 (by rw [den_variable]; exact k4 2 (by simp))
  have q1 : pexec fu (.primitive (.declare u64 true gRem)) (mk P [a,b]) =
      some ⟨mk P [a,b,a % b],none,gRem.nodes+1,P.length+2*[a,b].length+gRem.nodes+4⟩ := (pexec_prim _ _ _).trans d1
  have q2 : pexec fu (.primitive gA0) (mk P [a,b,a % b]) =
      some ⟨mk P [b,b,a % b],none,(NExpr.variable u64 1).nodes+1,P.length+2*[a,b,a % b].length+(NExpr.variable u64 1).nodes+2⟩ :=
    (pexec_prim _ _ _).trans a0
  have q3 : pexec fu (.primitive gA1) (mk P [b,b,a % b]) =
      some ⟨mk P [b,a % b,a % b],none,(NExpr.variable u64 2).nodes+1,P.length+2*[b,b,a % b].length+(NExpr.variable u64 2).nodes+2⟩ :=
    (pexec_prim _ _ _).trans a1
  have s3 := seq_some q3 rfl (Proofs.PexecKit.pexec_skip fu (mk P [b,a % b,a % b]))
  have s2 := seq_some q2 rfl s3
  have s1 := seq_some q1 rfl s2
  have sc := Proofs.PexecKit.pexec_scope fu _ _ _ s1
  have tk : (⟨(mk P [b,a % b,a % b]).mem.take (mk P [a,b]).mem.length,
      (mk P [b,a % b,a % b]).bs.take (mk P [a,b]).bs.length⟩ : PS) = mk P [b,a % b] := by
    have h1 : (mk P [a,b]).mem.length = (mk P [b,a % b]).mem.length := by simp [mk,cm]
    have h2 : (mk P [a,b]).bs.length = (mk P [b,a % b]).bs.length := by simp [mk,bmd]
    rw [h1,h2]
    have := take_mk_mem P [b,a % b] [a % b]
    have := take_mk_bs P [b,a % b] [a % b]
    simp only [List.cons_append, List.nil_append] at *
    simp_all [mk_eta]
  simp only [tk] at sc
  have fin := seq_some sc rfl (Proofs.PexecKit.pexec_skip fu (mk P [b,a % b]))
  refine ⟨_, fin, rfl, rfl, ?_, ?_⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes, mk_size]

/-- The number of loop iterations of Euclid's algorithm. -/
def gsteps (a b : Nat) : Nat :=
  if h : b = 0 then 0 else 1 + gsteps b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (by omega)

theorem gsteps_zero (a : Nat) : gsteps a 0 = 0 := by rw [gsteps]; simp

theorem gsteps_pos (a b : Nat) (h : b ≠ 0) : gsteps a b = 1 + gsteps b (a % b) := by
  rw [gsteps]; simp [h]

theorem mod_half (b r : Nat) (hr : 0 < r) (hrb : r < b) : 2 * (b % r) < b := by
  by_cases h : 2 * r ≤ b
  · have := Nat.mod_lt b hr
    omega
  · have hmod : b % r = b - r := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

theorem log_succ_le (c b : Nat) (hc : 0 < c) (h : 2 * c < b) : Nat.log2 c + 1 ≤ Nat.log2 b := by
  rw [Nat.le_log2 (by omega), Nat.pow_succ]
  have := Nat.log2_self_le (show c ≠ 0 by omega)
  omega

theorem gsteps_le : ∀ b a, 0 < b → gsteps a b ≤ 2 * Nat.log2 b + 1 := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ih =>
    intro a hb
    rw [gsteps_pos a b (by omega)]
    by_cases hr : a % b = 0
    · rw [hr, gsteps_zero]; omega
    · have hrb : a % b < b := Nat.mod_lt _ hb
      have hr0 : 0 < a % b := by omega
      rw [gsteps_pos b (a % b) hr]
      have hh := mod_half b (a % b) hr0 hrb
      by_cases hc : b % (a % b) = 0
      · rw [hc, gsteps_zero]
        have : 1 ≤ Nat.log2 b := by
          rw [Nat.le_log2 (by omega)]; omega
        omega
      · have hc0 : 0 < b % (a % b) := by omega
        have ih' := ih (b % (a % b)) (by omega) (a % b) hc0
        have hlog := log_succ_le (b % (a % b)) b hc0 hh
        omega

theorem gcd_step (a b : Nat) (h : b ≠ 0) : Nat.gcd a b = Nat.gcd b (a % b) := by
  rw [Nat.gcd_comm a b, Nat.gcd_rec b a]
  exact Nat.gcd_comm _ _

theorem g_loop (P : List Cell) : ∀ (b a : Nat), a < 18446744073709551616 → b < 18446744073709551616 →
    ∀ fu, gsteps a b + 1 ≤ fu →
    ∃ r1, pexec fu gLoop (mk P [a,b]) = some r1 ∧ r1.ps = mk P [Nat.gcd a b, 0] ∧ r1.ret = none ∧
      r1.cost ≤ 40 * gsteps a b + 5 ∧ r1.need ≤ P.length + 12 := by
  intro b
  induction b using Nat.strongRecOn with
  | _ b ih =>
    intro a ha hb fu hfu
    obtain ⟨fu', rfl⟩ : ∃ fu', fu = fu' + 1 := ⟨fu - 1, by omega⟩
    have hv : ∀ x ∈ [a,b], x < 18446744073709551616 := by intro x hx; simp at hx; omega
    have k := penv_mk P [a,b] hv
    have hc := gC_value (penv (mk P [a,b])) b (k 1 (by simp))
    by_cases z : b = 0
    · subst z
      rw [if_pos rfl] at hc
      rw [pexec_while]
      simp only [Bind.bind, Option.bind, hc, ite_true]
      refine ⟨_, rfl, ?_, rfl, ?_, ?_⟩
      · simp [Nat.gcd_zero_right]
      · simp [NExpr.nodes, gsteps_zero]
      · simp [NExpr.nodes, mk_size]
    · rw [if_neg z] at hc
      obtain ⟨r1, h1, p1, ret1, c1, n1⟩ := g_iter P a b ha hb z (fu' + 1)
      have hmod : a % b < 18446744073709551616 := by have := Nat.mod_le a b; omega
      obtain ⟨r2, h2, p2, ret2, c2, n2⟩ := ih (a % b) (Nat.mod_lt _ (by omega)) b hb hmod fu'
        (by rw [gsteps_pos a b z] at hfu; omega)
      rw [pexec_while]
      simp only [Bind.bind, Option.bind, hc, int_one_ne, ite_false, h1, ret1, p1, h2]
      refine ⟨_, rfl, ?_, ret2, ?_, ?_⟩
      · rw [p2, gcd_step a b z]
      · rw [gsteps_pos a b z]
        simp [NExpr.nodes] at *; omega
      · simp [NExpr.nodes, mk_size] at *
        omega
theorem prepare_gcd_int (caller : NState) (e1 e2 : NExpr) (v1 v2 : Int) (h1 : e1.scalarOnly = true)
    (h2 : e2.scalarOnly = true) (t1ty : e1.resultType = u64) (t2ty : e2.resultType = u64)
    (d1 : e1.denote (envOf caller) = some v1) (d2 : e2.denote (envOf caller) = some v2)
    (valid : caller.frame.state.wellFormed = true) (n1 : u64.valid v1 = true) (n2 : u64.valid v2 = true) :
    ∃ t1 t2, Good caller t1 e1.nodes e1.nodes ∧ Good t1 t2 e2.nodes e2.nodes ∧
      ∃ Sinit, prepare caller Proofs.GcdU64Instance.gcd_u64.parameters [.value e1,.value e2] = some Sinit ∧
        Sinit.slots = [.scalar 0,.scalar 1] ∧
        Sinit.scalars.memory = callerP caller ++ [⟨u64,v1⟩,⟨u64,v2⟩] ∧
        Sinit.scalars.bindings = [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩] ∧
        Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
        Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
        Sinit.scalars.work = t2.scalars.work+3 ∧ t2.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨t1,ran1,g1⟩ := scalar_eval e1 caller v1 h1 d1
  obtain ⟨t2,ran2,g2⟩ := scalar_eval e2 t1 v2 h2 (by rw [envOf_core g1.1]; exact d2)
  refine ⟨t1,t2,g1,g2,?_⟩
  have frameT : t2.frame = caller.frame := by rw [g2.1.1,g1.1.1]
  have fs : t2.frame.state = caller.frame.state := by rw [frameT]
  have fr : t2.frame.rootWritable = caller.frame.rootWritable := by rw [frameT]
  have fb : t2.frame.bindings = caller.frame.bindings := by rw [frameT]
  have hmem : t2.scalars.memory = caller.scalars.memory := by
    have b := g2.1.2.2.2.1; have c := g1.1.2.2.2.1; rw [b,c]
  have hbind : t2.scalars.bindings = caller.scalars.bindings := by
    have b := g2.1.2.2.2.2.1; have c := g1.1.2.2.2.2.1; rw [b,c]
  have hbase : t2.scalars.baseMemory = caller.scalars.baseMemory := by
    have b := g2.1.2.2.2.2.2; have c := g1.1.2.2.2.2.2; rw [b,c]
  have res1 : resolve caller (.scalar u64 false true) (.value e1) = some (t1,.scalar u64 true v1) := by
    simp [resolve,t1ty,ran1]
  have res2 : resolve t1 (.scalar u64 false true) (.value e2) = some (t2,.scalar u64 true v2) := by
    simp [resolve,t2ty,ran2]
  have hparams : Proofs.GcdU64Instance.gcd_u64.parameters =
      [.scalar u64 false true,.scalar u64 false true] := rfl
  rw [hparams]
  simp [prepare,valid,resolveAll,res1,res2]
  simp [fs,fr,fb,hmem,hbind,hbase,bindAll,bindOne,CppState.bindArgument,n1,n2,callerP,
    NState.observe,CppState.State.observe]
  exact ⟨by omega,Nat.le_max_left _ _⟩



theorem body_exec (P : List Cell) (a b : Nat) (ha : a < 18446744073709551616) (hb : b < 18446744073709551616) (fu : Nat)
    (hfu : gsteps a b + 1 ≤ fu) :
    ∃ r, pexec fu Proofs.GcdU64Instance.gcd_u64.body (mk P [a,b]) = some r ∧ r.ret = some ((Nat.gcd a b : Nat) : Int) ∧
      r.cost ≤ 40 * gsteps a b + 20 ∧ r.need ≤ P.length + 12 ∧ r.ps = mk P [Nat.gcd a b, 0] := by
  obtain ⟨rL, hL, pL, retL, cL, nL⟩ := g_loop P b a ha hb fu hfu
  have hg : Nat.gcd a b < 18446744073709551616 := by
    by_cases z : a = 0
    · subst z; rw [Nat.gcd_zero_left]; exact hb
    · have := Nat.gcd_le_left b (show 0 < a by omega); omega
  have hv : ∀ x ∈ [Nat.gcd a b, 0], x < 18446744073709551616 := by intro x hx; simp at hx; omega
  have k := penv_mk P [Nat.gcd a b, 0] hv
  have g1 := Proofs.PexecKit.pstmt_ret_ok (mk P [Nat.gcd a b, 0]) (.variable u64 0) ((Nat.gcd a b : Nat) : Int)
    (by rw [den_variable]; exact k 0 (by simp))
  have g2 : pexec fu (.sequence (.primitive (.ret (.variable u64 0))) Sk) (mk P [Nat.gcd a b, 0]) = _ :=
    seq_ret (b := Sk) ((pexec_prim _ _ _).trans g1) rfl
  have h3 := seq_some hL retL (by rw [pL]; exact g2)
  rw [body_eq]
  refine ⟨_, h3, rfl, ?_, ?_, ?_⟩
  · simp [NExpr.nodes]; omega
  · simp [NExpr.nodes, mk_size]; omega
  · rfl

set_option maxHeartbeats 4000000 in
theorem gcd_u64_correct (caller : NState) (aE bE : NExpr) (a b : Nat) (hs1 : aE.scalarOnly = true)
    (hs2 : bE.scalarOnly = true) (ty1 : aE.resultType = u64) (ty2 : bE.resultType = u64)
    (d1 : aE.denote (envOf caller) = some (a : Int)) (d2 : bE.denote (envOf caller) = some (b : Int))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) (ha : a < 18446744073709551616)
    (hb : b < 18446744073709551616) :
    ∃ Sinit fuel res, prepare caller Proofs.GcdU64Instance.gcd_u64.parameters [.value aE,.value bE] = some Sinit ∧
      Proofs.GcdU64Instance.gcd_u64.callFuel fuel caller [.value aE,.value bE] =
        .finished (res,.scalar ((Nat.gcd a b : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res (aE.nodes+bE.nodes) (80 * Nat.log2 b + 100) caller.scalars.memory := by
  obtain ⟨t1,t2,g1,g2,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prepare_gcd_int caller aE bE (a : Int) (b : Int) hs1 hs2 ty1 ty2 d1 d2 valid (u64_lt a ha) (u64_lt b hb)
  have hsteps : gsteps a b ≤ 2 * Nat.log2 b + 1 := by
    by_cases z : b = 0
    · subst z; rw [gsteps_zero]; omega
    · exact gsteps_le b a (by omega)
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := body_exec (callerP caller) a b ha hb (gsteps a b + 1) (Nat.le_refl _)
  have spC : caller.scalars.peak ≤ Sinit.scalars.peak := by
    have a1 := g1.2.2.2.2.1; have a2 := g2.2.2.2.2.1
    omega
  have hmk : (⟨callerP caller ++ [(⟨u64,(a : Int)⟩ : Cell),(⟨u64,(b : Int)⟩ : Cell)],
      [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]⟩ : PS) = mk (callerP caller) [a,b] := by
    simp [mk,cm,bmd,List.range_succ]
  have hbody : Scalar Proofs.GcdU64Instance.gcd_u64.body = true := by decide
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller ++ [(⟨u64,(a : Int)⟩ : Cell),(⟨u64,(b : Int)⟩ : Cell)]).take caller.scalars.memory.length =
      caller.scalars.memory := by
    simp only [callerP, List.append_assoc]; exact List.take_left
  have hg : Nat.gcd a b < 18446744073709551616 := by
    by_cases z : a = 0
    · subst z; rw [Nat.gcd_zero_left]; exact hb
    · have := Nat.gcd_le_left b (show 0 < a by omega); omega
  have hpost := call_scalar caller Proofs.GcdU64Instance.gcd_u64 (.value aE :: [.value bE]) Sinit
    (callerP caller ++ [(⟨u64,(a : Int)⟩ : Cell),(⟨u64,(b : Int)⟩ : Cell)])
    [⟨(callerP caller).length,true⟩,⟨(callerP caller).length+1,true⟩]
    hprep (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame spC
    (by simp [hlen]; omega) (by rw [takeM]) valid lengths strict base hbody (gsteps a b + 1) r
    (by rw [hmk]; exact hexec) ((Nat.gcd a b : Nat) : Int) hret u64 rfl (u64_lt _ hg) (by omega) (by simp [hlen])
    (aE.nodes+bE.nodes) (80 * Nat.log2 b + 100) (by
      have a1 := g1.2.2.1; have a2 := g2.2.2.1
      omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  have hs : r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory := by
    rw [hrps]
    simp only [mk_mem, callerP, List.append_assoc]
    exact List.take_left
  rw [hs] at post; exact post

end Proofs.GcdU64Call
