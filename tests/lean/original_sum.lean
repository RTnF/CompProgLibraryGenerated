namespace OriginalSumAudit
open Proofs
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch Proofs.ExtremaCall Proofs.MonoidCall
open Proofs.GroupCall
open Proofs.CppState (Cell)

abbrev zeroExpr : NExpr := .cast s64 (.literal i32 0)
abbrev difference : NExpr := .binary s64 .sub (.variable s64 3) (.variable s64 0)

theorem inv_exec (P : List Cell) (ba : CppState.Binding) (x : Int)
    (hx : s64.valid x = true) (hnx : s64.valid (-x) = true)
    (hc : P[ba.address]? = some ⟨s64,x⟩) :
    ∃ r, pexec 1 Original_sum.GroupSum_long_long_inv.body (ws P [⟨ba.address,false⟩] []) = some r ∧
      r.ret = some (-x) ∧ r.cost ≤ 20 ∧ r.need ≤ P.length+100 ∧
      r.ps.mem = P ++ [⟨s64,0⟩,⟨s64,0⟩,⟨s64,0⟩,⟨s64,-x⟩,⟨s64,-x⟩] := by
  let R : List CppState.Binding := [⟨ba.address,false⟩]
  let L1 : List Cell := [⟨s64,0⟩]
  let L2 : List Cell := L1 ++ [⟨s64,0⟩]
  let L3 : List Cell := L2 ++ [⟨s64,0⟩]
  let L4 : List Cell := L3 ++ [⟨s64,-x⟩]
  let L5 : List Cell := L4 ++ [⟨s64,-x⟩]
  have hz : s64.valid 0 = true := rfl
  have d0 : zeroExpr.denote (penv (ws P R [])) = some 0 := by rfl
  have s1 := ws_declare P R [] s64 zeroExpr 0 d0 (convS _ hz)
  have q1 := (pexec_prim 1 _ _).trans s1
  have e1 : penv (ws P R L1) 1 s64 = some 0 :=
    ws_env_loc P R L1 0 ⟨s64,0⟩ s64 rfl rfl hz
  have s2 := ws_declare P R L1 s64 (.variable s64 1) 0 (by rw [den_variable]; exact e1) (convS _ hz)
  have q2 := (pexec_prim 1 _ _).trans s2
  have e2 : penv (ws P R L2) 2 s64 = some 0 :=
    ws_env_loc P R L2 1 ⟨s64,0⟩ s64 rfl rfl hz
  have s3 := ws_declare P R L2 s64 (.variable s64 2) 0 (by rw [den_variable]; exact e2) (convS _ hz)
  have q3 := (pexec_prim 1 _ _).trans s3
  have e3 : penv (ws P R L3) 3 s64 = some 0 :=
    ws_env_loc P R L3 2 ⟨s64,0⟩ s64 rfl rfl hz
  have ex : penv (ws P R L3) 0 s64 = some x := ws_env_ref P R L3 0 ba.address false s64 x rfl hc hx
  have dd : difference.denote (penv (ws P R L3)) = some (-x) := by
    simp only [NExpr.denote, e3, ex, Option.bind_some, binaryValue, Int.zero_sub]
    exact convS _ hnx
  have s4 := ws_declare P R L3 s64 difference (-x) dd (convS _ hnx)
  have q4 := (pexec_prim 1 _ _).trans s4
  have e4 : penv (ws P R L4) 4 s64 = some (-x) :=
    ws_env_loc P R L4 3 ⟨s64,-x⟩ s64 rfl rfl hnx
  have s5 := ws_declare P R L4 s64 (.variable s64 4) (-x) (by rw [den_variable]; exact e4) (convS _ hnx)
  have q5 := (pexec_prim 1 _ _).trans s5
  have e5 : penv (ws P R L5) 5 s64 = some (-x) :=
    ws_env_loc P R L5 4 ⟨s64,-x⟩ s64 rfl rfl hnx
  have qr := exec_ret 1 (ws P R L5) (.variable s64 5) (-x) (by rw [den_variable]; exact e5)
  have q5r := seq_some q5 rfl qr
  have q45r := seq_some q4 rfl q5r
  have q345r := seq_some q3 rfl q45r
  have q2345r := seq_some q2 rfl q345r
  have qall := seq_some q1 rfl q2345r
  refine ⟨_,qall,rfl,?_,?_,?_⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes, ws, R, L1, L2, L3, L4, L5]
  · simp [ws, L1, L2, L3, L4, L5]

theorem inv_correct (caller : NState) (sa : Nat) (ba : CppState.Binding) (x : Int)
    (hxv : s64.valid x = true) (hnx : s64.valid (-x) = true)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,x⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Original_sum.GroupSum_long_long_inv.parameters [.scalarReference sa] = some Sinit ∧
      Original_sum.GroupSum_long_long_inv.callFuel fuel caller [.scalarReference sa] = .finished (res,.scalar (-x)) ∧
      ScalarPost2 caller Sinit res 0 80 caller.scalars.memory := by
  refine refs1_correct _ rfl rfl (by decide) caller sa ba x ca valid lengths strict base 1 (-x) hnx 20 ?_
  intro P hP
  subst hP
  obtain ⟨r,hex,hr,hcost,hneed,hmem⟩ := inv_exec (callerP caller) ba x hxv hnx (P_cell caller sa ba x ca)
  rw [ws_nil] at hex
  refine ⟨r,hex,hr,hcost,hneed,?_⟩
  rw [hmem]
  exact take_P caller _
end OriginalSumAudit
