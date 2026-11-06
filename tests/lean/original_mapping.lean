namespace OriginalMappingAudit
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

theorem apply_value_body : Original_mapping.Affine_long_long_apply__template_long_long.body =
    .sequence (.primitive (.ret applyE)) Sk := rfl

theorem apply_value_correct (caller : NState) (sa sb : Nat) (ba bb : CppState.Binding) (a b x : Int)
    (ca : caller.scalarCell sa s64 = some (ba,⟨s64,a⟩)) (cb : caller.scalarCell sb s64 = some (bb,⟨s64,b⟩))
    (hav : s64.valid a = true) (hbv : s64.valid b = true) (hxv : s64.valid x = true)
    (hm : s64.valid (a*x) = true) (hsum : s64.valid (a*x+b) = true)
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Original_mapping.Affine_long_long_apply__template_long_long.parameters
        [.scalarReference sa,.scalarReference sb,.value (.literal s64 x)] = some Sinit ∧
      Original_mapping.Affine_long_long_apply__template_long_long.callFuel fuel caller
        [.scalarReference sa,.scalarReference sb,.value (.literal s64 x)] = .finished (res,.scalar (a*x+b)) ∧
      ScalarPost2 caller Sinit res 0 80 caller.scalars.memory := by
  obtain ⟨t,good,Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_rrv caller _ rfl sa sb ba bb a b ca cb (.literal s64 x) x rfl rfl
      (by simp [NExpr.denote,hxv]) valid hxv
  let P := callerP caller ++ [⟨s64,x⟩]
  let refs : List CppState.Binding := [⟨ba.address,false⟩,⟨bb.address,false⟩,⟨(callerP caller).length,true⟩]
  have hlen : P.length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length)+1 := by simp [P,callerP]; omega
  have plen : P.length = (callerP caller).length + 1 := by simp [P]
  have gw := good.2.2.1
  simp only [charge_work,NExpr.nodes] at gw
  have takeM : P.take caller.scalars.memory.length = caller.scalars.memory := take_P caller _
  have hPa := P_cell caller sa ba a ca
  have hPb := P_cell caller sb bb b cb
  have hPa' : P[ba.address]? = some ⟨s64,a⟩ := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hPa).1];exact hPa
  have hPb' : P[bb.address]? = some ⟨s64,b⟩ := by
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp hPb).1];exact hPb
  have hPx : P[(callerP caller).length]? = some ⟨s64,x⟩ := by simp [P]
  have e0 : penv ⟨P,refs⟩ 0 s64 = some a := penv_ok _ 0 s64 ⟨ba.address,false⟩ ⟨s64,a⟩ rfl hPa' rfl hav
  have e1 : penv ⟨P,refs⟩ 1 s64 = some b := penv_ok _ 1 s64 ⟨bb.address,false⟩ ⟨s64,b⟩ rfl hPb' rfl hbv
  have e2 : penv ⟨P,refs⟩ 2 s64 = some x := penv_ok _ 2 s64 ⟨(callerP caller).length,true⟩ ⟨s64,x⟩ rfl hPx rfl hxv
  have q := exec_ret 1 ⟨P,refs⟩ applyE (a*x+b) (applyE_den _ a b x e0 e1 e2 hm hsum)
  have hexec : pexec 1 Original_mapping.Affine_long_long_apply__template_long_long.body ⟨P,refs⟩ =
      some ⟨⟨P,refs⟩,some (a*x+b),applyE.nodes+1,P.length+3+applyE.nodes+2⟩ := by
    rw [apply_value_body];simpa [refs] using q
  have hpost := call_scalar caller Original_mapping.Affine_long_long_apply__template_long_long
    [.scalarReference sa,.scalarReference sb,.value (.literal s64 x)] Sinit P refs
    hprep (by rw [sSlots];rfl) sMem sBind sBase sScope sFrame sPeak (by omega) (by rw [takeM]) valid lengths
    strict base (by rw [apply_value_body];simp [Scalar,NExpr.scalarOnly]) 1 _ hexec _ rfl s64 rfl hsum
    (by simp [NExpr.nodes];omega) (by simp [refs];omega) 0 80 (by simp only [NExpr.nodes] at *;omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  simp only [takeM] at post
  exact post
end OriginalMappingAudit
