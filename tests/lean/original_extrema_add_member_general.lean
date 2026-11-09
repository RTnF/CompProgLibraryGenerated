namespace ExtremaAddMemberGeneral
open Proofs
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.StraightLine Proofs.ScalarStraight Proofs.IntSim Proofs.ModIntCall
open Proofs.ModIntExec Proofs.PowModStep Proofs.PexecKit Proofs.QuotientSearch
open Proofs.ExtremaCall
open Proofs.CppState (Cell)

open Proofs.GroupCall


open Proofs.MonoidLazyCall Proofs.MonoidCall


open Proofs.CppScalarValuePrepare
open Proofs.Mod61Body

abbrev s64 : Ty := ⟨64,true,false⟩
abbrev i32 : Ty := ⟨32,true,false⟩
abbrev cx (x : Int) : Cell := ⟨s64,x⟩
def refs (a : Nat) : List CppState.Binding := [⟨a,true⟩]
def total : NExpr := .binary s64 .add (.variable s64 1) (.variable s64 0)
def rawBody : Command :=
  .sequence (.primitive (.declare s64 true total))
    (.sequence (.primitive (.declare s64 true (.variable s64 2))) (.sequence (.scope Sk) Sk))
theorem body_shape : SelectedExtrema.applyProgram.body = rawBody := rfl

theorem raw_exec (P : List Cell) (a : Nat) (v x : Int)
    (receiver : P[a]? = some (cx v)) (hv : s64.valid v = true)
    (hx : s64.valid x = true) (hs : s64.valid (x+v) = true) :
    ∃ r, pexec 1 SelectedExtrema.applyProgram.body (ws P (refs a) [cx x]) = some r ∧
      r.ret = none ∧ r.cost = 7 ∧ r.need = P.length+10 ∧
      r.ps = ws P (refs a) [cx x,cx (x+v),cx (x+v)] := by
  let R := refs a
  let L1 : List Cell := [cx x]
  let L2 : List Cell := [cx x,cx (x+v)]
  let L3 : List Cell := [cx x,cx (x+v),cx (x+v)]
  have rv : (NExpr.variable s64 0).denote (penv (ws P R L1)) = some v := by
    rw [den_variable]
    exact ws_env_ref P R L1 0 a true s64 v rfl receiver hv
  have xx : (NExpr.variable s64 1).denote (penv (ws P R L1)) = some x := by
    rw [den_variable]
    exact ws_env_loc P R L1 0 (cx x) s64 rfl rfl hx
  have sum : total.denote (penv (ws P R L1)) = some (x+v) := by
    rw [total,den_binary,xx,rv]
    simpa [binaryValue] using Ty.convert_of_valid s64 (x+v) hs
  have copied : (NExpr.variable s64 2).denote (penv (ws P R L2)) = some (x+v) := by
    rw [den_variable]
    exact ws_env_loc P R L2 1 (cx (x+v)) s64 rfl rfl hs
  have q0 := (pexec_prim 1 _ _).trans (ws_declare P R L1 s64 total (x+v) sum (Ty.convert_of_valid _ _ hs))
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P R L2 s64 (.variable s64 2) (x+v) copied (Ty.convert_of_valid _ _ hs))
  have sc0 := pexec_scope 1 Sk (ws P R L3) _ (pexec_skip 1 _)
  have sc : pexec 1 (.scope Sk) (ws P R L3) = some ⟨ws P R L3,none,1,P.length+7⟩ := by
    simp only [List.take_length] at sc0
    simpa [ws,R,refs,L3,Nat.add_assoc] using sc0
  have all := seq_some q0 rfl (seq_some q1 rfl (seq_some sc rfl (pexec_skip 1 _)))
  refine ⟨⟨ws P R L3,none,7,P.length+10⟩,?_,rfl,rfl,rfl,rfl⟩
  rw [body_shape]
  simpa [rawBody,ws,R,refs,L1,L2,L3,total,NExpr.nodes,Nat.add_assoc] using all
end ExtremaAddMemberGeneral
