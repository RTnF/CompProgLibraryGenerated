namespace AddMemberGeneral
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


open OriginalMemberResult
open Proofs.CppScalarValuePrepare
open Proofs.Mod61Body

abbrev s64 : Ty := ⟨64,true,false⟩
abbrev i32 : Ty := ⟨32,true,false⟩
abbrev cn (n : Int) : Cell := ⟨i32,n⟩
abbrev cx (x : Int) : Cell := ⟨s64,x⟩
def refs (a : Nat) : List CppState.Binding := [⟨a,true⟩]
def resultCells (v x n : Int) : List Cell :=
  [cx x,cn n,cx (x+n*v),cn n,cx (x+n*v),cn n]
def product : NExpr := .binary s64 .mul (.cast s64 (.variable i32 2)) (.variable s64 0)
def total : NExpr := .binary s64 .add (.variable s64 1) product
def rawBody : Command :=
  .sequence (.primitive (.declare s64 true total))
    (.sequence (.primitive (.declare i32 true (.variable i32 2)))
      (.sequence (.primitive (.declare s64 true (.variable s64 3)))
        (.sequence (.primitive (.declare i32 true (.variable i32 4)))
          (.sequence (.scope Sk) Sk))))
theorem body_shape : RangeSum_factory_receiver1_apply.body = rawBody := rfl

theorem widen_size (n : Int) (hn : i32.valid n = true) : s64.valid n = true := by
  simp [Ty.valid] at hn ⊢
  omega

theorem raw_exec (P : List Cell) (a : Nat) (v x n : Int)
    (receiver : P[a]? = some (cx v))
    (hv : s64.valid v = true) (hx : s64.valid x = true)
    (hn : i32.valid n = true)
    (hp : s64.valid (n*v) = true) (hs : s64.valid (x+n*v) = true) :
    ∃ r, pexec 1 RangeSum_factory_receiver1_apply.body (ws P (refs a) [cx x,cn n]) = some r ∧
      r.ret = none ∧ r.cost = 14 ∧ r.need = P.length+16 ∧
      r.ps = ws P (refs a) (resultCells v x n) := by
  let R := refs a
  let L2 : List Cell := [cx x,cn n]
  let L3 : List Cell := L2 ++ [cx (x+n*v)]
  let L4 : List Cell := L3 ++ [cn n]
  let L5 : List Cell := L4 ++ [cx (x+n*v)]
  let L6 := resultCells v x n
  have rv : (NExpr.variable s64 0).denote (penv (ws P R L2)) = some v := by
    rw [den_variable]
    exact ws_env_ref P R L2 0 a true s64 v (by rfl) receiver hv
  have xx : (NExpr.variable s64 1).denote (penv (ws P R L2)) = some x := by
    rw [den_variable]
    exact ws_env_loc P R L2 0 (cx x) s64 rfl rfl hx
  have nn (L : List Cell) (found : L[1]? = some (cn n)) :
      (NExpr.variable i32 2).denote (penv (ws P R L)) = some n := by
    rw [den_variable]
    exact ws_env_loc P R L 1 (cn n) i32 found rfl hn
  have castn : (NExpr.cast s64 (.variable i32 2)).denote (penv (ws P R L2)) = some n := by
    rw [den_cast,nn L2 rfl]
    simpa using Ty.convert_of_valid s64 n (widen_size n hn)
  have mul : product.denote (penv (ws P R L2)) = some (n*v) := by
    rw [product,den_binary,castn,rv]
    simpa [binaryValue] using Ty.convert_of_valid s64 (n*v) hp
  have sum : total.denote (penv (ws P R L2)) = some (x+n*v) := by
    rw [total,den_binary,xx,mul]
    simpa [binaryValue] using Ty.convert_of_valid s64 (x+n*v) hs
  have read3 : (NExpr.variable s64 3).denote (penv (ws P R L4)) = some (x+n*v) := by
    rw [den_variable]
    exact ws_env_loc P R L4 2 (cx (x+n*v)) s64 rfl rfl hs
  have read4 : (NExpr.variable i32 4).denote (penv (ws P R L5)) = some n := by
    rw [den_variable]
    exact ws_env_loc P R L5 3 (cn n) i32 rfl rfl hn
  have q0 := (pexec_prim 1 _ _).trans (ws_declare P R L2 s64 total (x+n*v) sum (Ty.convert_of_valid _ _ hs))
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P R L3 i32 (.variable i32 2) n (nn L3 rfl) (Ty.convert_of_valid _ _ hn))
  have q2 := (pexec_prim 1 _ _).trans (ws_declare P R L4 s64 (.variable s64 3) (x+n*v) read3 (Ty.convert_of_valid _ _ hs))
  have q3 := (pexec_prim 1 _ _).trans (ws_declare P R L5 i32 (.variable i32 4) n read4 (Ty.convert_of_valid _ _ hn))
  have sc0 := pexec_scope 1 Sk (ws P R L6) _ (pexec_skip 1 _)
  have sc : pexec 1 (.scope Sk) (ws P R L6) = some ⟨ws P R L6,none,1,P.length+13⟩ := by
    simp only [List.take_length] at sc0
    simpa [ws,L6,resultCells,R,refs,Nat.add_assoc] using sc0
  have all := seq_some q0 rfl (seq_some q1 rfl (seq_some q2 rfl (seq_some q3 rfl (seq_some sc rfl (pexec_skip 1 _)))))
  refine ⟨⟨ws P R L6,none,14,P.length+16⟩,?_,rfl,rfl,rfl,rfl⟩
  rw [body_shape]
  simpa [rawBody,ws,L2,L3,L4,L5,L6,resultCells,R,refs,total,product,NExpr.nodes,Nat.add_assoc] using all
end AddMemberGeneral
