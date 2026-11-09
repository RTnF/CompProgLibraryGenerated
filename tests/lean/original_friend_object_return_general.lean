namespace FriendObjectReturnGeneral
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


open OriginalFriendSumObject
open Proofs.Mod61Body

def inputs (a b c d : Nat) : List CppState.Binding := [⟨a,false⟩,⟨b,false⟩,⟨c,false⟩,⟨d,false⟩]
def fields (x n : Int) : List Cell := [⟨s64,x⟩,⟨i32,n⟩,⟨s64,x⟩,⟨i32,n⟩]
def add64 : NExpr := .binary s64 .add (.variable s64 0) (.variable s64 2)
def add32 : NExpr := .binary i32 .add (.variable i32 1) (.variable i32 3)
def rawBody : Command :=
  .sequence (.primitive (.declare s64 true add64))
    (.sequence (.primitive (.declare i32 true add32))
      (.sequence (.primitive (.declare s64 true (.variable s64 4)))
        (.sequence (.primitive (.declare i32 true (.variable i32 5)))
          (.sequence (.scope Sk) Sk))))
theorem body_shape : RangeSum_factory_op.body = rawBody := rfl

theorem add_value (env : Nat → Ty → Option Int) (ty : Ty) (i j : Nat) (x y : Int)
    (left : env i ty = some x) (right : env j ty = some y) (valid : ty.valid (x+y) = true) :
    (NExpr.binary ty .add (.variable ty i) (.variable ty j)).denote env = some (x+y) := by
  rw [den_binary,den_variable,den_variable,left,right]
  simpa [binaryValue] using Ty.convert_of_valid ty (x+y) valid

theorem raw_exec (P : List Cell) (a b c d : Nat) (x n y m : Int)
    (p0 : P[a]? = some ⟨s64,x⟩) (p1 : P[b]? = some ⟨i32,n⟩)
    (p2 : P[c]? = some ⟨s64,y⟩) (p3 : P[d]? = some ⟨i32,m⟩)
    (hx : s64.valid x = true) (hn : i32.valid n = true)
    (hy : s64.valid y = true) (hm : i32.valid m = true)
    (hs : s64.valid (x+y) = true) (ht : i32.valid (n+m) = true) :
    ∃ r, pexec 1 RangeSum_factory_op.body ⟨P,inputs a b c d⟩ = some r ∧
      r.ret = none ∧ r.cost = 13 ∧ r.need = P.length+15 ∧
      r.ps = ws P (inputs a b c d) (fields (x+y) (n+m)) := by
  let R := inputs a b c d
  let L1 : List Cell := [⟨s64,x+y⟩]
  let L2 : List Cell := [⟨s64,x+y⟩,⟨i32,n+m⟩]
  let L3 : List Cell := [⟨s64,x+y⟩,⟨i32,n+m⟩,⟨s64,x+y⟩]
  let L4 := fields (x+y) (n+m)
  have d0 : add64.denote (penv (ws P R [])) = some (x+y) :=
    add_value _ s64 0 2 x y
      (ws_env_ref P R [] 0 a false s64 x rfl p0 hx)
      (ws_env_ref P R [] 2 c false s64 y rfl p2 hy) hs
  have d1 : add32.denote (penv (ws P R L1)) = some (n+m) :=
    add_value _ i32 1 3 n m
      (ws_env_ref P R L1 1 b false i32 n rfl p1 hn)
      (ws_env_ref P R L1 3 d false i32 m rfl p3 hm) ht
  have d2 : (NExpr.variable s64 4).denote (penv (ws P R L2)) = some (x+y) := by
    rw [den_variable]
    exact ws_env_loc P R L2 0 ⟨s64,x+y⟩ s64 rfl rfl hs
  have d3 : (NExpr.variable i32 5).denote (penv (ws P R L3)) = some (n+m) := by
    rw [den_variable]
    exact ws_env_loc P R L3 1 ⟨i32,n+m⟩ i32 rfl rfl ht
  have q0 := (pexec_prim 1 _ _).trans (ws_declare P R [] s64 add64 (x+y) d0 (Ty.convert_of_valid _ _ hs))
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P R L1 i32 add32 (n+m) d1 (Ty.convert_of_valid _ _ ht))
  have q2 := (pexec_prim 1 _ _).trans (ws_declare P R L2 s64 (.variable s64 4) (x+y) d2 (Ty.convert_of_valid _ _ hs))
  have q3 := (pexec_prim 1 _ _).trans (ws_declare P R L3 i32 (.variable i32 5) (n+m) d3 (Ty.convert_of_valid _ _ ht))
  have sc0 := pexec_scope 1 Sk (ws P R L4) _ (pexec_skip 1 _)
  have sc : pexec 1 (.scope Sk) (ws P R L4) = some ⟨ws P R L4,none,1,P.length+12⟩ := by
    simp only [List.take_length] at sc0
    simpa [ws,R,inputs,L4,fields,Nat.add_assoc] using sc0
  have all := seq_some q0 rfl (seq_some q1 rfl (seq_some q2 rfl (seq_some q3 rfl (seq_some sc rfl (pexec_skip 1 _)))))
  refine ⟨⟨ws P R L4,none,13,P.length+15⟩,?_,rfl,rfl,rfl,rfl⟩
  rw [body_shape]
  simpa [rawBody,ws,R,inputs,L1,L2,L3,L4,fields,add64,add32,NExpr.nodes,Nat.add_assoc] using all
end FriendObjectReturnGeneral
