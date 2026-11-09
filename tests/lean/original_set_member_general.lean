namespace SetMemberGeneral
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
abbrev bl : Ty := ⟨1,false,true⟩
abbrev cn (n : Int) : Cell := ⟨i32,n⟩
abbrev cx (x : Int) : Cell := ⟨s64,x⟩
abbrev cf (f : Int) : Cell := ⟨bl,f⟩
def refs (a b : Nat) : List CppState.Binding := [⟨a,true⟩,⟨b,true⟩]
def selected (v f x n : Int) : Int := if f=0 then v*n else x
def product : NExpr := .binary s64 .mul (.variable s64 0) (.cast s64 (.variable i32 3))
def condition : NExpr := .unary bl .not (.variable bl 1)
def arm : Command := .sequence (.scope (.sequence (.primitive (.assign 2 s64 product)) Sk)) Sk
def update : Command := .branch condition arm Sk
def tailBody : Command := .sequence (.primitive (.declare s64 true (.variable s64 2)))
  (.sequence (.primitive (.declare i32 true (.variable i32 3))) Sk)
def rawBody : Command := .sequence update tailBody
theorem body_shape : RangeSum_factory_receiver1_apply.body = rawBody := rfl

theorem widen_size (n : Int) (hn : i32.valid n = true) : s64.valid n = true := by
  simp [Ty.valid] at hn ⊢
  omega

theorem update_exec (P : List Cell) (a b : Nat) (v f x n : Int)
    (receiver : P[a]? = some (cx v)) (flag : P[b]? = some (cf f))
    (hv : s64.valid v = true) (hf : bl.valid f = true)
    (hx : s64.valid x = true) (hn : i32.valid n = true)
    (hp : f=0 → s64.valid (v*n) = true) :
    ∃ r, pexec 1 update (ws P (refs a b) [cx x,cn n]) = some r ∧
      r.ret = none ∧ r.cost = (if f=0 then 9 else 3) ∧ r.need ≤ P.length+12 ∧
      r.ps = ws P (refs a b) [cx (selected v f x n),cn n] := by
  let R := refs a b
  let L : List Cell := [cx x,cn n]
  have readf : (NExpr.variable bl 1).denote (penv (ws P R L)) = some f := by
    rw [den_variable]
    exact ws_env_ref P R L 1 b true bl f rfl flag hf
  by_cases zero : f=0
  · have readv : (NExpr.variable s64 0).denote (penv (ws P R L)) = some v := by
      rw [den_variable]
      exact ws_env_ref P R L 0 a true s64 v rfl receiver hv
    have readn : (NExpr.variable i32 3).denote (penv (ws P R L)) = some n := by
      rw [den_variable]
      exact ws_env_loc P R L 1 (cn n) i32 rfl rfl hn
    have mul : product.denote (penv (ws P R L)) = some (v*n) := by
      rw [product,den_binary,readv,den_cast,readn]
      simpa [binaryValue,Ty.convert_of_valid s64 n (widen_size n hn)] using Ty.convert_of_valid s64 (v*n) (hp zero)
    have cond : condition.denote (penv (ws P R L)) = some 1 := by
      change ((penv (ws P R L) 1 bl).bind fun value => bl.convert (unaryValue .not value)) = _
      have envf : penv (ws P R L) 1 bl = some f := readf
      rw [envf]
      simp [zero,unaryValue,Ty.convert]
    have st := pstmt_assign_ok (ws P R L) 2 s64 product (v*n) mul ⟨P.length,true⟩ (cx x)
      (by simp [ws,R,refs,L,List.range_succ]) (by simp [ws,L,cx]) rfl hx rfl (v*n)
      (Ty.convert_of_valid _ _ (hp zero))
    have br := pexec_braced 1 (.assign 2 s64 product) (ws P R L) _ st rfl
      (by simp) rfl
    have run := pexec_branch_true 1 condition arm Sk (ws P R L) 1 cond (by decide) _ br
    refine ⟨_,run,rfl,?_,?_,?_⟩
    · simp [condition,product,NExpr.nodes,zero]
    · simp [ws,R,refs,L,condition,product,NExpr.nodes] <;> omega
    · simp [ws,R,refs,L,selected,zero,cx,cn,List.range_succ]
  · have cond : condition.denote (penv (ws P R L)) = some 0 := by
      change ((penv (ws P R L) 1 bl).bind fun value => bl.convert (unaryValue .not value)) = _
      have envf : penv (ws P R L) 1 bl = some f := readf
      rw [envf]
      simp [zero,unaryValue,Ty.convert]
    have run := pexec_branch_false 1 condition arm Sk (ws P R L) cond _ (pexec_skip 1 _)
    refine ⟨_,run,rfl,?_,?_,?_⟩
    · simp [condition,NExpr.nodes,zero]
    · simp [ws,R,refs,L,condition,NExpr.nodes] <;> omega
    · simp [selected,zero,R,L]

theorem raw_exec (P : List Cell) (a b : Nat) (v f x n : Int)
    (receiver : P[a]? = some (cx v)) (flag : P[b]? = some (cf f))
    (hv : s64.valid v = true) (hf : bl.valid f = true)
    (hx : s64.valid x = true) (hn : i32.valid n = true)
    (hp : f=0 → s64.valid (v*n) = true) :
    ∃ r, pexec 1 RangeSum_factory_receiver1_apply.body (ws P (refs a b) [cx x,cn n]) = some r ∧
      r.ret = none ∧ r.cost = (if f=0 then 13 else 7) ∧ r.need ≤ P.length+13 ∧
      r.ps = ws P (refs a b) [cx (selected v f x n),cn n,cx (selected v f x n),cn n] := by
  let R := refs a b
  let y := selected v f x n
  let L2 : List Cell := [cx y,cn n]
  let L3 : List Cell := L2 ++ [cx y]
  let L4 : List Cell := L3 ++ [cn n]
  have hy : s64.valid y = true := by unfold y selected; split; exact hp ‹f=0›; exact hx
  obtain ⟨u,qu,ru,cu,nu,pu⟩ := update_exec P a b v f x n receiver flag hv hf hx hn hp
  have readx : (NExpr.variable s64 2).denote (penv (ws P R L2)) = some y := by
    rw [den_variable]
    exact ws_env_loc P R L2 0 (cx y) s64 rfl rfl hy
  have readn : (NExpr.variable i32 3).denote (penv (ws P R L3)) = some n := by
    rw [den_variable]
    exact ws_env_loc P R L3 1 (cn n) i32 rfl rfl hn
  have q0 := (pexec_prim 1 _ _).trans (ws_declare P R L2 s64 (.variable s64 2) y readx (Ty.convert_of_valid _ _ hy))
  have q1 := (pexec_prim 1 _ _).trans (ws_declare P R L3 i32 (.variable i32 3) n readn (Ty.convert_of_valid _ _ hn))
  have tail := seq_some q0 rfl (seq_some q1 rfl (pexec_skip 1 _))
  have qt : pexec 1 tailBody u.ps = some ⟨ws P R L4,none,4,P.length+13⟩ := by
    rw [pu]
    simpa [tailBody,ws,R,refs,L2,L3,L4,NExpr.nodes,Nat.add_assoc] using tail
  have run := seq_some qu ru qt
  refine ⟨⟨ws P R L4,none,u.cost+4,max u.need (P.length+13)⟩,?_,rfl,?_,?_,rfl⟩
  · simpa [body_shape,rawBody] using run
  · simp [cu]; split <;> rfl
  · simp only [Nat.max_le]; constructor; exact Nat.le_trans nu (by omega); exact Nat.le_refl _
end SetMemberGeneral
