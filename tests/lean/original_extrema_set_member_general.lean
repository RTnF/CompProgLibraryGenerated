namespace ExtremaSetMemberGeneral
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
abbrev bl : Ty := ⟨1,false,true⟩
abbrev cx (x : Int) : Cell := ⟨s64,x⟩
abbrev cf (f : Int) : Cell := ⟨bl,f⟩
def refs (a b : Nat) : List CppState.Binding := [⟨a,true⟩,⟨b,true⟩]
def selected (v f x : Int) : Int := if f=0 then v else x
def yesInner : Command := .sequence (.primitive (.declare s64 true (.variable s64 2)))
  (.sequence (.primitive (.assign 3 s64 (.variable s64 4))) Sk)
def noInner : Command := .sequence (.primitive (.declare s64 true (.variable s64 0)))
  (.sequence (.primitive (.declare s64 true (.variable s64 4)))
    (.sequence (.scope Sk) (.sequence (.primitive (.assign 3 s64 (.variable s64 5))) Sk)))
def yesBody : Command := .sequence (.scope yesInner) Sk
def noBody : Command := .sequence (.scope noInner) Sk
def choice : Command := .branch (.variable bl 1) yesBody noBody
def rawBody : Command := .sequence (.primitive (.declare s64 true (.literal s64 0)))
  (.sequence choice Sk)
theorem body_shape : SelectedExtrema.applyProgram.body = rawBody := rfl

theorem ws_assign_second (P : List Cell) (R : List CppState.Binding) (L : List Cell)
    (x : Int) (e : NExpr) (v : Int) (hv : s64.valid v = true)
    (de : e.denote (penv (ws P R (cx x :: cx 0 :: L))) = some v) :
    pstmt (.assign (R.length+1) s64 e) (ws P R (cx x :: cx 0 :: L)) =
      some ⟨ws P R (cx x :: cx v :: L),none,e.nodes+1,
        P.length+R.length+2*(L.length+2)+e.nodes+2⟩ := by
  have h := pstmt_assign_ok (ws P R (cx x :: cx 0 :: L)) (R.length+1) s64 e v de
    ⟨P.length+1,true⟩ (cx 0) (by simp [ws]) (by simp [ws]) rfl rfl rfl v (Ty.convert_of_valid s64 v hv)
  have mem : (ws P R (cx x :: cx 0 :: L)).mem.set (P.length+1) (cx v) =
      (ws P R (cx x :: cx v :: L)).mem := by simp [ws]
  have need : (ws P R (cx x :: cx 0 :: L)).mem.length +
      (ws P R (cx x :: cx 0 :: L)).bs.length+e.nodes+2 =
      P.length+R.length+2*(L.length+2)+e.nodes+2 := by simp [ws]; omega
  rw [h,mem,need]
  rfl

theorem choice_exec (P : List Cell) (a b : Nat) (v f x : Int)
    (receiver : P[a]? = some (cx v)) (flag : P[b]? = some (cf f))
    (hv : s64.valid v = true) (hf : bl.valid f = true) (hx : s64.valid x = true) :
    ∃ r, pexec 1 choice (ws P (refs a b) [cx x,cx 0]) = some r ∧
      r.ret = none ∧ r.cost = (if f=0 then 10 else 7) ∧ r.need ≤ P.length+13 ∧
      r.ps = ws P (refs a b) [cx x,cx (selected v f x)] := by
  let R := refs a b
  have cond : (NExpr.variable bl 1).denote (penv (ws P R [cx x,cx 0])) = some f := by
    rw [den_variable]; exact ws_env_ref P R _ 1 b true bl f rfl flag hf
  by_cases zero : f=0
  · have dv : (NExpr.variable s64 0).denote (penv (ws P R [cx x,cx 0])) = some v := by
      rw [den_variable]; exact ws_env_ref P R _ 0 a true s64 v rfl receiver hv
    have q0 := (pexec_prim 1 _ _).trans (ws_declare P R [cx x,cx 0] s64 (.variable s64 0) v dv (Ty.convert_of_valid _ _ hv))
    have dv2 : (NExpr.variable s64 4).denote (penv (ws P R [cx x,cx 0,cx v])) = some v := by
      rw [den_variable]; exact ws_env_loc P R _ 2 (cx v) s64 rfl rfl hv
    have q1 := (pexec_prim 1 _ _).trans (ws_declare P R [cx x,cx 0,cx v] s64 (.variable s64 4) v dv2 (Ty.convert_of_valid _ _ hv))
    have dv3 : (NExpr.variable s64 5).denote (penv (ws P R [cx x,cx 0,cx v,cx v])) = some v := by
      rw [den_variable]; exact ws_env_loc P R _ 3 (cx v) s64 rfl rfl hv
    have q2 := (pexec_prim 1 _ _).trans (ws_assign_second P R [cx v,cx v] x (.variable s64 5) v hv dv3)
    have sc0 := pexec_scope 1 Sk (ws P R [cx x,cx 0,cx v,cx v]) _ (pexec_skip 1 _)
    have sc : pexec 1 (.scope Sk) (ws P R [cx x,cx 0,cx v,cx v]) =
        some ⟨ws P R [cx x,cx 0,cx v,cx v],none,1,P.length+10⟩ := by
      simp only [List.take_length] at sc0
      simpa [ws,R,refs,List.range_succ] using sc0
    have body := seq_some q0 rfl (seq_some q1 rfl (seq_some sc rfl (seq_some q2 rfl (pexec_skip 1 _))))
    have scope := pexec_scope 1 noInner (ws P R [cx x,cx 0]) _ body
    have clean : pexec 1 noBody (ws P R [cx x,cx 0]) =
        some ⟨ws P R [cx x,cx v],none,8,P.length+13⟩ := by
      have whole := seq_some scope rfl (pexec_skip 1 _)
      simpa [noBody,noInner,ws,R,refs,NExpr.nodes,List.take_append,List.range_succ,List.take_of_length_le,Nat.add_assoc] using whole
    have br := pexec_branch_false 1 (.variable bl 1) yesBody noBody (ws P R [cx x,cx 0])
      (by simpa [zero] using cond) _ clean
    refine ⟨_,br,rfl,?_,?_,?_⟩
    · simp [NExpr.nodes,zero]
    · simp [ws,R,refs,NExpr.nodes]
    · simp [selected,zero,R]
  · have dx : (NExpr.variable s64 2).denote (penv (ws P R [cx x,cx 0])) = some x := by
      rw [den_variable]; exact ws_env_loc P R _ 0 (cx x) s64 rfl rfl hx
    have q0 := (pexec_prim 1 _ _).trans (ws_declare P R [cx x,cx 0] s64 (.variable s64 2) x dx (Ty.convert_of_valid _ _ hx))
    have dx2 : (NExpr.variable s64 4).denote (penv (ws P R [cx x,cx 0,cx x])) = some x := by
      rw [den_variable]; exact ws_env_loc P R _ 2 (cx x) s64 rfl rfl hx
    have q1 := (pexec_prim 1 _ _).trans (ws_assign_second P R [cx x] x (.variable s64 4) x hx dx2)
    have body := seq_some q0 rfl (seq_some q1 rfl (pexec_skip 1 _))
    have scope := pexec_scope 1 yesInner (ws P R [cx x,cx 0]) _ body
    have clean : pexec 1 yesBody (ws P R [cx x,cx 0]) =
        some ⟨ws P R [cx x,cx x],none,5,P.length+11⟩ := by
      have whole := seq_some scope rfl (pexec_skip 1 _)
      simpa [yesBody,yesInner,ws,R,refs,NExpr.nodes,List.take_append,List.range_succ,List.take_of_length_le,Nat.add_assoc] using whole
    have br := pexec_branch_true 1 (.variable bl 1) yesBody noBody (ws P R [cx x,cx 0]) f cond zero _ clean
    refine ⟨_,br,rfl,?_,?_,?_⟩
    · simp [NExpr.nodes,zero]
    · simp [ws,R,refs,NExpr.nodes]
    · simp [selected,zero,R]

theorem raw_exec (P : List Cell) (a b : Nat) (v f x : Int)
    (receiver : P[a]? = some (cx v)) (flag : P[b]? = some (cf f))
    (hv : s64.valid v = true) (hf : bl.valid f = true) (hx : s64.valid x = true) :
    ∃ r, pexec 1 SelectedExtrema.applyProgram.body (ws P (refs a b) [cx x]) = some r ∧
      r.ret = none ∧ r.cost = (if f=0 then 12 else 9) ∧ r.need ≤ P.length+13 ∧
      r.ps = ws P (refs a b) [cx x,cx (selected v f x)] := by
  let R := refs a b
  have q0 := (pexec_prim 1 _ _).trans (ws_declare P R [cx x] s64 (.literal s64 0) 0 rfl rfl)
  obtain ⟨u,qu,ru,cu,nu,pu⟩ := choice_exec P a b v f x receiver flag hv hf hx
  have run := seq_some q0 rfl (seq_some qu ru (pexec_skip 1 _))
  refine ⟨⟨u.ps,none,2+u.cost,max (P.length+9) (max u.need (u.ps.mem.length+u.ps.bs.length))⟩,?_,rfl,?_,?_,?_⟩
  · simpa [body_shape,rawBody,ws,R,refs,NExpr.nodes,Nat.add_assoc] using run
  · simp [cu]; split <;> rfl
  · simp [ws,refs,pu] <;> omega
  · exact pu

end ExtremaSetMemberGeneral
