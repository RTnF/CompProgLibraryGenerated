namespace SetObjectGeneral
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


open OriginalSetObject

open Proofs.Mod61Body

abbrev cx (x : Int) : Cell := ⟨s64,x⟩
abbrev cf (f : Int) : Cell := ⟨bl,f⟩
def inputs (x f y g : Int) : List Cell := [cx x,cf f,cx y,cf g]
def refs (P : List Cell) : List CppState.Binding :=
  (List.range 4).map (fun i => ⟨P.length+i,true⟩) ++ [⟨P.length+4,false⟩]
def selectedValue (x f y : Int) : Int := if f=0 then x else y
def selectedFlag (f g : Int) : Int := if f=0 then f else g

def arm (ty : Ty) (dst source : Nat) : Command :=
  .sequence (.scope (.sequence (.primitive (.assign dst ty (.variable ty source))) Sk)) Sk
def choose (ty : Ty) (flag dst yes no : Nat) : Command :=
  .branch (.variable bl flag) (arm ty dst yes) (arm ty dst no)

theorem choose_assign (ps : PS) (ty : Ty) (flag dst yes no : Nat) (c x y z : Int)
    (hc : (NExpr.variable bl flag).denote (penv ps) = some c)
    (hx : (NExpr.variable ty no).denote (penv ps) = some x)
    (hy : (NExpr.variable ty yes).denote (penv ps) = some y)
    (vx : ty.valid x = true) (vy : ty.valid y = true)
    (binding : CppState.Binding) (hb : ps.bs[dst]? = some binding)
    (hm : ps.mem[binding.address]? = some ⟨ty,z⟩) (vz : ty.valid z = true)
    (hw : binding.writable = true) :
    ∃ r, pexec 1 (choose ty flag dst yes no) ps = some r ∧
      r.ret = none ∧ r.cost = 5 ∧ r.need = ps.mem.length+ps.bs.length+3 ∧
      r.ps = ⟨ps.mem.set binding.address ⟨ty,if c=0 then x else y⟩,ps.bs⟩ := by
  by_cases zero : c=0
  · have st := pstmt_assign_ok ps dst ty (.variable ty no) x hx binding ⟨ty,z⟩ hb hm rfl vz hw x
      (Ty.convert_of_valid ty x vx)
    have br := pexec_braced 1 (.assign dst ty (.variable ty no)) ps _ st rfl (by simp) rfl
    have q := pexec_branch_false 1 (.variable bl flag) (arm ty dst yes) (arm ty dst no) ps (by simpa [zero] using hc) _ br
    refine ⟨_,q,rfl,?_,?_,?_⟩
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]; omega
    · simp [zero]
  · have st := pstmt_assign_ok ps dst ty (.variable ty yes) y hy binding ⟨ty,z⟩ hb hm rfl vz hw y
      (Ty.convert_of_valid ty y vy)
    have br := pexec_braced 1 (.assign dst ty (.variable ty yes)) ps _ st rfl (by simp) rfl
    have q := pexec_branch_true 1 (.variable bl flag) (arm ty dst yes) (arm ty dst no) ps c hc zero _ br
    refine ⟨_,q,rfl,?_,?_,?_⟩
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]; omega
    · simp [zero]

def tailBody : Command :=
  .sequence (.primitive (.declare s64 true (.literal s64 0)))
    (.sequence (choose s64 4 5 2 0)
      (.sequence (.primitive (.declare s64 true (.variable s64 5)))
        (.sequence (.primitive (.declare bl true (.literal bl 0)))
          (.sequence (choose bl 4 7 3 1)
            (.sequence (.primitive (.declare bl true (.variable bl 7))) Sk)))))
def rawBody : Command :=
  .sequence (.primitive (.declare bl false (.variable bl 1))) tailBody

theorem body_shape : RangeSet_factory_compose.body = rawBody := rfl

theorem tail_exec (P : List Cell) (x f y g : Int)
    (hx : s64.valid x = true) (hf : bl.valid f = true)
    (hy : s64.valid y = true) (hg : bl.valid g = true) :
    ∃ r, pexec 1 tailBody ⟨P ++ inputs x f y g ++ [cf f],refs P⟩ = some r ∧
      r.ret = none ∧ r.cost = 18 ∧ r.need = P.length+21 ∧
      r.ps = ws (P ++ inputs x f y g ++ [cf f]) (refs P)
        [cx (selectedValue x f y),cx (selectedValue x f y),cf (selectedFlag f g),cf (selectedFlag f g)] := by
  let M := P ++ inputs x f y g ++ [cf f]
  let R := refs P
  let v := selectedValue x f y
  let n := selectedFlag f g
  let L1 : List Cell := [cx 0]
  let L1' : List Cell := [cx v]
  let L2 : List Cell := [cx v,cx v]
  let L3 : List Cell := [cx v,cx v,cf 0]
  let L3' : List Cell := [cx v,cx v,cf n]
  let L4 : List Cell := [cx v,cx v,cf n,cf n]
  have vv : s64.valid v = true := by unfold v selectedValue; split <;> assumption
  have vn : bl.valid n = true := by unfold n selectedFlag; split <;> assumption
  have flag (L : List Cell) : (NExpr.variable bl 4).denote (penv (ws M R L)) = some f := by
    rw [den_variable]
    exact ws_env_ref M R L 4 (P.length+4) false bl f (by simp [R,refs]) (by simp [M,inputs,cf]) hf
  have value0 (L : List Cell) : (NExpr.variable s64 0).denote (penv (ws M R L)) = some x := by
    rw [den_variable]
    exact ws_env_ref M R L 0 P.length true s64 x (by simp [R,refs,List.range_succ]) (by simp [M,inputs,cx]) hx
  have value2 (L : List Cell) : (NExpr.variable s64 2).denote (penv (ws M R L)) = some y := by
    rw [den_variable]
    exact ws_env_ref M R L 2 (P.length+2) true s64 y (by simp [R,refs,List.range_succ]) (by simp [M,inputs,cx]) hy
  have flag1 (L : List Cell) : (NExpr.variable bl 1).denote (penv (ws M R L)) = some f := by
    rw [den_variable]
    exact ws_env_ref M R L 1 (P.length+1) true bl f (by simp [R,refs,List.range_succ]) (by simp [M,inputs,cf]) hf
  have flag3 (L : List Cell) : (NExpr.variable bl 3).denote (penv (ws M R L)) = some g := by
    rw [den_variable]
    exact ws_env_ref M R L 3 (P.length+3) true bl g (by simp [R,refs,List.range_succ]) (by simp [M,inputs,cf]) hg
  have z64 : s64.valid 0 = true := by decide
  have zb : bl.valid 0 = true := by decide
  have q0 := (pexec_prim 1 _ _).trans (ws_declare M R [] s64 (.literal s64 0) 0
    (by simp [NExpr.denote,z64]) (Ty.convert_of_valid _ _ z64))
  obtain ⟨b1,qb1,rb1,cb1,nb1,pb1⟩ := choose_assign (ws M R L1) s64 4 5 2 0 f x y 0
    (flag L1) (value0 L1) (value2 L1) hx hy ⟨M.length,true⟩
    (by simp [ws,R,refs,L1,List.range_succ]) (by simp [ws,L1,cx]) z64 rfl
  have q1 : pexec 1 (choose s64 4 5 2 0) (ws M R L1) =
      some ⟨ws M R L1',none,5,P.length+15⟩ := by
    have eq : b1 = ⟨ws M R L1',none,5,P.length+15⟩ := by
      cases b1
      simp_all [ws,M,R,refs,L1,L1',v,selectedValue,inputs,List.set_append_right,Nat.add_assoc,cx,cf]
    simpa [eq] using qb1
  have ev : (NExpr.variable s64 5).denote (penv (ws M R L1')) = some v := by
    rw [den_variable]
    simpa [R,refs] using ws_env_loc M R L1' 0 (cx v) s64 rfl rfl vv
  have q2 := (pexec_prim 1 _ _).trans (ws_declare M R L1' s64 (.variable s64 5) v ev (Ty.convert_of_valid _ _ vv))
  have q3 := (pexec_prim 1 _ _).trans (ws_declare M R L2 bl (.literal bl 0) 0
    (by simp [NExpr.denote,zb]) (Ty.convert_of_valid _ _ zb))
  obtain ⟨b2,qb2,rb2,cb2,nb2,pb2⟩ := choose_assign (ws M R L3) bl 4 7 3 1 f f g 0
    (flag L3) (flag1 L3) (flag3 L3) hf hg ⟨M.length+2,true⟩
    (by simp [ws,R,refs,L3,List.range_succ]) (by simp [ws,L3,cf]) zb rfl
  have q4 : pexec 1 (choose bl 4 7 3 1) (ws M R L3) =
      some ⟨ws M R L3',none,5,P.length+19⟩ := by
    have eq : b2 = ⟨ws M R L3',none,5,P.length+19⟩ := by
      cases b2
      simp_all [ws,M,R,refs,L3,L3',n,selectedFlag,inputs,List.set_append_right,Nat.add_assoc,cx,cf]
    simpa [eq] using qb2
  have en : (NExpr.variable bl 7).denote (penv (ws M R L3')) = some n := by
    rw [den_variable]
    simpa [R,refs] using ws_env_loc M R L3' 2 (cf n) bl rfl rfl vn
  have q5 := (pexec_prim 1 _ _).trans (ws_declare M R L3' bl (.variable bl 7) n en (Ty.convert_of_valid _ _ vn))
  have all := seq_some q0 rfl (seq_some q1 rfl (seq_some q2 rfl (seq_some q3 rfl (seq_some q4 rfl
    (seq_some q5 rfl (pexec_skip 1 _))))))
  refine ⟨⟨ws M R L4,none,18,P.length+21⟩,?_,rfl,rfl,rfl,rfl⟩
  simpa [tailBody,ws,M,R,refs,inputs,L1,L1',L2,L3,L3',L4,v,n,cx,cf,NExpr.nodes,Nat.add_assoc] using all

theorem raw_exec (P : List Cell) (x f y g : Int)
    (hx : s64.valid x = true) (hf : bl.valid f = true)
    (hy : s64.valid y = true) (hg : bl.valid g = true) :
    ∃ r, pexec 1 RangeSet_factory_compose.body (ws P [] (inputs x f y g)) = some r ∧
      r.ret = none ∧ r.cost = 20 ∧ r.need = P.length+21 ∧
      r.ps = ws (P ++ inputs x f y g ++ [cf f]) (refs P)
        [cx (selectedValue x f y),cx (selectedValue x f y),cf (selectedFlag f g),cf (selectedFlag f g)] := by
  have ev : (NExpr.variable bl 1).denote (penv (ws P [] (inputs x f y g))) = some f := by
    rw [den_variable]
    exact ws_env_loc P [] (inputs x f y g) 1 (cf f) bl rfl rfl hf
  have q0 := (pexec_prim 1 _ _).trans (pstmt_declare_ok (ws P [] (inputs x f y g)) bl false
    (.variable bl 1) f ev f (Ty.convert_of_valid _ _ hf))
  obtain ⟨r,ran,ret,cost,need,ps⟩ := tail_exec P x f y g hx hf hy hg
  have q1 : pexec 1 tailBody
      ⟨(ws P [] (inputs x f y g)).mem ++ [cf f],
       (ws P [] (inputs x f y g)).bs ++ [⟨(ws P [] (inputs x f y g)).mem.length,false⟩]⟩ = some r := by
    simpa [ws,refs,inputs,List.range_succ,Nat.add_assoc] using ran
  have all := seq_some q0 rfl q1
  refine ⟨⟨r.ps,none,20,P.length+21⟩,?_,rfl,rfl,rfl,ps⟩
  rw [body_shape]
  have peakBound : max (P.length+13) (P.length+21) = P.length+21 := Nat.max_eq_right (by omega)
  simpa [rawBody,ret,cost,need,NExpr.nodes,ws,inputs,Nat.add_assoc,peakBound] using all

end SetObjectGeneral
