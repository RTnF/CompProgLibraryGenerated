namespace ExtremaObjectGeneral
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



open Proofs.Mod61Body

abbrev tail : Command :=
 .sequence (.primitive (.declare s64 true (.variable s64 2)))
  (.sequence (.primitive (.declare s64 true (.variable s64 3)))
   (.sequence (.primitive (.declare s64 true (.variable s64 4)))
    (.sequence (.scope Sk) Sk)))
abbrev selectionBody (i j : Nat) : Command :=
 .sequence (.primitive (.declare s64 true (.variable s64 0)))
  (.sequence (.branch (.binary Proofs.MonoidCall.bT .lt (.variable s64 i) (.variable s64 j))
    (.sequence (.scope (.sequence (.primitive (.assign 2 s64 (.variable s64 1))) Sk)) Sk) Sk) tail)

theorem tail_exec (P : List Cell) (a b : Nat) (v : Int) (hv : s64.valid v = true) :
 ∃ r, pexec 1 tail (ws P [⟨a,false⟩,⟨b,false⟩] [⟨s64,v⟩]) = some r ∧
   r.ret = none ∧ r.cost ≤ 12 ∧ r.need ≤ P.length+16 ∧
   r.ps = ws P [⟨a,false⟩,⟨b,false⟩] [⟨s64,v⟩,⟨s64,v⟩,⟨s64,v⟩,⟨s64,v⟩] := by
 let R : List CppState.Binding := [⟨a,false⟩,⟨b,false⟩]
 let L1 : List Cell := [⟨s64,v⟩]
 let L2 : List Cell := L1 ++ [⟨s64,v⟩]
 let L3 : List Cell := L2 ++ [⟨s64,v⟩]
 let L4 : List Cell := L3 ++ [⟨s64,v⟩]
 have e1 : penv (ws P R L1) 2 s64 = some v := ws_env_loc P R L1 0 ⟨s64,v⟩ s64 rfl rfl hv
 have s1 := ws_declare P R L1 s64 (.variable s64 2) v (by rw [den_variable]; exact e1) (convS _ hv)
 have q1 := (pexec_prim 1 _ _).trans s1
 have e2 : penv (ws P R L2) 3 s64 = some v := ws_env_loc P R L2 1 ⟨s64,v⟩ s64 rfl rfl hv
 have s2 := ws_declare P R L2 s64 (.variable s64 3) v (by rw [den_variable]; exact e2) (convS _ hv)
 have q2 := (pexec_prim 1 _ _).trans s2
 have e3 : penv (ws P R L3) 4 s64 = some v := ws_env_loc P R L3 2 ⟨s64,v⟩ s64 rfl rfl hv
 have s3 := ws_declare P R L3 s64 (.variable s64 4) v (by rw [den_variable]; exact e3) (convS _ hv)
 have q3 := (pexec_prim 1 _ _).trans s3
 have sc0 := pexec_scope 1 Sk (ws P R L4) _ (pexec_skip 1 _)
 have sc : pexec 1 (.scope Sk) (ws P R L4) = some ⟨ws P R L4,none,1,P.length+10⟩ := by
   simp only [List.take_length] at sc0
   simpa [ws,R,L1,L2,L3,L4,Nat.add_assoc] using sc0
 have qr := seq_some sc rfl (pexec_skip 1 _)
 have q3r := seq_some q3 rfl qr
 have q23r := seq_some q2 rfl q3r
 have qall := seq_some q1 rfl q23r
 refine ⟨_,qall,rfl,?_,?_,?_⟩
 · simp [NExpr.nodes]
 · simp [NExpr.nodes,ws,R,L1,L2,L3,L4]
 · simp [ws,R,L1,L2,L3,L4]

theorem selection_exec (i j : Nat) (hij : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) (P : List Cell) (a b : Nat) (x y : Int)
    (hxv : s64.valid x = true) (hyv : s64.valid y = true) (ha : P[a]? = some ⟨s64,x⟩) (hb : P[b]? = some ⟨s64,y⟩) :
    ∃ r, pexec 1 (selectionBody i j) ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = none ∧
      r.cost ≤ 40 ∧ r.need ≤ P.length+16 ∧ r.ps = ws P [⟨a,false⟩,⟨b,false⟩] [⟨s64,if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x⟩,⟨s64,if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x⟩,⟨s64,if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x⟩,⟨s64,if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x⟩] := by
  have hla : a < P.length := (List.getElem?_eq_some_iff.mp ha).1
  have hlb : b < P.length := (List.getElem?_eq_some_iff.mp hb).1
  have e0 : penv ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ 0 s64 = some x :=
    penv_ok _ 0 s64 ⟨a,false⟩ ⟨s64,x⟩ rfl ha rfl hxv
  have s1 := pstmt_declare_ok ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ s64 true (.variable s64 0) x (by rw [den_variable]; exact e0) x (convS _ hxv)
  have q1 := (pexec_prim 1 _ _).trans s1
  have hmemS1 : ∀ k, k < P.length → (P ++ [(⟨s64,x⟩ : Cell)])[k]? = P[k]? := fun k hk => List.getElem?_append_left hk
  have e0' : penv ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ 0 s64 = some x :=
    penv_ok _ 0 s64 ⟨a,false⟩ ⟨s64,x⟩ rfl (by simpa using (hmemS1 a hla).trans ha) rfl hxv
  have e1' : penv ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ 1 s64 = some y :=
    penv_ok _ 1 s64 ⟨b,false⟩ ⟨s64,y⟩ rfl (by simpa using (hmemS1 b hlb).trans hb) rfl hyv
  obtain ⟨u, hu⟩ : ∃ u, penv ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ i s64 = some u ∧
      u = if i = 0 then x else y := by
    rcases hij with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact ⟨x, e0', by simp⟩
    · exact ⟨y, e1', by simp⟩
  obtain ⟨w, hw⟩ : ∃ w, penv ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ j s64 = some w ∧
      w = if j = 0 then x else y := by
    rcases hij with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨y, e1', by simp⟩
    · exact ⟨x, e0', by simp⟩
  have hcond : (NExpr.binary bT .lt (.variable s64 i) (.variable s64 j)).denote
      (penv ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩) = some (if u < w then 1 else 0) := by
    rw [den_binary, den_variable, den_variable, hu.1, hw.1]
    simp only [Option.bind_some]
    have : binaryValue .lt u w = if u < w then 1 else 0 := rfl
    rw [this]
    unfold Ty.convert
    by_cases h : u < w <;> simp [h]
  have huw : (u < w) ↔ ((if i = 0 then x else y) < (if j = 0 then x else y)) := by rw [hu.2, hw.2]
  have hskip := pexec_skip 1 ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩
  by_cases hlt : u < w
  · rw [ite_eq_left hlt] at hcond
    have st := pstmt_assign_ok ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ 2 s64 (.variable s64 1) y
      (by rw [den_variable]; exact e1') ⟨P.length,true⟩ ⟨s64,x⟩ (by simp) (by simp) rfl hxv rfl y (convS _ hyv)
    have hset : (P ++ [(⟨s64,x⟩ : Cell)]).set P.length ⟨s64,y⟩ = P ++ [(⟨s64,y⟩ : Cell)] := by
      simp [List.set_append_right]
    rw [hset] at st
    have yes := pexec_braced 1 (.assign 2 s64 (.variable s64 1)) _ _ st rfl (by simp) (by simp)
    have br := pexec_branch_true 1 (.binary bT .lt (.variable s64 i) (.variable s64 j))
      (.sequence (.scope (.sequence (.primitive (.assign 2 s64 (.variable s64 1))) Sk)) Sk) Sk _ 1 hcond (by decide) _ yes
    obtain ⟨rT,qt,hrt,hct,hnt,hmt⟩ := tail_exec P a b y hyv
    have q3 : pexec 1 tail ⟨P ++ [(⟨s64,y⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ = some rT := by
      simpa [ws] using qt
    have q23 := seq_some br rfl q3
    have q123 := seq_some q1 rfl q23
    refine ⟨_, q123, ?_, ?_, ?_, ?_⟩
    · exact hrt
    · simp [NExpr.nodes]; omega
    · simp [NExpr.nodes]; omega
    · rw [ite_eq_left (huw.mp hlt)]; exact hmt
  · rw [ite_eq_right hlt] at hcond
    have br := pexec_branch_false 1 (.binary bT .lt (.variable s64 i) (.variable s64 j))
      (.sequence (.scope (.sequence (.primitive (.assign 2 s64 (.variable s64 1))) Sk)) Sk) Sk _ hcond _ hskip
    obtain ⟨rT,qt,hrt,hct,hnt,hmt⟩ := tail_exec P a b x hxv
    have q3 : pexec 1 tail ⟨P ++ [(⟨s64,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ = some rT := by
      simpa [ws] using qt
    have q23 := seq_some br rfl q3
    have q123 := seq_some q1 rfl q23
    refine ⟨_, q123, ?_, ?_, ?_, ?_⟩
    · exact hrt
    · simp [NExpr.nodes]; omega
    · simp [NExpr.nodes]; omega
    · rw [ite_eq_right (fun h => hlt (huw.mpr h))]; exact hmt

theorem selected_max (x y : Int) : (if x < y then y else x) = max x y := by
  rw [Int.max_def]
  split <;> split <;> omega

theorem selected_min (x y : Int) : (if y < x then y else x) = min x y := by
  rw [Int.min_def]
  split <;> split <;> omega

end ExtremaObjectGeneral
