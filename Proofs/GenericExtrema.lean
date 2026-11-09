import Proofs.GenericLazy
import Proofs.Mod61Body

namespace Proofs.GenericExtrema
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


open Proofs.MonoidLazyCall Proofs.MonoidCall Proofs.GenericCall Proofs.GenericLazy



open Proofs.Mod61Body

abbrev tail (ty : Ty) : Command :=
 .sequence (.primitive (.declare ty true (.variable ty 2)))
  (.sequence (.primitive (.declare ty true (.variable ty 3)))
   (.sequence (.primitive (.declare ty true (.variable ty 4)))
    (.sequence (.scope Sk) Sk)))
abbrev selectionBody (ty : Ty) (i j : Nat) : Command :=
 .sequence (.primitive (.declare ty true (.variable ty 0)))
  (.sequence (.branch (.binary Proofs.MonoidCall.bT .lt (.variable ty i) (.variable ty j))
    (.sequence (.scope (.sequence (.primitive (.assign 2 ty (.variable ty 1))) Sk)) Sk) Sk) (tail ty))

theorem tail_exec (ty : Ty) (P : List Cell) (a b : Nat) (v : Int) (hv : ty.valid v = true) :
 ∃ r, pexec 1 (tail ty) (ws P [⟨a,false⟩,⟨b,false⟩] [⟨ty,v⟩]) = some r ∧
   r.ret = none ∧ r.cost ≤ 12 ∧ r.need ≤ P.length+16 ∧
   r.ps = ws P [⟨a,false⟩,⟨b,false⟩] [⟨ty,v⟩,⟨ty,v⟩,⟨ty,v⟩,⟨ty,v⟩] := by
 let R : List CppState.Binding := [⟨a,false⟩,⟨b,false⟩]
 let L1 : List Cell := [⟨ty,v⟩]
 let L2 : List Cell := L1 ++ [⟨ty,v⟩]
 let L3 : List Cell := L2 ++ [⟨ty,v⟩]
 let L4 : List Cell := L3 ++ [⟨ty,v⟩]
 have e1 : penv (ws P R L1) 2 ty = some v := ws_env_loc P R L1 0 ⟨ty,v⟩ ty rfl rfl hv
 have s1 := ws_declare P R L1 ty (.variable ty 2) v (by rw [den_variable]; exact e1) (convG ty _ hv)
 have q1 := (pexec_prim 1 _ _).trans s1
 have e2 : penv (ws P R L2) 3 ty = some v := ws_env_loc P R L2 1 ⟨ty,v⟩ ty rfl rfl hv
 have s2 := ws_declare P R L2 ty (.variable ty 3) v (by rw [den_variable]; exact e2) (convG ty _ hv)
 have q2 := (pexec_prim 1 _ _).trans s2
 have e3 : penv (ws P R L3) 4 ty = some v := ws_env_loc P R L3 2 ⟨ty,v⟩ ty rfl rfl hv
 have s3 := ws_declare P R L3 ty (.variable ty 4) v (by rw [den_variable]; exact e3) (convG ty _ hv)
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

theorem selection_exec (ty : Ty) (i j : Nat) (hij : (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) (P : List Cell) (a b : Nat) (x y : Int)
    (hxv : ty.valid x = true) (hyv : ty.valid y = true) (ha : P[a]? = some ⟨ty,x⟩) (hb : P[b]? = some ⟨ty,y⟩) :
    ∃ r, pexec 1 (selectionBody ty i j) ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = none ∧
      r.cost ≤ 40 ∧ r.need ≤ P.length+16 ∧ r.ps = ws P [⟨a,false⟩,⟨b,false⟩] [⟨ty,if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x⟩,⟨ty,if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x⟩,⟨ty,if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x⟩,⟨ty,if (if i = 0 then x else y) < (if j = 0 then x else y) then y else x⟩] := by
  have hla : a < P.length := (List.getElem?_eq_some_iff.mp ha).1
  have hlb : b < P.length := (List.getElem?_eq_some_iff.mp hb).1
  have e0 : penv ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ 0 ty = some x :=
    penv_ok _ 0 ty ⟨a,false⟩ ⟨ty,x⟩ rfl ha rfl hxv
  have s1 := pstmt_declare_ok ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ ty true (.variable ty 0) x (by rw [den_variable]; exact e0) x (convG ty _ hxv)
  have q1 := (pexec_prim 1 _ _).trans s1
  have hmemS1 : ∀ k, k < P.length → (P ++ [(⟨ty,x⟩ : Cell)])[k]? = P[k]? := fun k hk => List.getElem?_append_left hk
  have e0' : penv ⟨P ++ [(⟨ty,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ 0 ty = some x :=
    penv_ok _ 0 ty ⟨a,false⟩ ⟨ty,x⟩ rfl (by simpa using (hmemS1 a hla).trans ha) rfl hxv
  have e1' : penv ⟨P ++ [(⟨ty,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ 1 ty = some y :=
    penv_ok _ 1 ty ⟨b,false⟩ ⟨ty,y⟩ rfl (by simpa using (hmemS1 b hlb).trans hb) rfl hyv
  obtain ⟨u, hu⟩ : ∃ u, penv ⟨P ++ [(⟨ty,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ i ty = some u ∧
      u = if i = 0 then x else y := by
    rcases hij with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact ⟨x, e0', by simp⟩
    · exact ⟨y, e1', by simp⟩
  obtain ⟨w, hw⟩ : ∃ w, penv ⟨P ++ [(⟨ty,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ j ty = some w ∧
      w = if j = 0 then x else y := by
    rcases hij with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · exact ⟨y, e1', by simp⟩
    · exact ⟨x, e0', by simp⟩
  have hcond : (NExpr.binary bT .lt (.variable ty i) (.variable ty j)).denote
      (penv ⟨P ++ [(⟨ty,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩) = some (if u < w then 1 else 0) := by
    rw [den_binary, den_variable, den_variable, hu.1, hw.1]
    simp only [Option.bind_some]
    have : binaryValue .lt u w = if u < w then 1 else 0 := rfl
    rw [this]
    unfold Ty.convert
    by_cases h : u < w <;> simp [h]
  have huw : (u < w) ↔ ((if i = 0 then x else y) < (if j = 0 then x else y)) := by rw [hu.2, hw.2]
  have hskip := pexec_skip 1 ⟨P ++ [(⟨ty,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩
  by_cases hlt : u < w
  · rw [ite_eq_left hlt] at hcond
    have st := pstmt_assign_ok ⟨P ++ [(⟨ty,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ 2 ty (.variable ty 1) y
      (by rw [den_variable]; exact e1') ⟨P.length,true⟩ ⟨ty,x⟩ (by simp) (by simp) rfl hxv rfl y (convG ty _ hyv)
    have hset : (P ++ [(⟨ty,x⟩ : Cell)]).set P.length ⟨ty,y⟩ = P ++ [(⟨ty,y⟩ : Cell)] := by
      simp [List.set_append_right]
    rw [hset] at st
    have yes := pexec_braced 1 (.assign 2 ty (.variable ty 1)) _ _ st rfl (by simp) (by simp)
    have br := pexec_branch_true 1 (.binary bT .lt (.variable ty i) (.variable ty j))
      (.sequence (.scope (.sequence (.primitive (.assign 2 ty (.variable ty 1))) Sk)) Sk) Sk _ 1 hcond (by decide) _ yes
    obtain ⟨rT,qt,hrt,hct,hnt,hmt⟩ := tail_exec ty P a b y hyv
    have q3 : pexec 1 (tail ty) ⟨P ++ [(⟨ty,y⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ = some rT := by
      simpa [ws] using qt
    have q23 := seq_some br rfl q3
    have q123 := seq_some q1 rfl q23
    refine ⟨_, q123, ?_, ?_, ?_, ?_⟩
    · exact hrt
    · simp [NExpr.nodes]; omega
    · simp [NExpr.nodes]; omega
    · rw [ite_eq_left (huw.mp hlt)]; exact hmt
  · rw [ite_eq_right hlt] at hcond
    have br := pexec_branch_false 1 (.binary bT .lt (.variable ty i) (.variable ty j))
      (.sequence (.scope (.sequence (.primitive (.assign 2 ty (.variable ty 1))) Sk)) Sk) Sk _ hcond _ hskip
    obtain ⟨rT,qt,hrt,hct,hnt,hmt⟩ := tail_exec ty P a b x hxv
    have q3 : pexec 1 (tail ty) ⟨P ++ [(⟨ty,x⟩ : Cell)],[⟨a,false⟩,⟨b,false⟩] ++ [⟨P.length,true⟩]⟩ = some rT := by
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

/-- Body of `e()` for `RangeMax`/`RangeMin`: `T lit = ...; T x = lit; { }`. -/
abbrev identBody (ty : Ty) (v : Int) : Command :=
  .sequence (.primitive (.declare ty true (.literal ty v)))
    (.sequence (.primitive (.declare ty true (.variable ty 0))) (.sequence (.scope Sk) Sk))

/-- Body of the default constructor: as `identBody`, then one more copy. -/
abbrev ctorBody (ty : Ty) (v : Int) : Command :=
  .sequence (.primitive (.declare ty true (.literal ty v)))
    (.sequence (.primitive (.declare ty true (.variable ty 0)))
      (.sequence (.scope Sk) (.sequence (.primitive (.declare ty true (.variable ty 1))) Sk)))

theorem ident_exec (ty : Ty) (P : List Cell) (v : Int) (hv : ty.valid v = true) :
    ∃ r, pexec 1 (identBody ty v) (ws P [] []) = some r ∧ r.ret = none ∧ r.cost ≤ 40 ∧
      r.need ≤ P.length + 16 ∧ r.ps = ws P [] [⟨ty,v⟩,⟨ty,v⟩] := by
  let R : List CppState.Binding := []
  have d0 : (NExpr.literal ty v).denote (penv (ws P R [])) = some v := by
    rw [den_literal, if_pos hv]
  have s1 := ws_declare P R [] ty (.literal ty v) v d0 (convG ty _ hv)
  have q1 := (pexec_prim 1 _ _).trans s1
  have e1 : penv (ws P R [⟨ty,v⟩]) (R.length + 0) ty = some v := ws_env_loc P R [⟨ty,v⟩] 0 ⟨ty,v⟩ ty rfl rfl hv
  have s2 := ws_declare P R [⟨ty,v⟩] ty (.variable ty (R.length + 0)) v (by rw [den_variable]; exact e1) (convG ty _ hv)
  have q2 := (pexec_prim 1 _ _).trans s2
  have sc0 := pexec_scope 1 Sk (ws P R ([⟨ty,v⟩] ++ [⟨ty,v⟩])) _ (pexec_skip 1 _)
  have sc : pexec 1 (.scope Sk) (ws P R ([⟨ty,v⟩] ++ [⟨ty,v⟩])) = some ⟨ws P R ([⟨ty,v⟩] ++ [⟨ty,v⟩]),none,1,P.length+4⟩ := by
    simp only [List.take_length] at sc0
    simpa [ws,R,Nat.add_assoc] using sc0
  have qr := seq_some sc rfl (pexec_skip 1 _)
  have q2r := seq_some q2 rfl qr
  have qall := seq_some q1 rfl q2r
  refine ⟨_,qall,rfl,?_,?_,?_⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes,ws,R]
  · simp [ws,R]

theorem ctor_exec (ty : Ty) (P : List Cell) (v : Int) (hv : ty.valid v = true) :
    ∃ r, pexec 1 (ctorBody ty v) (ws P [] []) = some r ∧ r.ret = none ∧ r.cost ≤ 40 ∧
      r.need ≤ P.length + 16 ∧ r.ps = ws P [] [⟨ty,v⟩,⟨ty,v⟩,⟨ty,v⟩] := by
  let R : List CppState.Binding := []
  have d0 : (NExpr.literal ty v).denote (penv (ws P R [])) = some v := by
    rw [den_literal, if_pos hv]
  have s1 := ws_declare P R [] ty (.literal ty v) v d0 (convG ty _ hv)
  have q1 := (pexec_prim 1 _ _).trans s1
  have e1 : penv (ws P R [⟨ty,v⟩]) (R.length + 0) ty = some v := ws_env_loc P R [⟨ty,v⟩] 0 ⟨ty,v⟩ ty rfl rfl hv
  have s2 := ws_declare P R [⟨ty,v⟩] ty (.variable ty (R.length + 0)) v (by rw [den_variable]; exact e1) (convG ty _ hv)
  have q2 := (pexec_prim 1 _ _).trans s2
  have sc0 := pexec_scope 1 Sk (ws P R ([⟨ty,v⟩] ++ [⟨ty,v⟩])) _ (pexec_skip 1 _)
  have sc : pexec 1 (.scope Sk) (ws P R ([⟨ty,v⟩] ++ [⟨ty,v⟩])) = some ⟨ws P R ([⟨ty,v⟩] ++ [⟨ty,v⟩]),none,1,P.length+4⟩ := by
    simp only [List.take_length] at sc0
    simpa [ws,R,Nat.add_assoc] using sc0
  have e3 : penv (ws P R ([⟨ty,v⟩] ++ [⟨ty,v⟩])) (R.length + 1) ty = some v :=
    ws_env_loc P R ([⟨ty,v⟩] ++ [⟨ty,v⟩]) 1 ⟨ty,v⟩ ty rfl rfl hv
  have s3 := ws_declare P R ([⟨ty,v⟩] ++ [⟨ty,v⟩]) ty (.variable ty (R.length + 1)) v (by rw [den_variable]; exact e3) (convG ty _ hv)
  have q3 := (pexec_prim 1 _ _).trans s3
  have q3r := seq_some q3 rfl (pexec_skip 1 _)
  have qsr := seq_some sc rfl q3r
  have q2r := seq_some q2 rfl qsr
  have qall := seq_some q1 rfl q2r
  refine ⟨_,qall,rfl,?_,?_,?_⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes,ws,R]
  · simp [ws,R]

/-- `std::numeric_limits<T>::lowest()`/`max()` for a non-bool integer type. -/
def lowestV (ty : Ty) : Int := if ty.signed then -(2 ^ (ty.width - 1)) else 0
def highestV (ty : Ty) : Int := if ty.signed then 2 ^ (ty.width - 1) - 1 else 2 ^ ty.width - 1

theorem lowestV_valid (ty : Ty) (hb : ty.boolean = false) : ty.valid (lowestV ty) = true := by
  unfold lowestV Ty.valid
  by_cases hs : ty.signed = true
  · have h : (0:Int) < 2 ^ (ty.width - 1) := Int.pow_pos (by decide)
    simp [hb, hs]
    omega
  · have hs' : ty.signed = false := by simpa using hs
    have h : (0:Int) < 2 ^ ty.width := Int.pow_pos (by decide)
    simp [hb, hs']
    omega

theorem highestV_valid (ty : Ty) (hb : ty.boolean = false) : ty.valid (highestV ty) = true := by
  unfold highestV Ty.valid
  by_cases hs : ty.signed = true
  · have h : (0:Int) < 2 ^ (ty.width - 1) := Int.pow_pos (by decide)
    simp [hb, hs]
    omega
  · have hs' : ty.signed = false := by simpa using hs
    have h : (0:Int) < 2 ^ ty.width := Int.pow_pos (by decide)
    simp [hb, hs']
    omega

example : lowestV ⟨32, true, false⟩ = -2147483648 := rfl
example : highestV ⟨32, true, false⟩ = 2147483647 := rfl
example : lowestV ⟨64, false, false⟩ = 0 := rfl
example : highestV ⟨64, false, false⟩ = 18446744073709551615 := rfl

end Proofs.GenericExtrema
