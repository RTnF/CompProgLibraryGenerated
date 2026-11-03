import Proofs.Mod61Body
import Proofs.Generated.Extrema

namespace Proofs.ExtremaRef
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.FlatVectorStmt Proofs.QuotientFrame
open Proofs.QuotientSearch Proofs.Mod61Body
open Proofs.CppState (Cell)

abbrev s64 : Ty := ⟨64,true,false⟩

abbrev condE (i j : Nat) : NExpr := .binary bl .lt (.variable s64 i) (.variable s64 j)
abbrev yesCh : Command :=
  .sequence (.scope (.sequence (.primitive (.assign 0 s64 (.variable s64 1)))
    (.sequence (.primitive (.assign 2 bl (.literal bl 1))) (.primitive .skip)))) (.primitive .skip)
abbrev chCmd (i j : Nat) : Command :=
  .sequence (.primitive (.declare bl true (.literal bl 0)))
    (.sequence (.branch (condE i j) yesCh (.primitive .skip))
      (.sequence (.primitive (.ret (.variable bl 2))) (.primitive .skip)))

theorem chmax_body_eq : Proofs.ExtremaLibInstance.chmax_long_long.body = chCmd 0 1 := rfl
theorem chmin_body_eq : Proofs.ExtremaLibInstance.chmin_long_long.body = chCmd 1 0 := rfl


theorem env_qs {S : NState} {P : List Cell} {B sc : Nat} {cells : List Cell} {binds : List CppState.Binding}
    {slots : List Location} (qs : QS S P B sc cells binds slots) (slot idx : Nat) (binding : CppState.Binding)
    (ty : Ty) (v : Int) (hs : slots[slot]? = some (.scalar idx)) (hb : binds[idx]? = some binding)
    (hm : (P ++ cells)[binding.address]? = some ⟨ty,v⟩) (valid : ty.valid v = true) :
    envOf S slot ty = some v :=
  envOf_at S slot idx binding ty v (by rw [qs.slots]; exact hs) (by rw [qs.bindings]; exact hb)
    (by rw [qs.memory]; exact hm) valid

theorem s64_valid_of {v : Int} (h : s64.valid v = true) : s64.valid v = true := h

abbrev bind0 (aa ab : Nat) : List CppState.Binding := [⟨aa,true⟩,⟨ab,false⟩]
abbrev slots0 : List Location := [.scalar 0,.scalar 1]

-- `bool changed = false;`
theorem decl_changed {P : List Cell} {B sc L0 T0 N scq SPB TPB W : Nat} (S : NState) (aa ab : Nat)
    (qs : QS S P B sc [] (bind0 aa ab) slots0) (cq : Cq SPB TPB W S) (cap : liveS S+4 ≤ SPB) :
    ∃ t, (NStmt.declare bl true (.literal bl 0)).run S = some ⟨t,none,false⟩ ∧ t.frame = S.frame ∧
      QS t P B sc [⟨bl,0⟩] (bind0 aa ab ++ [⟨P.length,true⟩]) (slots0 ++ [.scalar 2]) ∧ Cq SPB TPB (W+2) t := by
  have lit : bl.valid 0 = true := by simp [Ty.valid]
  obtain ⟨t,run,fr,qs',cq'⟩ := decl_step S (.literal bl 0) bl true 0 0 qs cq (by simp [NExpr.nodes]; omega)
    (by simp [NExpr.scalarOnly]) (by simp [NExpr.denote,lit]) (Ty.convert_of_valid _ _ lit)
  exact ⟨t,run,fr,by simpa using qs',cq'.mono (by simp [NExpr.nodes])⟩


-- Scope exit when cells of the caller prefix were overwritten inside the scope.
theorem leave_pack2 {outer inner : NState} {P P' : List Cell} {B sc : Nat} {cells cells' : List Cell}
    {binds : List CppState.Binding} {slots : List Location} {L0 T0 N scq SPB TPB W W' : Nat}
    (qs : QS outer P B sc cells binds slots) (qsI : QS inner P' B (sc+1) cells' binds slots)
    (hty : (P' ++ cells').map Cell.type = (P ++ cells).map Cell.type)
    (faI : FA inner.frame L0 T0 scq N) (hsc : scq ≤ sc)
    (co : Cq SPB TPB W outer) (ci : Cq SPB TPB W' inner) (cap : liveS outer ≤ SPB) (hL : L0 ≤ TPB) :
    ∃ r, outer.leave inner none = some r ∧ QS r P' B sc cells' binds slots ∧ FA r.frame L0 T0 scq N ∧
      Cq SPB TPB (W'+1) r := by
  have hm : inner.scalars.memory = (P' ++ cells') ++ [] := by rw [qsI.memory]; simp
  have hty' : (P' ++ cells').map Cell.type = outer.scalars.memory.map Cell.type := by rw [qs.memory]; exact hty
  obtain ⟨leaveEq,memEq⟩ := leave_gen outer inner (P' ++ cells') [] hm hty' faI.valid
    (by rw [qs.scope]; exact faI.fresh hsc)
  have lens : (P' ++ cells').length = outer.scalars.memory.length := by
    have := congrArg List.length hty'; simpa using this
  have lengthTake : (inner.scalars.memory.take outer.scalars.memory.length).length = outer.scalars.memory.length := by
    rw [hm,← lens]; rw [List.take_left]
  refine ⟨outer.left inner,leaveEq,⟨?_,?_,?_,?_,?_⟩,?_,?_⟩
  · rw [left_slots]; exact qs.slots
  · rw [memEq]
  · rw [left_bindings]; exact qs.bindings
  · rw [left_baseMemory]; exact qs.base
  · rw [left_scope]; exact qs.scope
  · refine faI.noop (by rw [left_state]; exact noopRetired_same _) (by rw [left_rootWritable]) ?_ ?_
    · rw [left_state]; rfl
    · rw [left_frameBindings,faI.bindings]; exact List.take_nil
  · refine Cb.left co ci lengthTake cap ?_
    have e : (fx SPB TPB).TPB = TPB := rfl
    rw [faI.live]; omega


theorem map_type_set (P : List Cell) (aa : Nat) (va vb : Int) (ha : P[aa]? = some ⟨s64,va⟩) :
    (P.set aa ⟨s64,vb⟩).map Cell.type = P.map Cell.type := by
  apply List.ext_getElem?
  intro k
  by_cases h : k = aa
  · subst h
    have aaLt : k < P.length := (List.getElem?_eq_some_iff.mp ha).1
    have lt : k < (P.map Cell.type).length := by simpa using aaLt
    simp [List.getElem?_set_self lt,ha]
  · simp [List.getElem?_set_ne (Ne.symm h)]

-- `{ a = b; changed = true; }`
theorem yes_ref {P : List Cell} {B sc L0 T0 N scq SPB TPB W : Nat} (U : NState) (aa ab : Nat) (va vb : Int)
    (ha : P[aa]? = some ⟨s64,va⟩) (hb : P[ab]? = some ⟨s64,vb⟩) (vva : s64.valid va = true)
    (vvb : s64.valid vb = true)
    (qs : QS U P B sc [⟨bl,0⟩] (bind0 aa ab ++ [⟨P.length,true⟩]) (slots0 ++ [.scalar 2]))
    (fa : FA U.frame L0 T0 scq N) (cq : Cq SPB TPB W U) (cap : liveS U+8 ≤ SPB) (hsc : scq ≤ sc)
    (hL : L0 ≤ TPB) :
    RunsTo yesCh U fun step => step.returned = none ∧ step.breaking = false ∧
      QS step.state (P.set aa ⟨s64,vb⟩) B sc [⟨bl,1⟩] (bind0 aa ab ++ [⟨P.length,true⟩]) (slots0 ++ [.scalar 2]) ∧
      FA step.state.frame L0 T0 scq N ∧ Cq SPB TPB (W+12) step.state := by
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have aaLt : aa < P.length := (List.getElem?_eq_some_iff.mp ha).1
  have abLt : ab < P.length := (List.getElem?_eq_some_iff.mp hb).1
  have qs1 := qs.enter
  have cq1 := cq.enter
  have liveEq : liveS (scopeUp U) = liveS U := rfl
  have e1 : envOf (scopeUp U) 1 s64 = some vb :=
    env_qs qs1 1 1 ⟨ab,false⟩ s64 vb (by simp) (by simp [bind0]) (by simp [List.getElem?_append_left abLt,hb]) vvb
  obtain ⟨t1,run1,fr1,sl1,sc1,me1,bi1,ba1,wl1,wu1,pl1,pu1,ql1,qu1,live1⟩ :=
    assign_good (.variable s64 1) 0 0 s64 (scopeUp U) vb vb ⟨aa,true⟩ ⟨s64,va⟩ (by simp [NExpr.scalarOnly])
      (by rw [den_variable]; exact e1) (Ty.convert_of_valid _ _ vvb) (by simp [qs1.slots])
      (by simp [qs1.bindings,bind0]) (by simp [qs1.memory,List.getElem?_append_left aaLt,ha]) rfl vva rfl
  have memT1 : t1.scalars.memory = P.set aa ⟨s64,vb⟩ ++ [⟨bl,0⟩] := by
    rw [me1]; simp [qs1.memory,List.set_append_left aa _ aaLt]
  have lenP : (P.set aa ⟨s64,vb⟩).length = P.length := by simp
  have qs2 : QS t1 (P.set aa ⟨s64,vb⟩) B (sc+1) [⟨bl,0⟩] (bind0 aa ab ++ [⟨P.length,true⟩])
      (slots0 ++ [.scalar 2]) := ⟨by rw [sl1]; exact qs1.slots,memT1,by rw [bi1]; exact qs1.bindings,
        by rw [ba1]; exact qs1.base,by rw [sc1]; exact qs1.scope⟩
  have cq2 : Cq SPB TPB (W+2) t1 := by
    have := Cb.step (w := 2) (p := 1) cq1 fr1 (by simp [NExpr.nodes] at wu1; omega)
      (by simp [NExpr.nodes] at pu1; omega) (by rw [liveEq]; omega) qu1
    exact this
  have fa2 : FA t1.frame L0 T0 scq N := fa.of_eq fr1
  have one : bl.valid 1 = true := by simp [Ty.valid]
  obtain ⟨t2,run2,fr2,sl2,sc2,me2,bi2,ba2,wl2,wu2,pl2,pu2,ql2,qu2,live2⟩ :=
    assign_good (.literal bl 1) 2 2 bl t1 1 1 ⟨P.length,true⟩ ⟨bl,0⟩ (by simp [NExpr.scalarOnly])
      (by simp [NExpr.denote,one]) (Ty.convert_of_valid _ _ one) (by simp [qs2.slots])
      (by simp [qs2.bindings,bind0]) (by simp [qs2.memory,lenP]) rfl (by simp [Ty.valid]) rfl
  have memT2 : t2.scalars.memory = P.set aa ⟨s64,vb⟩ ++ [⟨bl,1⟩] := by
    rw [me2]; simp [qs2.memory,lenP,List.set_append_right]
  have qs3 : QS t2 (P.set aa ⟨s64,vb⟩) B (sc+1) [⟨bl,1⟩] (bind0 aa ab ++ [⟨P.length,true⟩])
      (slots0 ++ [.scalar 2]) := ⟨by rw [sl2]; exact qs2.slots,memT2,by rw [bi2]; exact qs2.bindings,
        by rw [ba2]; exact qs2.base,by rw [sc2]; exact qs2.scope⟩
  have cq3 : Cq SPB TPB (W+4) t2 := by
    have := Cb.step (w := 2) (p := 1) cq2 fr2 (by simp [NExpr.nodes] at wu2; omega)
      (by simp [NExpr.nodes] at pu2; omega) (by rw [live1,liveEq]; omega) qu2
    exact this
  have fa3 : FA t2.frame L0 T0 scq N := fa2.of_eq fr2
  have hty : (P.set aa ⟨s64,vb⟩ ++ [(⟨bl,1⟩ : Cell)]).map Cell.type = (P ++ [(⟨bl,0⟩ : Cell)]).map Cell.type := by
    simp [List.map_append,map_type_set P aa va vb ha]
  obtain ⟨res,leaveEq,qsR,faR,cqR⟩ := leave_pack2 (outer := U) (inner := t2) qs qs3 hty fa3 hsc cq cq3 (by omega) hL
  apply RunsTo.seqSkip
  apply RunsTo.scopeSimple
  apply RunsTo.seq
  apply RunsTo.primitive run1
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seqSkip
  apply RunsTo.primitive run2
  exact ⟨rfl,rfl,rfl,rfl,res,leaveEq,rfl,rfl,rfl,rfl,qsR,faR,cqR.mono (by omega)⟩


-- `return <scalar local>;` as the last statement.
theorem ret_cell {P : List Cell} {B sc L0 T0 N scq SPB TPB W : Nat} {cells : List Cell}
    {binds : List CppState.Binding} {slots : List Location} (S : NState) (slot idx : Nat) (ty : Ty)
    (binding : CppState.Binding) (v : Int) (hs : slots[slot]? = some (.scalar idx)) (hb : binds[idx]? = some binding)
    (hm : (P ++ cells)[binding.address]? = some ⟨ty,v⟩) (valid : ty.valid v = true)
    (qs : QS S P B sc cells binds slots) (fa : FA S.frame L0 T0 scq N) (cq : Cq SPB TPB W S) (cap : liveS S+2 ≤ SPB) :
    RunsTo (.sequence (.primitive (.ret (.variable ty slot))) (.primitive .skip)) S fun step =>
      step.returned = some (.scalar v) ∧ step.breaking = false ∧ ∃ D, step.state = D.charge 1 0 ∧
        QS D P B sc cells binds slots ∧ FA D.frame L0 T0 scq N ∧ Cq SPB TPB (W+3) D := by
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have h4 : envOf S slot ty = some v := env_qs qs slot idx binding ty v hs hb hm valid
  obtain ⟨u,hu,good⟩ := scalar_eval (.variable ty slot) S v (by simp [NExpr.scalarOnly]) (by simp [NExpr.denote,h4])
  have self := release_self good.1.1
  have run : (NStmt.ret (.variable ty slot)).run S = some ⟨u.charge 1 0,some (.scalar v),false⟩ := by
    simp [NStmt.run,hu,self]
  have cqU : Cq SPB TPB (W+1) u := cq.good good (by simp [NExpr.nodes]; omega)
  apply RunsTo.sequence
  apply RunsTo.primitive run
  refine Or.inl ⟨Or.inl rfl,rfl,rfl,u,rfl,qs.core good.1,fa.of_eq (by simpa using good.1.1),?_⟩
  exact cqU.mono (by omega)


theorem ch_run {P : List Cell} {B sc L0 T0 N scq SPB TPB W : Nat} (i j : Nat) (aa ab : Nat) (va vb x y : Int)
    (hxy : (i = 0 ∧ j = 1 ∧ x = va ∧ y = vb) ∨ (i = 1 ∧ j = 0 ∧ x = vb ∧ y = va))
    (ha : P[aa]? = some ⟨s64,va⟩) (hb : P[ab]? = some ⟨s64,vb⟩) (vva : s64.valid va = true)
    (vvb : s64.valid vb = true) (S : NState) (qs : QS S P B sc [] (bind0 aa ab) slots0)
    (fa : FA S.frame L0 T0 scq N) (cq : Cq SPB TPB W S) (spb : P.length+3-B+3+40 ≤ SPB) (hsc : scq ≤ sc)
    (hL : L0 ≤ TPB) :
    RunsTo (chCmd i j) S fun step => step.returned = some (.scalar (if x < y then 1 else 0)) ∧
      step.breaking = false ∧ ∃ D, step.state = D.charge 1 0 ∧
      QS D (if x < y then P.set aa ⟨s64,vb⟩ else P) B sc [⟨bl,(if x < y then 1 else 0)⟩]
        (bind0 aa ab ++ [⟨P.length,true⟩]) (slots0 ++ [.scalar 2]) ∧
      FA D.frame L0 T0 scq N ∧ Cq SPB TPB (W+30) D := by
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have aaLt : aa < P.length := (List.getElem?_eq_some_iff.mp ha).1
  have abLt : ab < P.length := (List.getElem?_eq_some_iff.mp hb).1
  have live0 : liveS S = P.length-B+2 := by rw [qs.live_eq]; simp [bind0]
  obtain ⟨s1,run1,fr1,qs1,cq1⟩ := decl_changed (L0 := L0) (T0 := T0) (N := N) (scq := scq) S aa ab qs cq
    (by omega)
  have fa1 : FA s1.frame L0 T0 scq N := fa.of_eq fr1
  have live1 : liveS s1 = P.length+1-B+3 := by
    have := qs1.live_eq; simp [bind0] at this; omega
  have ea : envOf s1 0 s64 = some va :=
    env_qs qs1 0 0 ⟨aa,true⟩ s64 va (by simp [slots0]) (by simp [bind0]) (by simp [List.getElem?_append_left aaLt,ha]) vva
  have eb : envOf s1 1 s64 = some vb :=
    env_qs qs1 1 1 ⟨ab,false⟩ s64 vb (by simp [slots0]) (by simp [bind0]) (by simp [List.getElem?_append_left abLt,hb]) vvb
  have ex : envOf s1 i s64 = some x := by rcases hxy with ⟨h1,h2,h3,h4⟩ | ⟨h1,h2,h3,h4⟩ <;> subst h1 h2 h3 h4 <;> assumption
  have ey : envOf s1 j s64 = some y := by rcases hxy with ⟨h1,h2,h3,h4⟩ | ⟨h1,h2,h3,h4⟩ <;> subst h1 h2 h3 h4 <;> assumption
  have cv := denote_lt (envOf s1) i j s64 x y ex ey
  obtain ⟨u,hu,good⟩ := scalar_eval (condE i j) s1 _ (by simp [NExpr.scalarOnly]) cv
  have self := release_self good.1.1
  have qsU : QS (u.charge 1 0) P B sc [⟨bl,0⟩] (bind0 aa ab ++ [⟨P.length,true⟩]) (slots0 ++ [.scalar 2]) :=
    qs1.core (good.1.trans (core_charge u 1 0))
  have faU : FA (u.charge 1 0).frame L0 T0 scq N := fa1.of_eq (by simpa using good.1.1)
  have liveU : liveS (u.charge 1 0) = liveS s1 := liveS_core (good.1.trans (core_charge u 1 0))
  have cqU : Cq SPB TPB (W+2+4+1) (u.charge 1 0) := by
    have c1 := cq1.good good (by simp [NExpr.nodes]; omega)
    have c2 := c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; omega)
    exact c2.mono (by simp [NExpr.nodes])
  apply RunsTo.seq
  apply RunsTo.primitive run1
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seq
  by_cases c : x < y
  · have hv : (if x < y then (1 : Int) else 0) = 1 := by simp [c]
    apply RunsTo.branch (next := u) (value := if x < y then 1 else 0) hu
    rw [hv, if_neg (by decide), self]
    refine (yes_ref (u.charge 1 0) aa ab va vb ha hb vva vvb qsU faU cqU (by omega) hsc hL).mono ?_
    intro step ⟨nr,nb,qsE,faE,cqE⟩
    refine ⟨nr,nb,?_⟩
    simp only [c, if_true]
    have liveE : liveS step.state = P.length+1-B+3 := by
      have := qsE.live_eq; simp [bind0] at this; omega
    refine (ret_cell step.state 2 2 bl ⟨P.length,true⟩ 1 (by simp) (by simp [bind0]) (by simp [List.getElem?_append_right,
      List.length_set]) (by simp [Ty.valid]) qsE faE cqE (by omega)).mono ?_
    intro st ⟨h1,h2,D,h3,h4,h5,h6⟩
    exact ⟨h1,h2,D,h3,h4,h5,h6.mono (by omega)⟩
  · have hv : (if x < y then (1 : Int) else 0) = 0 := by simp [c]
    apply RunsTo.branch (next := u) (value := if x < y then 1 else 0) hu
    rw [hv, if_pos rfl, self]
    apply RunsTo.skip
    refine ⟨rfl,rfl,?_⟩
    simp only [c, if_false]
    have liveE : liveS (u.charge 1 0) = P.length+1-B+3 := by omega
    refine (ret_cell (u.charge 1 0) 2 2 bl ⟨P.length,true⟩ 0 (by simp) (by simp [bind0]) (by simp [qsU.memory])
      (by simp [Ty.valid]) qsU faU cqU (by omega)).mono ?_
    intro st ⟨h1,h2,D,h3,h4,h5,h6⟩
    exact ⟨h1,h2,D,h3,h4,h5,h6.mono (by omega)⟩

end Proofs.ExtremaRef
