import Proofs.QuotientSearch
import Proofs.Generated.Mod61

namespace Proofs.Mod61Body
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.FlatVectorStmt Proofs.QuotientFrame
open Proofs.QuotientSearch
open Proofs.CppState (Cell)

-- Scalar locals that are all `unsigned long long`: cells, bindings and slots by position.
def cm (l : List Int) : List Cell := l.map fun v => ⟨u64,v⟩
def bmd (P : List Cell) (n : Nat) (w : Nat → Bool) : List CppState.Binding :=
  (List.range n).map fun j => ⟨P.length+j,w j⟩
def ssl (n : Nat) : List Location := (List.range n).map fun j => .scalar j

theorem cm_append (l : List Int) (v : Int) : cm (l ++ [v]) = cm l ++ [⟨u64,v⟩] := by simp [cm]
theorem bmd_succ (P : List Cell) (n : Nat) (w : Nat → Bool) :
    bmd P (n+1) w = bmd P n w ++ [⟨P.length+n,w n⟩] := by simp [bmd,List.range_succ]
theorem ssl_succ (n : Nat) : ssl (n+1) = ssl n ++ [.scalar n] := by simp [ssl,List.range_succ]
theorem bmd_length (P : List Cell) (n : Nat) (w : Nat → Bool) : (bmd P n w).length = n := by simp [bmd]
theorem cm_length (l : List Int) : (cm l).length = l.length := by simp [cm]

theorem _root_.Proofs.QuotientFrame.QS.of_eq {S : NState} {P : List Cell} {B sc : Nat} {c c' : List Cell} {b b' : List CppState.Binding}
    {s s' : List Location} (qs : QS S P B sc c b s) (hc : c = c') (hb : b = b') (hs : s = s') :
    QS S P B sc c' b' s' := by subst hc hb hs; exact qs

theorem env_cm {S : NState} {P : List Cell} {B sc : Nat} {l : List Int} {w : Nat → Bool}
    (qs : QS S P B sc (cm l) (bmd P l.length w) (ssl l.length)) (idx : Nat) (v : Int)
    (hidx : idx < l.length) (hv : l[idx]? = some v) (valid : u64.valid v = true) :
    envOf S idx u64 = some v :=
  envOf_at S idx idx ⟨P.length+idx,w idx⟩ u64 v (by simp [qs.slots,ssl,hidx])
    (by simp [qs.bindings,bmd,hidx]) (by simp [qs.memory,cm,List.getElem?_append_right,hv]) valid

theorem decl_cm {P : List Cell} {B sc : Nat} {l : List Int} {w : Nat → Bool} {SPB TPB W : Nat} (S : NState)
    (e : NExpr) (writable : Bool) (v : Int) (hw : writable = w l.length) (hv : u64.valid v = true)
    (qs : QS S P B sc (cm l) (bmd P l.length w) (ssl l.length)) (cq : Cq SPB TPB W S)
    (cap : liveS S+e.nodes+1 ≤ SPB) (scalar : e.scalarOnly = true) (value : e.denote (envOf S) = some v) :
    ∃ t, (NStmt.declare u64 writable e).run S = some ⟨t,none,false⟩ ∧ t.frame = S.frame ∧
      QS t P B sc (cm (l ++ [v])) (bmd P (l.length+1) w) (ssl (l.length+1)) ∧ Cq SPB TPB (W+e.nodes+1) t := by
  obtain ⟨t,run,fr,qs',cq'⟩ := decl_step S e u64 writable v v qs cq cap scalar value (Ty.convert_of_valid _ _ hv)
  refine ⟨t,run,fr,qs'.of_eq ?_ ?_ ?_,cq'⟩
  · rw [cm_append]
  · rw [bmd_succ,cm_length,hw]
  · rw [ssl_succ,bmd_length]

abbrev xE : NExpr := .variable u64 0
abbrev mE : NExpr := .binary u64 .sub (.binary u64 .mul (.literal u64 1) (.literal u64 2305843009213693952))
  (.cast u64 (.literal i32 1))
abbrev xuE : NExpr := .binary u64 .shr (.variable u64 0) (.literal i32 61)
abbrev xdE : NExpr := .binary u64 .band (.variable u64 0) (.variable u64 1)
abbrev resE : NExpr := .binary u64 .add (.variable u64 2) (.variable u64 3)
abbrev geE : NExpr := .binary bl .ge (.variable u64 4) (.variable u64 1)
abbrev subE : NExpr := .binary u64 .sub (.variable u64 4) (.variable u64 1)

def M61 : Nat := 2^61-1

theorem mE_value (env : Nat → Ty → Option Int) : mE.denote env = some (M61 : Int) := by
  have a : u64.valid 1 = true := by simp [Ty.valid]
  have b : u64.valid 2305843009213693952 = true := by simp [Ty.valid]
  have c : i32.valid 1 = true := by simp [Ty.valid]
  have d : u64.valid 2305843009213693951 = true := by simp [Ty.valid]
  have e : u64.valid 2305843009213693952 = true := b
  have f : u64.valid (1 * 2305843009213693952) = true := by simpa using b
  have g : u64.valid (2305843009213693952 - 1) = true := by simpa using d
  simp [NExpr.denote,a,b,c,binaryValue,Ty.convert_of_valid _ _ a,Ty.convert_of_valid _ _ b,Ty.convert_of_valid _ _ f,
    Ty.convert_of_valid _ _ g,Ty.convert_of_valid _ _ d,M61]


theorem u64_lt (n : Nat) (h : n < 18446744073709551616) : u64.valid (n : Int) = true := u64_valid_nat n h

theorem xuE_value (env : Nat → Ty → Option Int) (x : Nat) (hx : x < 18446744073709551616)
    (h0 : env 0 u64 = some (x : Int)) : xuE.denote env = some ((x / 2^61 : Nat) : Int) := by
  have lit : i32.valid 61 = true := by simp [Ty.valid]
  have valid : u64.valid ((x / 2^61 : Nat) : Int) = true := u64_lt _ (by have := Nat.div_le_self x (2^61); omega)
  rw [den_binary,den_variable,h0]
  simp only [Option.bind_some,NExpr.denote,lit,if_true,binaryValue,Int.toNat_natCast,Nat.shiftRight_eq_div_pow]
  simpa using Ty.convert_of_valid _ _ valid

theorem xdE_value (env : Nat → Ty → Option Int) (x : Nat) (hx : x < 18446744073709551616)
    (h0 : env 0 u64 = some (x : Int)) (h1 : env 1 u64 = some (M61 : Int)) :
    xdE.denote env = some ((x % 2^61 : Nat) : Int) := by
  have valid : u64.valid ((x % 2^61 : Nat) : Int) = true := u64_lt _ (by have := Nat.mod_lt x (by decide : 0 < 2^61); omega)
  rw [den_binary,den_variable,den_variable,h0,h1]
  simp only [Option.bind_some,binaryValue,Int.toNat_natCast,M61,Nat.and_two_pow_sub_one_eq_mod]
  exact Ty.convert_of_valid _ _ valid

theorem resE_value (env : Nat → Ty → Option Int) (a b : Nat) (ha : a ≤ 7) (hb : b < 2^61)
    (h2 : env 2 u64 = some (a : Int)) (h3 : env 3 u64 = some (b : Int)) :
    resE.denote env = some ((a + b : Nat) : Int) := by
  have valid : u64.valid ((a + b : Nat) : Int) = true := u64_lt _ (by omega)
  rw [den_binary,den_variable,den_variable,h2,h3]
  simp only [Option.bind_some,binaryValue]
  have : ((a + b : Nat) : Int) = (a : Int) + (b : Int) := by omega
  rw [← this]
  exact Ty.convert_of_valid _ _ valid

theorem geE_value (env : Nat → Ty → Option Int) (r : Nat) (h4 : env 4 u64 = some (r : Int))
    (h1 : env 1 u64 = some (M61 : Int)) : geE.denote env = some (if M61 ≤ r then 1 else 0) := by
  rw [den_binary,den_variable,den_variable,h4,h1]
  simp only [Option.bind_some,binaryValue]
  by_cases c : M61 ≤ r
  · have : (r : Int) ≥ (M61 : Int) := by omega
    simp [this,c]
    exact Ty.convert_of_valid bl 1 (by simp [Ty.valid])
  · have : ¬ ((r : Int) ≥ (M61 : Int)) := by omega
    simp [this,c]
    exact Ty.convert_of_valid bl 0 (by simp [Ty.valid])

theorem subE_value (env : Nat → Ty → Option Int) (r : Nat) (h4 : env 4 u64 = some (r : Int))
    (h1 : env 1 u64 = some (M61 : Int)) (ge : M61 ≤ r) (hr : r < 2^64) :
    subE.denote env = some ((r - M61 : Nat) : Int) := by
  have valid : u64.valid ((r - M61 : Nat) : Int) = true := u64_lt _ (by omega)
  rw [den_binary,den_variable,den_variable,h4,h1]
  simp only [Option.bind_some,binaryValue]
  have : ((r - M61 : Nat) : Int) = (r : Int) - (M61 : Int) := by omega
  rw [← this]
  exact Ty.convert_of_valid _ _ valid


def wm (j : Nat) : Bool := decide (j ≠ 1)

abbrev declM : NStmt := .declare u64 false mE
abbrev declXu : NStmt := .declare u64 true xuE
abbrev declXd : NStmt := .declare u64 true xdE
abbrev declRes : NStmt := .declare u64 true resE
abbrev asgRes : NStmt := .assign 4 u64 subE
abbrev yesM : Command := .sequence (.scope (.sequence (.primitive asgRes) (.primitive .skip))) (.primitive .skip)
abbrev ifM : Command := .branch geE yesM (.primitive .skip)
abbrev mod61Cmd : Command :=
  .sequence (.primitive declM) (.sequence (.primitive declXu) (.sequence (.primitive declXd)
    (.sequence (.primitive declRes) (.sequence ifM (.sequence (.primitive (.ret (.variable u64 4))) (.primitive .skip))))))

theorem body_eq : Proofs.Mod61Instance.mod61.body = mod61Cmd := rfl

theorem live_cm {S : NState} {P : List Cell} {B sc : Nat} {l : List Int} {w : Nat → Bool}
    (qs : QS S P B sc (cm l) (bmd P l.length w) (ssl l.length)) :
    liveS S = P.length+l.length-B+l.length := by
  rw [qs.live_eq]; simp [cm_length,bmd_length]

-- `{ res = res - m; }` when the reduction is needed.
theorem yes_scope {P : List Cell} {B sc L0 T0 N scq SPB TPB W : Nat} (U : NState) (a c d : Int) (r : Nat)
    (hr : M61 ≤ r) (hr2 : r < 18446744073709551616) (va : u64.valid a = true)
    (qs : QS U P B sc (cm [a,(M61 : Int),c,d,(r : Int)]) (bmd P 5 wm) (ssl 5)) (fa : FA U.frame L0 T0 scq N)
    (cq : Cq SPB TPB W U) (cap : liveS U+8 ≤ SPB) (hsc : scq ≤ sc) (hL : L0 ≤ TPB) :
    RunsTo yesM U fun step => step.returned = none ∧ step.breaking = false ∧
      QS step.state P B sc (cm [a,(M61 : Int),c,d,((r - M61 : Nat) : Int)]) (bmd P 5 wm) (ssl 5) ∧
      FA step.state.frame L0 T0 scq N ∧ Cq SPB TPB (W+10) step.state := by
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have vM : u64.valid (M61 : Int) = true := u64_lt M61 (by unfold M61; omega)
  have vr : u64.valid (r : Int) = true := u64_lt r hr2
  have qs' := qs.enter
  have cq' := cq.enter
  have h4 := env_cm (l := [a,(M61 : Int),c,d,(r : Int)]) (w := wm) qs' 4 r (by simp) (by simp) vr
  have h1 := env_cm (l := [a,(M61 : Int),c,d,(r : Int)]) (w := wm) qs' 1 M61 (by simp) (by simp) vM
  have vs : u64.valid ((r - M61 : Nat) : Int) = true := u64_lt _ (by omega)
  have liveEq : liveS (scopeUp U) = liveS U := rfl
  obtain ⟨t,run,fr,qsT,cqT⟩ := assign_step (scopeUp U) subE 4 4 u64 ((r - M61 : Nat) : Int) ((r - M61 : Nat) : Int)
    ⟨P.length+4,true⟩ ⟨u64,(r : Int)⟩ qs' cq' (by rw [liveEq]; simp [NExpr.nodes]; omega)
    (by simp [NExpr.scalarOnly]) (subE_value _ r h4 h1 hr (by omega)) (Ty.convert_of_valid _ _ vs)
    (by simp [ssl]) (by simp [bmd,wm]) (by simp [cm,List.getElem?_append_right]) rfl vr (by simp)
    (cells' := cm [a,(M61 : Int),c,d,((r - M61 : Nat) : Int)])
    (by simp [cm,List.set_append_right])
  apply RunsTo.seqSkip
  apply RunsTo.scopeSimple
  apply RunsTo.seq
  apply RunsTo.primitive run
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.skip
  refine ⟨rfl,rfl,?_⟩
  have faT : FA t.frame L0 T0 scq N := fa.of_eq fr
  obtain ⟨res,leaveEq,qsR,faR,cqR⟩ := leave_pack (outer := U) (inner := t) (extra := []) (binds' := bmd P 5 wm)
    (slots' := ssl 5) qs (by simpa using qsT) (by simp [cm]) faT hsc cq cqT (by omega) hL
  exact ⟨res,leaveEq,rfl,rfl,rfl,rfl,qsR,faR,cqR.mono (by simp [NExpr.nodes])⟩

theorem res_final (x : Nat) (hx : x < 18446744073709551616) :
    (if M61 ≤ x / 2^61 + x % 2^61 then x / 2^61 + x % 2^61 - M61 else x / 2^61 + x % 2^61) = x % M61 := by
  unfold M61
  have h1 : x / 2^61 ≤ 7 := by omega
  have h2 : x % 2^61 < 2^61 := Nat.mod_lt x (by decide)
  have h3 : x = 2^61 * (x / 2^61) + x % 2^61 := (Nat.div_add_mod x (2^61)).symm
  by_cases c : 2^61-1 ≤ x / 2^61 + x % 2^61
  · rw [if_pos c]; omega
  · rw [if_neg c]; omega

abbrev retC : Command := .sequence (.primitive (.ret (.variable u64 4))) (.primitive .skip)

theorem ret_phase {P : List Cell} {B sc L0 T0 N scq SPB TPB W : Nat} {l : List Int} (S : NState) (r : Int)
    (hl : l.length = 5) (hr : l[4]? = some r) (vr : u64.valid r = true)
    (qs : QS S P B sc (cm l) (bmd P 5 wm) (ssl 5)) (fa : FA S.frame L0 T0 scq N)
    (cq : Cq SPB TPB W S) (cap : liveS S+2 ≤ SPB) :
    RunsTo retC S fun step => step.returned = some (.scalar r) ∧ step.breaking = false ∧
      ∃ D, step.state = D.charge 1 0 ∧ QS D P B sc (cm l) (bmd P 5 wm) (ssl 5) ∧ FA D.frame L0 T0 scq N ∧
        Cq SPB TPB (W+3) D := by
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have h4 : envOf S 4 u64 = some r := by
    have := env_cm (l := l) (w := wm) (S := S) (P := P) (B := B) (sc := sc) (by rw [hl]; exact qs) 4 r (by omega) hr vr
    exact this
  obtain ⟨u,hu,good⟩ := scalar_eval (.variable u64 4) S r (by simp [NExpr.scalarOnly]) (by simp [NExpr.denote,h4])
  have self := release_self good.1.1
  have run : (NStmt.ret (.variable u64 4)).run S = some ⟨u.charge 1 0,some (.scalar r),false⟩ := by
    simp [NStmt.run,hu,self]
  have coreU : Core S (u.charge 1 0) := good.1.trans (core_charge u 1 0)
  have cqU : Cq SPB TPB (W+1) u := cq.good good (by simp [NExpr.nodes]; omega)
  apply RunsTo.sequence
  apply RunsTo.primitive run
  refine Or.inl ⟨Or.inl rfl,rfl,rfl,u,rfl,qs.core good.1,fa.of_eq (by simpa using good.1.1),?_⟩
  exact cqU.mono (by omega)

theorem mod61_run {P : List Cell} {B sc L0 T0 N scq SPB TPB W : Nat} (S : NState) (x : Nat)
    (hx : x < 18446744073709551616)
    (qs : QS S P B sc (cm [(x : Int)]) (bmd P 1 wm) (ssl 1)) (fa : FA S.frame L0 T0 scq N)
    (cq : Cq SPB TPB W S) (spb : P.length+5-B+5+60 ≤ SPB) (hsc : scq ≤ sc) (hL : L0 ≤ TPB) :
    RunsTo mod61Cmd S fun step => step.returned = some (.scalar ((x % M61 : Nat) : Int)) ∧
      step.breaking = false ∧ ∃ D, step.state = D.charge 1 0 ∧
      QS D P B sc (cm [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int),((x % 2^61 : Nat) : Int),
        ((x % M61 : Nat) : Int)]) (bmd P 5 wm) (ssl 5) ∧ FA D.frame L0 T0 scq N ∧ Cq SPB TPB (W+100) D := by
  have vx : u64.valid (x : Int) = true := u64_lt x hx
  have vM : u64.valid (M61 : Int) = true := u64_lt M61 (by unfold M61; omega)
  have x0 := env_cm (l := [(x : Int)]) qs 0 x (by simp) (by simp) vx
  have live0 : liveS S = P.length+1-B+1 := by have := live_cm (l := [(x : Int)]) qs; simpa using this
  -- m
  obtain ⟨s1,run1,fr1,qs1,cq1⟩ := decl_cm S mE false (M61 : Int) (by simp [wm]) vM qs cq
    (by simp [NExpr.nodes]; omega) (by simp [NExpr.scalarOnly]) (mE_value _)
  have qs1' : QS s1 P B sc (cm [(x : Int),(M61 : Int)]) (bmd P 2 wm) (ssl 2) :=
    qs1.of_eq (by simp [cm]) (by simp) (by simp)
  have fa1 : FA s1.frame L0 T0 scq N := fa.of_eq fr1
  have live1 : liveS s1 = P.length+2-B+2 := by have := live_cm (l := [(x : Int),(M61 : Int)]) qs1'; simpa using this
  have cq1' : Cq SPB TPB (W+8) s1 := cq1.mono (by simp [NExpr.nodes])
  -- xu
  have e1 := env_cm (l := [(x : Int),(M61 : Int)]) qs1' 0 x (by simp) (by simp) vx
  obtain ⟨s2,run2,fr2,qs2,cq2⟩ := decl_cm s1 xuE true ((x / 2^61 : Nat) : Int) (by simp [wm])
    (u64_lt _ (by have := Nat.div_le_self x (2^61); omega)) qs1' cq1'
    (by simp [NExpr.nodes]; omega) (by simp [NExpr.scalarOnly]) (xuE_value _ x hx e1)
  have qs2' : QS s2 P B sc (cm [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int)]) (bmd P 3 wm) (ssl 3) :=
    qs2.of_eq (by simp [cm]) (by simp) (by simp)
  have fa2 : FA s2.frame L0 T0 scq N := fa1.of_eq fr2
  have live2 : liveS s2 = P.length+3-B+3 := by
    have := live_cm (l := [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int)]) qs2'; simpa using this
  have cq2' : Cq SPB TPB (W+16) s2 := cq2.mono (by simp [NExpr.nodes])
  -- xd
  have f0 := env_cm (l := [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int)]) qs2' 0 x (by simp) (by simp) vx
  have f1 := env_cm (l := [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int)]) qs2' 1 M61 (by simp) (by simp) vM
  obtain ⟨s3,run3,fr3,qs3,cq3⟩ := decl_cm s2 xdE true ((x % 2^61 : Nat) : Int) (by simp [wm])
    (u64_lt _ (by have := Nat.mod_lt x (by decide : 0 < 2^61); omega)) qs2' cq2'
    (by simp [NExpr.nodes]; omega) (by simp [NExpr.scalarOnly]) (xdE_value _ x hx f0 f1)
  have qs3' : QS s3 P B sc (cm [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int),((x % 2^61 : Nat) : Int)])
      (bmd P 4 wm) (ssl 4) := qs3.of_eq (by simp [cm]) (by simp) (by simp)
  have fa3 : FA s3.frame L0 T0 scq N := fa2.of_eq fr3
  have live3 : liveS s3 = P.length+4-B+4 := by
    have := live_cm (l := [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int),((x % 2^61 : Nat) : Int)]) qs3'
    simpa using this
  have cq3' : Cq SPB TPB (W+24) s3 := cq3.mono (by simp [NExpr.nodes])
  -- res
  have g2 := env_cm (l := [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int),((x % 2^61 : Nat) : Int)]) qs3' 2
    (x / 2^61 : Nat) (by simp) (by simp) (u64_lt _ (by have := Nat.div_le_self x (2^61); omega))
  have g3 := env_cm (l := [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int),((x % 2^61 : Nat) : Int)]) qs3' 3
    (x % 2^61 : Nat) (by simp) (by simp) (u64_lt _ (by have := Nat.mod_lt x (by decide : 0 < 2^61); omega))
  obtain ⟨s4,run4,fr4,qs4,cq4⟩ := decl_cm s3 resE true (((x / 2^61) + (x % 2^61) : Nat) : Int) (by simp [wm])
    (u64_lt _ (by have : x / 2^61 ≤ 7 := by omega
                  have := Nat.mod_lt x (by decide : 0 < 2^61); omega)) qs3' cq3'
    (by simp [NExpr.nodes]; omega) (by simp [NExpr.scalarOnly])
    (resE_value _ _ _ (by omega) (Nat.mod_lt x (by decide)) g2 g3)
  have rN : (x / 2^61) + (x % 2^61) < 18446744073709551616 := by
    have : x / 2^61 ≤ 7 := by omega
    have := Nat.mod_lt x (by decide : 0 < 2^61); omega
  have qs4' : QS s4 P B sc (cm [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int),((x % 2^61 : Nat) : Int),
      (((x / 2^61) + (x % 2^61) : Nat) : Int)]) (bmd P 5 wm) (ssl 5) := qs4.of_eq (by simp [cm]) (by simp) (by simp)
  have fa4 : FA s4.frame L0 T0 scq N := fa3.of_eq fr4
  have live4 : liveS s4 = P.length+5-B+5 := by
    have := live_cm (l := [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int),((x % 2^61 : Nat) : Int),
      (((x / 2^61) + (x % 2^61) : Nat) : Int)]) qs4'; simpa using this
  have cq4' : Cq SPB TPB (W+32) s4 := cq4.mono (by simp [NExpr.nodes])
  have k4 := env_cm (l := [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int),((x % 2^61 : Nat) : Int),
      (((x / 2^61) + (x % 2^61) : Nat) : Int)]) (w := wm) qs4' 4 (((x / 2^61) + (x % 2^61) : Nat) : Int) (by simp) (by simp)
    (u64_lt _ rN)
  have k1 := env_cm (l := [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int),((x % 2^61 : Nat) : Int),
      (((x / 2^61) + (x % 2^61) : Nat) : Int)]) (w := wm) qs4' 1 M61 (by simp) (by simp) vM
  obtain ⟨u,hu,good⟩ := scalar_eval geE s4 _ (by simp [NExpr.scalarOnly]) (geE_value _ _ k4 k1)
  have self := release_self good.1.1
  have eS : (fx SPB TPB).SPB = SPB := rfl
  have qsU : QS (u.charge 1 0) P B sc (cm [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int),((x % 2^61 : Nat) : Int),
      (((x / 2^61) + (x % 2^61) : Nat) : Int)]) (bmd P 5 wm) (ssl 5) :=
    qs4'.core (good.1.trans (core_charge u 1 0))
  have faU : FA (u.charge 1 0).frame L0 T0 scq N := fa4.of_eq (by simpa using good.1.1)
  have liveU : liveS (u.charge 1 0) = liveS s4 := liveS_core (good.1.trans (core_charge u 1 0))
  have cqU : Cq SPB TPB (W+32+4+1) (u.charge 1 0) := by
    have c1 := cq4'.good good (by simp [NExpr.nodes]; omega)
    have c2 := c1.good (Good.charge u 1 0) (by rw [liveS_core good.1]; omega)
    exact c2.mono (by simp [NExpr.nodes])
  apply RunsTo.seq
  apply RunsTo.primitive run1
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seq
  apply RunsTo.primitive run2
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seq
  apply RunsTo.primitive run3
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seq
  apply RunsTo.primitive run4
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seq
  have fin := res_final x hx
  by_cases c : M61 ≤ x / 2^61 + x % 2^61
  · have hv : (if M61 ≤ x / 2^61 + x % 2^61 then (1 : Int) else 0) = 1 := by simp [c]
    apply RunsTo.branch (next := u) (value := if M61 ≤ x / 2^61 + x % 2^61 then 1 else 0) hu
    rw [hv, if_neg (by decide), self]
    refine (yes_scope (u.charge 1 0) (x : Int) _ _ ((x / 2^61) + (x % 2^61)) c rN (u64_lt _ hx) qsU faU cqU
      (by omega) hsc hL).mono ?_
    intro step ⟨nr,nb,qsE,faE,cqE⟩
    refine ⟨nr,nb,?_⟩
    rw [if_pos c] at fin
    rw [fin] at qsE
    have liveE : liveS step.state = P.length+5-B+5 := by
      have := live_cm (l := [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int),((x % 2^61 : Nat) : Int),
        ((x % M61 : Nat) : Int)]) qsE; simpa using this
    refine (ret_phase step.state ((x % M61 : Nat) : Int) (l := [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int),
      ((x % 2^61 : Nat) : Int),((x % M61 : Nat) : Int)]) rfl (by simp) (u64_lt _ (by unfold M61; omega)) qsE faE cqE
      (by omega)).mono ?_
    intro st ⟨h1,h2,D,h3,h4,h5,h6⟩
    exact ⟨h1,h2,D,h3,h4,h5,h6.mono (by omega)⟩
  · have hv : (if M61 ≤ x / 2^61 + x % 2^61 then (1 : Int) else 0) = 0 := by simp [c]
    apply RunsTo.branch (next := u) (value := if M61 ≤ x / 2^61 + x % 2^61 then 1 else 0) hu
    rw [hv, if_pos rfl, self]
    apply RunsTo.skip
    refine ⟨rfl,rfl,?_⟩
    rw [if_neg c] at fin
    rw [fin] at qsU
    have liveE : liveS (u.charge 1 0) = P.length+5-B+5 := by
      have := live_cm (l := [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int),((x % 2^61 : Nat) : Int),
        ((x % M61 : Nat) : Int)]) qsU; simpa using this
    refine (ret_phase (u.charge 1 0) ((x % M61 : Nat) : Int) (l := [(x : Int),(M61 : Int),((x / 2^61 : Nat) : Int),
      ((x % 2^61 : Nat) : Int),((x % M61 : Nat) : Int)]) rfl (by simp) (u64_lt _ (by unfold M61; omega)) qsU faU cqU
      (by omega)).mono ?_
    intro st ⟨h1,h2,D,h3,h4,h5,h6⟩
    exact ⟨h1,h2,D,h3,h4,h5,h6.mono (by omega)⟩

end Proofs.Mod61Body
