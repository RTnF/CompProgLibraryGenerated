import Proofs.QuotientFrame
import Proofs.EnumerateQuotientsMath

namespace Proofs.QuotientSearch
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.FlatVectorStmt Proofs.QuotientFrame
open Proofs.CppState (Cell)



theorem tdiv_nat (a b : Nat) : (a : Int).tdiv (b : Int) = ((a / b : Nat) : Int) := by
  rw [Int.tdiv_eq_ediv]
  simp [Int.natCast_ediv]

theorem div_value (a b : Nat) (hb : 0 < b) (ha : a < 18446744073709551616) :
    checkedDivRem u64 false (a : Int) (b : Int) = some ((a / b : Nat) : Int) := by
  have hq : u64.valid ((a : Int).tdiv (b : Int)) = true := by
    rw [tdiv_nat]
    exact u64_valid_nat _ (by have := Nat.div_le_self a b; omega)
  rw [checkedDivRem_division_exact u64 _ _ (by omega) hq,tdiv_nat]

def qcell (v : Nat) : Cell := ⟨u64,(v : Int)⟩
def cellsQ3 (n hi lo : Nat) : List Cell := [qcell n,qcell hi,qcell lo]
def bindsQ3 (pl : Nat) : List CppState.Binding := [⟨pl,true⟩,⟨pl+1,true⟩,⟨pl+2,true⟩]
def slotsQ3 : List Location := [.scalar 0,.scalar 1,.scalar 2]
def cellsQ4 (n hi lo k : Nat) : List Cell := cellsQ3 n hi lo ++ [qcell k]
def bindsQ4 (pl : Nat) : List CppState.Binding := bindsQ3 pl ++ [⟨pl+3,false⟩]
def slotsQ4 : List Location := slotsQ3 ++ [.scalar 3]

theorem u64_nat (n : Nat) (h : n < 18446744073709551616) : u64.valid (n : Int) = true := u64_valid_nat n h

theorem envQ3 {S : NState} {P : List Cell} {B sc n hi lo : Nat}
    (qs : QS S P B sc (cellsQ3 n hi lo) (bindsQ3 P.length) slotsQ3)
    (hn : n < 18446744073709551616) (hhi : hi < 18446744073709551616) (hlo : lo < 18446744073709551616) :
    envOf S 0 u64 = some (n : Int) ∧ envOf S 1 u64 = some (hi : Int) ∧ envOf S 2 u64 = some (lo : Int) :=
  ⟨envOf_at S 0 0 ⟨P.length,true⟩ u64 n (by simp [qs.slots,slotsQ3]) (by simp [qs.bindings,bindsQ3])
      (by simp [qs.memory,cellsQ3,qcell]) (u64_nat n hn),
   envOf_at S 1 1 ⟨P.length+1,true⟩ u64 hi (by simp [qs.slots,slotsQ3]) (by simp [qs.bindings,bindsQ3])
      (by simp [qs.memory,cellsQ3,qcell]) (u64_nat hi hhi),
   envOf_at S 2 2 ⟨P.length+2,true⟩ u64 lo (by simp [qs.slots,slotsQ3]) (by simp [qs.bindings,bindsQ3])
      (by simp [qs.memory,cellsQ3,qcell]) (u64_nat lo hlo)⟩

theorem envQ4 {S : NState} {P : List Cell} {B sc n hi lo k : Nat}
    (qs : QS S P B sc (cellsQ4 n hi lo k) (bindsQ4 P.length) slotsQ4)
    (hn : n < 18446744073709551616) (hhi : hi < 18446744073709551616) (hlo : lo < 18446744073709551616)
    (hk : k < 18446744073709551616) :
    envOf S 0 u64 = some (n : Int) ∧ envOf S 1 u64 = some (hi : Int) ∧ envOf S 2 u64 = some (lo : Int) ∧
      envOf S 3 u64 = some (k : Int) :=
  ⟨envOf_at S 0 0 ⟨P.length,true⟩ u64 n (by simp [qs.slots,slotsQ4,slotsQ3]) (by simp [qs.bindings,bindsQ4,bindsQ3])
      (by simp [qs.memory,cellsQ4,cellsQ3,qcell]) (u64_nat n hn),
   envOf_at S 1 1 ⟨P.length+1,true⟩ u64 hi (by simp [qs.slots,slotsQ4,slotsQ3]) (by simp [qs.bindings,bindsQ4,bindsQ3])
      (by simp [qs.memory,cellsQ4,cellsQ3,qcell]) (u64_nat hi hhi),
   envOf_at S 2 2 ⟨P.length+2,true⟩ u64 lo (by simp [qs.slots,slotsQ4,slotsQ3]) (by simp [qs.bindings,bindsQ4,bindsQ3])
      (by simp [qs.memory,cellsQ4,cellsQ3,qcell]) (u64_nat lo hlo),
   envOf_at S 3 3 ⟨P.length+3,false⟩ u64 k (by simp [qs.slots,slotsQ4,slotsQ3]) (by simp [qs.bindings,bindsQ4,bindsQ3])
      (by simp [qs.memory,cellsQ4,cellsQ3,qcell]) (u64_nat k hk)⟩

def lit1 : NExpr := .cast u64 (.literal i32 1)
def lit2 : NExpr := .cast u64 (.literal i32 2)
abbrev condE : NExpr := .binary bl .gt (.binary u64 .sub (.variable u64 1) (.variable u64 2)) lit1
abbrev kE : NExpr := .divrem u64 false (.binary u64 .add (.variable u64 1) (.variable u64 2)) lit2
abbrev bcond : NExpr := .binary bl .ge (.binary u64 .mul (.variable u64 3)
  (.binary u64 .add (.variable u64 3) lit1)) (.variable u64 0)

theorem lit1_value (env : Nat → Ty → Option Int) : lit1.denote env = some 1 := by
  have a : i32.valid 1 = true := by simp [Ty.valid]
  have b : u64.valid 1 = true := by simp [Ty.valid]
  simp [lit1,NExpr.denote,a,Ty.convert_of_valid _ _ b]

theorem lit2_value (env : Nat → Ty → Option Int) : lit2.denote env = some 2 := by
  have a : i32.valid 2 = true := by simp [Ty.valid]
  have b : u64.valid 2 = true := by simp [Ty.valid]
  simp [lit2,NExpr.denote,a,Ty.convert_of_valid _ _ b]

theorem condE_value (env : Nat → Ty → Option Int) (hi lo : Nat) (h1 : env 1 u64 = some (hi : Int))
    (h2 : env 2 u64 = some (lo : Int)) (le : lo ≤ hi) (small : hi < 18446744073709551616) :
    condE.denote env = some (if 1 < hi - lo then 1 else 0) := by
  have v : u64.valid ((hi : Int) - (lo : Int)) = true := by
    have := u64_nat (hi - lo) (by omega)
    have e : ((hi - lo : Nat) : Int) = (hi : Int) - (lo : Int) := by omega
    rwa [e] at this
  simp only [NExpr.denote,h1,h2,Option.bind_some,lit1_value,binaryValue,Ty.convert_of_valid _ _ v]
  by_cases c : 1 < hi - lo
  · have : (hi : Int) - (lo : Int) > 1 := by omega
    simp [this,c,Ty.convert,bl]
  · have : ¬ ((hi : Int) - (lo : Int) > 1) := by omega
    simp [this,c,Ty.convert,bl]

theorem u64_add (a b : Nat) (h : a + b < 18446744073709551616) : u64.valid ((a : Int) + (b : Int)) = true := by
  simp [Ty.valid]; omega

theorem u64_mul (a b : Nat) (h : a * b < 18446744073709551616) : u64.valid ((a : Int) * (b : Int)) = true := by
  have e : ((a : Int) * (b : Int)) = ((a * b : Nat) : Int) := by omega
  rw [e]; exact u64_nat _ h

theorem den_divrem (env : Nat → Ty → Option Int) (ty : Ty) (rem : Bool) (l r : NExpr) :
    (NExpr.divrem ty rem l r).denote env =
      (l.denote env).bind fun a => (r.denote env).bind fun b => checkedDivRem ty rem a b := by
  simp [NExpr.denote]

theorem den_binary (env : Nat → Ty → Option Int) (ty : Ty) (op : Binary) (l r : NExpr) :
    (NExpr.binary ty op l r).denote env =
      (l.denote env).bind fun a => (r.denote env).bind fun b => ty.convert (binaryValue op a b) := by
  simp [NExpr.denote]

theorem den_variable (env : Nat → Ty → Option Int) (ty : Ty) (slot : Nat) :
    (NExpr.variable ty slot).denote env = env slot ty := by
  simp [NExpr.denote]

theorem kE_value (env : Nat → Ty → Option Int) (hi lo : Nat) (h1 : env 1 u64 = some (hi : Int))
    (h2 : env 2 u64 = some (lo : Int)) (small : hi+lo < 18446744073709551616) :
    kE.denote env = some (((hi+lo)/2 : Nat) : Int) := by
  have d := div_value (hi+lo) 2 (by omega) small
  have v := u64_add hi lo small
  have e : ((hi + lo : Nat) : Int) = (hi : Int) + (lo : Int) := by omega
  rw [e] at d
  have e2 : ((2 : Nat) : Int) = (2 : Int) := rfl
  rw [e2] at d
  unfold kE
  rw [den_divrem,den_binary,den_variable,den_variable,lit2_value,h1,h2]
  have c : u64.convert (binaryValue .add (hi : Int) (lo : Int)) = some ((hi : Int) + (lo : Int)) :=
    Ty.convert_of_valid _ _ v
  show (u64.convert (binaryValue .add (hi : Int) (lo : Int))).bind (fun a => checkedDivRem u64 false a 2) = _
  rw [c,Option.bind_some]
  exact d

theorem bcond_value (env : Nat → Ty → Option Int) (n k : Nat) (h3 : env 3 u64 = some (k : Int))
    (h0 : env 0 u64 = some (n : Int)) (small : k < 4294967296) :
    bcond.denote env = some (if n ≤ k*(k+1) then 1 else 0) := by
  have bound : k * (k+1) < 18446744073709551616 := by
    have h1 : k ≤ 4294967295 := by omega
    have h2 : k + 1 ≤ 4294967296 := by omega
    have := Nat.mul_le_mul h1 h2
    omega
  have e1 : ((k+1 : Nat) : Int) = (k : Int) + 1 := by omega
  have va : u64.valid ((k : Int) + 1) = true := by
    have := u64_nat (k+1) (by omega)
    rw [e1] at this
    exact this
  have vm : u64.valid ((k : Int) * ((k : Int) + 1)) = true := by
    have := u64_mul k (k+1) bound
    rw [e1] at this
    exact this
  have ca : u64.convert (binaryValue .add (k : Int) 1) = some ((k : Int) + 1) := Ty.convert_of_valid _ _ va
  have cm : u64.convert (binaryValue .mul (k : Int) ((k : Int) + 1)) = some ((k : Int) * ((k : Int) + 1)) :=
    Ty.convert_of_valid _ _ vm
  unfold bcond
  simp only [den_binary,den_variable,lit1_value,h3,h0,Option.bind_some]
  rw [ca,Option.bind_some,cm,Option.bind_some]
  have e : ((k * (k+1) : Nat) : Int) = (k : Int) * ((k : Int) + 1) := by
    rw [Int.natCast_mul, e1]
  by_cases c : n ≤ k*(k+1)
  · have : (k : Int) * ((k : Int) + 1) ≥ (n : Int) := by rw [← e]; omega
    have r : binaryValue .ge ((k : Int) * ((k : Int) + 1)) (n : Int) = 1 := by simp [binaryValue,this]
    rw [r,if_pos c]
    exact Ty.convert_of_valid bl 1 (by simp [Ty.valid])
  · have : ¬ ((k : Int) * ((k : Int) + 1) ≥ (n : Int)) := by rw [← e]; omega
    have r : binaryValue .ge ((k : Int) * ((k : Int) + 1)) (n : Int) = 0 := by simp [binaryValue,this]
    rw [r,if_neg c]
    exact Ty.convert_of_valid bl 0 (by simp [Ty.valid])

abbrev asg1 : NStmt := .assign 1 u64 (.variable u64 3)
abbrev asg2 : NStmt := .assign 2 u64 (.variable u64 3)
abbrev declK : NStmt := .declare u64 false kE

theorem var_scalar (ty : Ty) (slot : Nat) : (NExpr.variable ty slot).scalarOnly = true := by
  simp [NExpr.scalarOnly]

theorem kE_scalar : kE.scalarOnly = true := by simp [kE,lit2,NExpr.scalarOnly]
theorem bcond_scalar : bcond.scalarOnly = true := by simp [bcond,lit1,NExpr.scalarOnly]
theorem condE_scalar : condE.scalarOnly = true := by simp [condE,lit1,NExpr.scalarOnly]

theorem cells_set1 (P : List Cell) (n hi lo k k' : Nat) :
    (P ++ cellsQ4 n hi lo k).set (P.length+1) ⟨u64,(k' : Int)⟩ = P ++ cellsQ4 n k' lo k := by
  simp [cellsQ4,cellsQ3,qcell,List.set_append_right]

theorem cells_set2 (P : List Cell) (n hi lo k k' : Nat) :
    (P ++ cellsQ4 n hi lo k).set (P.length+2) ⟨u64,(k' : Int)⟩ = P ++ cellsQ4 n hi k' k := by
  simp [cellsQ4,cellsQ3,qcell,List.set_append_right]

-- `{ x = k; }` where `x` is an outer scalar and `k` is the loop-local midpoint.
theorem asg_scope {P : List Cell} {B sc n hi lo k : Nat} {cells' : List Cell} {L0 T0 N scq SPB TPB W : Nat}
    (S : NState) (slot idx : Nat) (binding : CppState.Binding) (cell : Cell)
    (qs : QS S P B sc (cellsQ4 n hi lo k) (bindsQ4 P.length) slotsQ4) (fa : FA S.frame L0 T0 scq N)
    (cq : Cq SPB TPB W S) (cap : liveS S+4 ≤ SPB) (hsc : scq ≤ sc) (hL : L0 ≤ TPB)
    (hn : n < 18446744073709551616) (hhi : hi < 18446744073709551616) (hlo : lo < 18446744073709551616)
    (hk : k < 18446744073709551616)
    (hs : slotsQ4[slot]? = some (.scalar idx)) (hb : (bindsQ4 P.length)[idx]? = some binding)
    (hm : (P ++ cellsQ4 n hi lo k)[binding.address]? = some cell) (ctype : cell.type = u64)
    (cvalid : u64.valid cell.value = true) (writable : binding.writable = true)
    (hcells : (P ++ cellsQ4 n hi lo k).set binding.address ⟨u64,(k : Int)⟩ = P ++ cells')
    (hty : cells'.map Cell.type = (cellsQ4 n hi lo k).map Cell.type) :
    RunsTo (.sequence (.scope (.sequence (.primitive (.assign slot u64 (.variable u64 3))) (.primitive .skip)))
        (.primitive .skip)) S fun step => step.returned = none ∧ step.breaking = false ∧
      QS step.state P B sc cells' (bindsQ4 P.length) slotsQ4 ∧ FA step.state.frame L0 T0 scq N ∧
      Cq SPB TPB (W+10) step.state := by
  have qs' : QS (scopeUp S) P B (sc+1) (cellsQ4 n hi lo k) (bindsQ4 P.length) slotsQ4 := qs.enter
  have cq' : Cq SPB TPB W (scopeUp S) := cq.enter
  have env := (envQ4 qs' hn hhi hlo hk).2.2.2
  obtain ⟨t,run,fr,qsT,cqT⟩ := assign_step (scopeUp S) (.variable u64 3) slot idx u64 (k : Int) (k : Int) binding cell
    qs' cq' (by simp [NExpr.nodes]; have : liveS (scopeUp S) = liveS S := rfl; omega) (var_scalar _ _)
    (by rw [den_variable]; exact env) (Ty.convert_of_valid _ _ (u64_nat k hk)) hs hb hm ctype cvalid writable hcells
  apply RunsTo.seqSkip
  apply RunsTo.scopeSimple
  apply RunsTo.seq
  apply RunsTo.primitive run
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.skip
  refine ⟨rfl,rfl,?_⟩
  have faT : FA t.frame L0 T0 scq N := fa.of_eq fr
  obtain ⟨r,leaveEq,qsR,faR,cqR⟩ := leave_pack (outer := S) (inner := t) (extra := []) (binds' := bindsQ4 P.length)
    (slots' := slotsQ4) qs (by simpa using qsT) hty faT hsc cq cqT (by omega) hL
  exact ⟨r,leaveEq,rfl,rfl,rfl,rfl,qsR,faR,cqR.mono (by simp [NExpr.nodes] <;> omega)⟩

abbrev yesC : Command := .sequence (.scope (.sequence (.primitive asg1) (.primitive .skip))) (.primitive .skip)
abbrev noC : Command := .sequence (.scope (.sequence (.primitive asg2) (.primitive .skip))) (.primitive .skip)
abbrev bsX : Command := .sequence (.primitive declK) (.sequence (.branch bcond yesC noC) (.primitive .skip))
abbrev bsBody : Command := .sequence (.scope bsX) (.primitive .skip)
abbrev bsWhile : Command := .whileLoop condE bsBody

theorem cellsQ4_of_decl (n hi lo k : Nat) (pl : Nat) :
    cellsQ3 n hi lo ++ [⟨u64,(k : Int)⟩] = cellsQ4 n hi lo k := rfl

theorem QS.to4 {S : NState} {P : List Cell} {B sc n hi lo k : Nat}
    (qs : QS S P B sc (cellsQ3 n hi lo ++ [⟨u64,(k : Int)⟩])
      (bindsQ3 P.length ++ [⟨P.length+(cellsQ3 n hi lo).length,false⟩])
      (slotsQ3 ++ [.scalar (bindsQ3 P.length).length])) :
    QS S P B sc (cellsQ4 n hi lo k) (bindsQ4 P.length) slotsQ4 := by
  have a : P.length+(cellsQ3 n hi lo).length = P.length+3 := by simp [cellsQ3]
  have b : (bindsQ3 P.length).length = 3 := by simp [bindsQ3]
  rw [a] at qs
  rw [b] at qs
  exact qs

theorem bs_body {P : List Cell} {B sc n hi lo L0 T0 N scq SPB TPB W : Nat} (S : NState)
    (qs : QS S P B sc (cellsQ3 n hi lo) (bindsQ3 P.length) slotsQ3) (fa : FA S.frame L0 T0 scq N)
    (cq : Cq SPB TPB W S) (hB : B ≤ P.length) (spb : P.length+12-B+40 ≤ SPB) (hsc : scq ≤ sc) (hL : L0 ≤ TPB)
    (hn : n < 18446744073709551616) (hhi : hi ≤ 4294967296) (hlo : lo < hi) :
    RunsTo bsBody S fun step => step.returned = none ∧ step.breaking = false ∧
      ∃ hi' lo', ((n ≤ ((hi+lo)/2)*(((hi+lo)/2)+1) ∧ hi' = (hi+lo)/2 ∧ lo' = lo) ∨
        (¬ n ≤ ((hi+lo)/2)*(((hi+lo)/2)+1) ∧ hi' = hi ∧ lo' = (hi+lo)/2)) ∧
      QS step.state P B sc (cellsQ3 n hi' lo') (bindsQ3 P.length) slotsQ3 ∧
      FA step.state.frame L0 T0 scq N ∧ Cq SPB TPB (W+60) step.state := by
  have liveS0 : liveS S = P.length+3-B+3 := by rw [qs.live_eq]; simp [cellsQ3,bindsQ3]
  have hk : (hi+lo)/2 < hi := by omega
  have hk32 : (hi+lo)/2 < 4294967296 := by omega
  apply RunsTo.seqSkip
  apply RunsTo.scopeSimple
  have qs' : QS (scopeUp S) P B (sc+1) (cellsQ3 n hi lo) (bindsQ3 P.length) slotsQ3 := qs.enter
  have cq' : Cq SPB TPB W (scopeUp S) := cq.enter
  have env3 := envQ3 qs' hn (by omega) (by omega)
  obtain ⟨tk,runK,frK,qsK0,cqK⟩ := decl_step (scopeUp S) kE u64 false (((hi+lo)/2 : Nat) : Int) (((hi+lo)/2 : Nat) : Int)
    qs' cq' (by simp [kE,lit2,NExpr.nodes]; have : liveS (scopeUp S) = liveS S := rfl; omega) kE_scalar
    (kE_value _ hi lo env3.2.1 env3.2.2 (by omega)) (Ty.convert_of_valid _ _ (u64_nat _ (by omega)))
  have qsK : QS tk P B (sc+1) (cellsQ4 n hi lo ((hi+lo)/2)) (bindsQ4 P.length) slotsQ4 := QS.to4 qsK0
  have liveK : liveS tk = P.length+4-B+4 := by rw [qsK.live_eq]; simp [cellsQ4,cellsQ3,bindsQ4,bindsQ3]
  have faK : FA tk.frame L0 T0 scq N := fa.of_eq frK
  apply RunsTo.seq
  apply RunsTo.primitive runK
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seqSkip
  have env4 := envQ4 qsK hn (by omega) (by omega) (by omega)
  have cv := bcond_value (envOf tk) n ((hi+lo)/2) env4.2.2.2 env4.1 hk32
  obtain ⟨u,hu,good⟩ := scalar_eval bcond tk _ bcond_scalar cv
  have self := release_self good.1.1
  have qsU : QS (u.charge 1 0) P B (sc+1) (cellsQ4 n hi lo ((hi+lo)/2)) (bindsQ4 P.length) slotsQ4 :=
    qsK.core (good.1.trans (core_charge u 1 0))
  have faU : FA (u.charge 1 0).frame L0 T0 scq N := faK.of_eq (by simpa using good.1.1)
  have liveU0 : liveS u = liveS tk := liveS_core good.1
  have cqU : Cq SPB TPB (W+7+8+1) (u.charge 1 0) := by
    have capB : liveS tk + bcond.nodes ≤ SPB := by simp [bcond,lit1,NExpr.nodes]; omega
    have c1 := cqK.good good capB
    have capC : liveS u + 0 ≤ SPB := by omega
    have c2 := c1.good (Good.charge u 1 0) capC
    exact c2.mono (by simp [kE,lit2,bcond,lit1,NExpr.nodes])
  have liveU : liveS (u.charge 1 0) = liveS tk := liveS_core (good.1.trans (core_charge u 1 0))
  -- the outer scope is left after the branch has finished
  have finish : ∀ (hi' lo' : Nat) (st : NState),
      ((n ≤ ((hi+lo)/2)*(((hi+lo)/2)+1) ∧ hi' = (hi+lo)/2 ∧ lo' = lo) ∨
        (¬ n ≤ ((hi+lo)/2)*(((hi+lo)/2)+1) ∧ hi' = hi ∧ lo' = (hi+lo)/2)) →
      QS st P B (sc+1) (cellsQ4 n hi' lo' ((hi+lo)/2)) (bindsQ4 P.length) slotsQ4 → FA st.frame L0 T0 scq N →
      Cq SPB TPB (W+7+8+1+10) st →
      ∃ r, S.leave st none = some r ∧ QS r P B sc (cellsQ3 n hi' lo') (bindsQ3 P.length) slotsQ3 ∧
        FA r.frame L0 T0 scq N ∧ Cq SPB TPB (W+7+8+1+10+1) r := by
    intro hi' lo' st cond qsE faE cqE
    exact leave_pack (outer := S) (inner := st) (extra := [qcell ((hi+lo)/2)]) (binds' := bindsQ4 P.length)
      (slots' := slotsQ4) qs qsE (by simp [cellsQ3,qcell]) faE hsc cq cqE (by omega) hL
  by_cases c : n ≤ ((hi+lo)/2)*(((hi+lo)/2)+1)
  · have hv : (if n ≤ ((hi+lo)/2)*(((hi+lo)/2)+1) then (1 : Int) else 0) = 1 := by simp [c]
    apply RunsTo.branch (next := u) (value := if n ≤ ((hi+lo)/2)*(((hi+lo)/2)+1) then 1 else 0) hu
    rw [hv]
    rw [if_neg (by decide)]
    rw [self]
    refine (asg_scope (u.charge 1 0) 1 1 ⟨P.length+1,true⟩ (qcell hi) qsU faU cqU (by omega) (by omega) hL hn (by omega)
      (by omega) (by omega) (by simp [slotsQ4,slotsQ3]) (by simp [bindsQ4,bindsQ3]) (by simp [cellsQ4,cellsQ3,qcell])
      rfl (u64_nat hi (by omega)) rfl (cells_set1 P n hi lo _ _) (by simp [cellsQ4,cellsQ3,qcell])).mono ?_
    intro step ⟨nr,nb,qsE,faE,cqE⟩
    obtain ⟨r,leaveEq,qsR,faR,cqR⟩ := finish ((hi+lo)/2) lo step.state (Or.inl ⟨c,rfl,rfl⟩) qsE faE cqE
    exact ⟨nr,nb,rfl,rfl,r,leaveEq,rfl,rfl,rfl,rfl,(hi+lo)/2,lo,Or.inl ⟨c,rfl,rfl⟩,qsR,faR,cqR.mono (by omega)⟩
  · have hv : (if n ≤ ((hi+lo)/2)*(((hi+lo)/2)+1) then (1 : Int) else 0) = 0 := by simp [c]
    apply RunsTo.branch (next := u) (value := if n ≤ ((hi+lo)/2)*(((hi+lo)/2)+1) then 1 else 0) hu
    rw [hv]
    rw [if_pos rfl]
    rw [self]
    refine (asg_scope (u.charge 1 0) 2 2 ⟨P.length+2,true⟩ (qcell lo) qsU faU cqU (by omega) (by omega) hL hn (by omega)
      (by omega) (by omega) (by simp [slotsQ4,slotsQ3]) (by simp [bindsQ4,bindsQ3]) (by simp [cellsQ4,cellsQ3,qcell])
      rfl (u64_nat lo (by omega)) rfl (cells_set2 P n hi lo _ _) (by simp [cellsQ4,cellsQ3,qcell])).mono ?_
    intro step ⟨nr,nb,qsE,faE,cqE⟩
    obtain ⟨r,leaveEq,qsR,faR,cqR⟩ := finish hi ((hi+lo)/2) step.state (Or.inr ⟨c,rfl,rfl⟩) qsE faE cqE
    exact ⟨nr,nb,rfl,rfl,r,leaveEq,rfl,rfl,rfl,rfl,hi,(hi+lo)/2,Or.inr ⟨c,rfl,rfl⟩,qsR,faR,cqR.mono (by omega)⟩

def BsInv (P : List Cell) (B sc n L0 T0 scq N SPB TPB W0 : Nat) (m : Nat) (S : NState) : Prop :=
  m ≤ 32 ∧ ∃ hi lo, hi - lo ≤ 2^m ∧ lo < hi ∧ hi ≤ 4294967296 ∧ n ≤ hi*(hi+1) ∧ (lo = 0 ∨ lo*(lo+1) < n) ∧
    QS S P B sc (cellsQ3 n hi lo) (bindsQ3 P.length) slotsQ3 ∧ FA S.frame L0 T0 scq N ∧
    Cq SPB TPB (W0+(32-m)*70) S

theorem bs_loop {P : List Cell} {B sc n L0 T0 N scq SPB TPB W0 : Nat} (S : NState) (m0 : Nat)
    (inv : BsInv P B sc n L0 T0 scq N SPB TPB W0 m0 S) (hB : B ≤ P.length) (spb : P.length+12-B+40 ≤ SPB)
    (hsc : scq ≤ sc) (hL : L0 ≤ TPB) (hn : n < 18446744073709551616) :
    RunsTo bsWhile S fun step => step.returned = none ∧ step.breaking = false ∧
      ∃ hi lo, hi = lo+1 ∧ hi ≤ 4294967296 ∧ n ≤ hi*(hi+1) ∧ (lo = 0 ∨ lo*(lo+1) < n) ∧
        QS step.state P B sc (cellsQ3 n hi lo) (bindsQ3 P.length) slotsQ3 ∧ FA step.state.frame L0 T0 scq N ∧
        Cq SPB TPB (W0+32*70+10) step.state := by
  refine RunsTo.whileGhost (BsInv P B sc n L0 T0 scq N SPB TPB W0) _ ?_ m0 m0 S (Nat.le_refl _) inv
  intro m t ⟨hm32,hi,lo,hd,hlo,hhi,hnn,hlow,qs,fa,cq⟩
  have liveT : liveS t = P.length+3-B+3 := by rw [qs.live_eq]; simp [cellsQ3,bindsQ3]
  have env3 := envQ3 qs hn (by omega) (by omega)
  have cv := condE_value (envOf t) hi lo env3.2.1 env3.2.2 (by omega) (by omega)
  obtain ⟨u,hu,good⟩ := scalar_eval condE t _ condE_scalar cv
  have self := release_self good.1.1
  have liveU : liveS u = liveS t := liveS_core good.1
  have qsU : QS (u.charge 1 0) P B sc (cellsQ3 n hi lo) (bindsQ3 P.length) slotsQ3 :=
    qs.core (good.1.trans (core_charge u 1 0))
  have faU : FA (u.charge 1 0).frame L0 T0 scq N := fa.of_eq (by simpa using good.1.1)
  have cqU : Cq SPB TPB (W0+(32-m)*70+7) (u.charge 1 0) := by
    have capB : liveS t + condE.nodes ≤ SPB := by simp [condE,lit1,NExpr.nodes]; omega
    have c1 := cq.good good capB
    have capC : liveS u + 0 ≤ SPB := by omega
    have c2 := c1.good (Good.charge u 1 0) capC
    exact c2.mono (by simp [condE,lit1,NExpr.nodes])
  refine ⟨u,_,hu,?_,?_⟩
  · intro zero
    have notGt : ¬ (1 < hi - lo) := by
      intro h; simp [h] at zero
    rw [self]
    refine ⟨rfl,rfl,hi,lo,by omega,hhi,hnn,hlow,qsU,faU,?_⟩
    exact cqU.mono (by have : 32 - m ≤ 32 := Nat.sub_le _ _; omega)
  · intro nonzero
    have gt : 1 < hi - lo := by
      by_cases h : 1 < hi - lo
      · exact h
      · simp [h] at nonzero
    rw [self]
    have mpos : 1 ≤ m := by
      by_cases h : m = 0
      · subst h; simp at hd; omega
      · omega
    have pow : 2^m = 2*2^(m-1) := by
      have : m = (m-1)+1 := by omega
      rw [this, Nat.pow_succ, Nat.mul_comm]; simp
    have body := bs_body (W := W0+(32-m)*70+7) (u.charge 1 0) qsU faU cqU hB spb hsc hL hn hhi hlo
    refine body.mono ?_
    intro step ⟨nr,nb,hi',lo',cond,qsE,faE,cqE⟩
    refine ⟨nr,nb,m-1,by omega,by omega,hi',lo',?_,?_,?_,?_,?_,qsE,faE,?_⟩
    · rcases cond with ⟨c,rfl,rfl⟩ | ⟨c,rfl,rfl⟩ <;> omega
    · rcases cond with ⟨c,rfl,rfl⟩ | ⟨c,rfl,rfl⟩ <;> omega
    · rcases cond with ⟨c,rfl,rfl⟩ | ⟨c,rfl,rfl⟩ <;> omega
    · rcases cond with ⟨c,rfl,rfl⟩ | ⟨c,rfl,rfl⟩
      · exact c
      · exact hnn
    · rcases cond with ⟨c,rfl,rfl⟩ | ⟨c,rfl,rfl⟩
      · exact hlow
      · right; omega
    · have : (32 - (m-1)) = (32 - m) + 1 := by omega
      rw [this]
      exact cqE.mono (by omega)

end Proofs.QuotientSearch
