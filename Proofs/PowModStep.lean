import Proofs.ScalarStraight

namespace Proofs.PowModStep
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppNestedCall
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.QuotientSearch Proofs.Mod61Body Proofs.StraightLine
open Proofs.CppState (Cell)

-- A scalar state whose cells are u64 values, all bindings writable.
def mk (P : List Cell) (vs : List Nat) : PS := ⟨P ++ cm (vs.map Nat.cast), bmd P vs.length fun _ => true⟩

theorem mk_mem (P : List Cell) (vs : List Nat) : (mk P vs).mem = P ++ cm (vs.map Nat.cast) := rfl
theorem mk_bs (P : List Cell) (vs : List Nat) : (mk P vs).bs = bmd P vs.length fun _ => true := rfl

theorem penv_mk (P : List Cell) (vs : List Nat) (hv : ∀ x ∈ vs, x < 18446744073709551616) (i : Nat) (hi : i < vs.length) :
    penv (mk P vs) i u64 = some ((vs[i] : Nat) : Int) := by
  have h1 : (bmd P vs.length fun _ => true)[i]? = some ⟨P.length+i,true⟩ := by simp [bmd,hi]
  have h2 : (P ++ cm (vs.map Nat.cast))[P.length+i]? = some ⟨u64,((vs[i] : Nat) : Int)⟩ := by
    rw [List.getElem?_append_right (by omega)]
    simp [cm,hi]
  have hx : u64.valid ((vs[i] : Nat) : Int) = true := u64_lt _ (hv _ (List.getElem_mem hi))
  unfold penv
  rw [show (mk P vs).bs = bmd P vs.length fun _ => true from rfl,
    show (mk P vs).mem = P ++ cm (vs.map Nat.cast) from rfl]
  simp only [h1,Bind.bind,Option.bind]
  rw [h2]
  simp [hx]

theorem rem_value (a b : Nat) (hb : 0 < b) (ha : a < 18446744073709551616) :
    checkedDivRem u64 true (a : Int) (b : Int) = some ((a % b : Nat) : Int) := by
  have hq : u64.valid ((a : Int).tdiv (b : Int)) = true := by
    rw [tdiv_nat]
    exact u64_valid_nat _ (by have := Nat.div_le_self a b; omega)
  have hr : u64.valid ((a : Int).tmod (b : Int)) = true := by
    have : (a : Int).tmod (b : Int) = ((a % b : Nat) : Int) := by
      rw [Int.tmod_eq_emod_of_nonneg (by omega)]; exact (Int.natCast_emod a b).symm
    rw [this]
    exact u64_valid_nat _ (by have := Nat.mod_le a b; omega)
  rw [checkedDivRem_remainder_exact u64 _ _ (by omega) hq hr]
  rw [Int.tmod_eq_emod_of_nonneg (by omega)]; exact congrArg some (Int.natCast_emod a b).symm

abbrev c0E : NExpr := .cast u64 (.literal i32 0)
abbrev c1E : NExpr := .cast u64 (.literal i32 1)
abbrev initR : NExpr := .divrem u64 true c1E (.variable u64 2)
abbrev initB : NExpr := .divrem u64 true (.variable u64 0) (.variable u64 2)
abbrev initE : NExpr := .variable u64 1
abbrev loopC : NExpr := .binary bl .ne (.variable u64 5) c0E
abbrev oddC : NExpr := .binary bl .ne (.binary u64 .band (.variable u64 5) c1E) c0E
abbrev mulE : NExpr := .divrem u64 true (.binary u64 .mul (.variable u64 3) (.variable u64 4)) (.variable u64 2)
abbrev sqE : NExpr := .divrem u64 true (.binary u64 .mul (.variable u64 4) (.variable u64 4)) (.variable u64 2)
abbrev shrE : NExpr := .binary u64 .shr (.variable u64 5) (.literal i32 1)

theorem c0_value (env : Nat → Ty → Option Int) : c0E.denote env = some 0 := by
  have a : i32.valid 0 = true := by simp [Ty.valid]
  have b : u64.valid 0 = true := by simp [Ty.valid]
  simp [NExpr.denote,a,Ty.convert_of_valid _ _ b]

theorem c1_value (env : Nat → Ty → Option Int) : c1E.denote env = some 1 := by
  have a : i32.valid 1 = true := by simp [Ty.valid]
  have b : u64.valid 1 = true := by simp [Ty.valid]
  simp [NExpr.denote,a,Ty.convert_of_valid _ _ b]

theorem initR_value (env : Nat → Ty → Option Int) (m : Nat) (hm : 0 < m) (hm' : m < 18446744073709551616)
    (h2 : env 2 u64 = some (m : Int)) : initR.denote env = some ((1 % m : Nat) : Int) := by
  rw [den_divrem,c1_value,den_variable,h2]
  have := rem_value 1 m hm (by omega)
  simpa using this

theorem initB_value (env : Nat → Ty → Option Int) (x m : Nat) (hm : 0 < m) (hx : x < 18446744073709551616)
    (h0 : env 0 u64 = some (x : Int)) (h2 : env 2 u64 = some (m : Int)) :
    initB.denote env = some ((x % m : Nat) : Int) := by
  rw [den_divrem,den_variable,den_variable,h0,h2]
  exact rem_value x m hm hx

theorem initE_value (env : Nat → Ty → Option Int) (x : Nat) (h1 : env 1 u64 = some (x : Int)) :
    initE.denote env = some (x : Int) := by
  rw [den_variable,h1]

theorem loopC_value (env : Nat → Ty → Option Int) (e : Nat) (h5 : env 5 u64 = some (e : Int)) :
    loopC.denote env = some (if e = 0 then 0 else 1) := by
  rw [den_binary,den_variable,h5,c0_value]
  simp only [Option.bind_some,binaryValue]
  by_cases z : e = 0
  · subst z; simpa using Ty.convert_of_valid bl 0 (by simp [Ty.valid])
  · have : ((e : Int) != 0) = true := by simp [z]
    simp only [this,if_true,z,if_false]
    exact Ty.convert_of_valid bl 1 (by simp [Ty.valid])

theorem oddC_value (env : Nat → Ty → Option Int) (e : Nat) (he : e < 18446744073709551616)
    (h5 : env 5 u64 = some (e : Int)) : oddC.denote env = some (if e % 2 = 0 then 0 else 1) := by
  have v : u64.valid ((e % 2 : Nat) : Int) = true := u64_lt _ (by have := Nat.mod_le e 2; omega)
  rw [den_binary,den_binary,den_variable,h5,c1_value,c0_value]
  simp only [Option.bind_some,binaryValue,Int.toNat_natCast]
  have hb : (1 : Int).toNat = 1 := rfl
  simp only [hb,Nat.and_one_is_mod]
  rw [Ty.convert_of_valid _ _ (by simpa using v)]
  simp only [Option.bind_some]
  rcases Nat.mod_two_eq_zero_or_one e with z | z
  · rw [z]; simpa [binaryValue] using Ty.convert_of_valid bl 0 (by simp [Ty.valid])
  · rw [z]; simpa [binaryValue] using Ty.convert_of_valid bl 1 (by simp [Ty.valid])

theorem mulE_value (env : Nat → Ty → Option Int) (r b m : Nat) (hr : r < m) (hb : b < m) (hm : m ≤ 4294967296)
    (h3 : env 3 u64 = some (r : Int)) (h4 : env 4 u64 = some (b : Int)) (h2 : env 2 u64 = some (m : Int)) :
    mulE.denote env = some ((r * b % m : Nat) : Int) := by
  have hp : r * b < 18446744073709551616 := by
    have : r * b < m * m := Nat.mul_lt_mul'' hr hb
    have : m * m ≤ 4294967296 * 4294967296 := Nat.mul_le_mul hm hm
    omega
  rw [den_divrem,den_binary,den_variable,den_variable,den_variable,h3,h4,h2]
  simp only [Option.bind_some,binaryValue]
  have e1 : (r : Int) * (b : Int) = ((r * b : Nat) : Int) := by omega
  rw [e1,Ty.convert_of_valid _ _ (u64_lt _ hp)]
  simp only [Option.bind_some]
  exact rem_value (r * b) m (by omega) hp

theorem sqE_value (env : Nat → Ty → Option Int) (b m : Nat) (hb : b < m) (hm : m ≤ 4294967296)
    (h4 : env 4 u64 = some (b : Int)) (h2 : env 2 u64 = some (m : Int)) :
    sqE.denote env = some ((b * b % m : Nat) : Int) := by
  have hp : b * b < 18446744073709551616 := by
    have : b * b < m * m := Nat.mul_lt_mul'' hb hb
    have : m * m ≤ 4294967296 * 4294967296 := Nat.mul_le_mul hm hm
    omega
  rw [den_divrem,den_binary]
  simp only [den_variable,h4,h2]
  simp only [Option.bind_some,binaryValue]
  have e1 : (b : Int) * (b : Int) = ((b * b : Nat) : Int) := by omega
  rw [e1,Ty.convert_of_valid _ _ (u64_lt _ hp)]
  simp only [Option.bind_some]
  exact rem_value (b * b) m (by omega) hp

theorem shrE_value (env : Nat → Ty → Option Int) (e : Nat) (he : e < 18446744073709551616)
    (h5 : env 5 u64 = some (e : Int)) : shrE.denote env = some ((e / 2 : Nat) : Int) := by
  have v : u64.valid ((e / 2 : Nat) : Int) = true := u64_lt _ (by have := Nat.div_le_self e 2; omega)
  have lit : i32.valid 1 = true := by simp [Ty.valid]
  rw [den_binary,den_variable,h5]
  simp only [Option.bind_some,NExpr.denote,lit,if_true,binaryValue,Int.toNat_natCast,Nat.shiftRight_eq_div_pow]
  simpa using Ty.convert_of_valid _ _ v

theorem mk_size (P : List Cell) (vs : List Nat) : (mk P vs).mem.length+(mk P vs).bs.length = P.length+2*vs.length := by
  simp [mk,cm,bmd]; omega

theorem mk_decl (P : List Cell) (vs : List Nat) (e : NExpr) (x : Nat) (hx : x < 18446744073709551616)
    (h : e.denote (penv (mk P vs)) = some (x : Int)) :
    pstmt (.declare u64 true e) (mk P vs) =
      some ⟨mk P (vs ++ [x]),none,e.nodes+1,P.length+2*vs.length+e.nodes+4⟩ := by
  have hs := mk_size P vs
  have hconv := Ty.convert_of_valid u64 (x : Int) (u64_lt _ hx)
  have hmem : (mk P vs).mem ++ [⟨u64,(x : Int)⟩] = (mk P (vs ++ [x])).mem := by
    simp [mk,cm]
  have hbs : (mk P vs).bs ++ [⟨(mk P vs).mem.length,true⟩] = (mk P (vs ++ [x])).bs := by
    simp only [mk_bs,bmd_succ,List.length_append,List.length_singleton]
    simp [mk,cm,bmd]
  simp only [pstmt,h,hconv,Bind.bind,Option.bind,hmem,hbs]
  have : (mk P vs).mem.length+(mk P vs).bs.length+e.nodes+4 = P.length+2*vs.length+e.nodes+4 := by omega
  rw [this]

theorem mk_assign (P : List Cell) (vs : List Nat) (slot : Nat) (hslot : slot < vs.length) (e : NExpr) (x : Nat)
    (hx : x < 18446744073709551616) (hvs : ∀ y ∈ vs, y < 18446744073709551616)
    (h : e.denote (penv (mk P vs)) = some (x : Int)) :
    pstmt (.assign slot u64 e) (mk P vs) =
      some ⟨mk P (vs.set slot x),none,e.nodes+1,P.length+2*vs.length+e.nodes+2⟩ := by
  have hs := mk_size P vs
  have hconv := Ty.convert_of_valid u64 (x : Int) (u64_lt _ hx)
  have h1 : (mk P vs).bs[slot]? = some ⟨P.length+slot,true⟩ := by simp [mk,bmd,hslot]
  have h2 : (mk P vs).mem[P.length+slot]? = some ⟨u64,((vs[slot] : Nat) : Int)⟩ := by
    simp only [mk_mem]
    rw [List.getElem?_append_right (by omega)]
    simp [cm,hslot]
  have hv : u64.valid ((vs[slot] : Nat) : Int) = true := u64_lt _ (hvs _ (List.getElem_mem hslot))
  have hset : (mk P vs).mem.set (P.length+slot) ⟨u64,(x : Int)⟩ = (mk P (vs.set slot x)).mem := by
    simp only [mk_mem]
    rw [List.set_append_right _ _ (by omega)]
    simp [cm,List.map_set]
  have hbs : (mk P vs).bs = (mk P (vs.set slot x)).bs := by simp [mk]
  simp only [pstmt,h,h1,h2,hv,hconv,Bind.bind,Option.bind]
  simp only [and_self,if_true,hset,hbs]
  have hm : (mk P vs).mem.length = P.length + vs.length := by simp [mk,cm]
  have hb : (mk P (vs.set slot x)).bs.length = vs.length := by simp [mk,bmd]
  have : P.length+vs.length+vs.length+e.nodes+2 = P.length+2*vs.length+e.nodes+2 := by omega
  rw [hm,hb,this]

def sv (base exp m r b e : Nat) : List Nat := [base,exp,m,r,b,e]

structure Ok (base exp m r b e : Nat) : Prop where
  base_lt : base < 18446744073709551616
  exp_lt : exp < 18446744073709551616
  m_pos : 0 < m
  m_le : m ≤ 4294967296
  r_lt : r < m
  b_lt : b < m
  e_lt : e < 18446744073709551616

theorem Ok.vs {base exp m r b e : Nat} (h : Ok base exp m r b e) : ∀ y ∈ sv base exp m r b e, y < 18446744073709551616 := by
  have := h.base_lt; have := h.exp_lt; have := h.m_le; have := h.r_lt; have := h.b_lt; have := h.e_lt
  intro y hy
  simp [sv] at hy
  omega

theorem env_sv (P : List Cell) {base exp m r b e : Nat} (h : Ok base exp m r b e) :
    penv (mk P (sv base exp m r b e)) 0 u64 = some (base : Int) ∧
    penv (mk P (sv base exp m r b e)) 1 u64 = some (exp : Int) ∧
    penv (mk P (sv base exp m r b e)) 2 u64 = some (m : Int) ∧
    penv (mk P (sv base exp m r b e)) 3 u64 = some (r : Int) ∧
    penv (mk P (sv base exp m r b e)) 4 u64 = some (b : Int) ∧
    penv (mk P (sv base exp m r b e)) 5 u64 = some (e : Int) := by
  have hv := h.vs
  have k : ∀ i (hi : i < 6), penv (mk P (sv base exp m r b e)) i u64 = some (((sv base exp m r b e)[i]'(by simpa [sv] using hi) : Nat) : Int) :=
    fun i hi => penv_mk P (sv base exp m r b e) hv i (by simpa [sv] using hi)
  exact ⟨k 0 (by decide),k 1 (by decide),k 2 (by decide),k 3 (by decide),k 4 (by decide),k 5 (by decide)⟩

theorem st_A3 (P : List Cell) {base exp m r b e : Nat} (h : Ok base exp m r b e) :
    pstmt (.assign 3 u64 mulE) (mk P (sv base exp m r b e)) =
      some ⟨mk P (sv base exp m (r*b%m) b e),none,mulE.nodes+1,P.length+12+mulE.nodes+2⟩ := by
  obtain ⟨_,_,e2,e3,e4,_⟩ := env_sv P h
  have hd := mulE_value (penv (mk P (sv base exp m r b e))) r b m h.r_lt h.b_lt h.m_le e3 e4 e2
  have hx : r*b%m < 18446744073709551616 := by
    have := Nat.mod_lt (r*b) h.m_pos; have := h.m_le; omega
  have := mk_assign P (sv base exp m r b e) 3 (by simp [sv]) mulE (r*b%m) hx h.vs hd
  simpa [sv] using this

theorem st_A4 (P : List Cell) {base exp m r b e : Nat} (h : Ok base exp m r b e) :
    pstmt (.assign 4 u64 sqE) (mk P (sv base exp m r b e)) =
      some ⟨mk P (sv base exp m r (b*b%m) e),none,sqE.nodes+1,P.length+12+sqE.nodes+2⟩ := by
  obtain ⟨_,_,e2,_,e4,_⟩ := env_sv P h
  have hd := sqE_value (penv (mk P (sv base exp m r b e))) b m h.b_lt h.m_le e4 e2
  have hx : b*b%m < 18446744073709551616 := by
    have := Nat.mod_lt (b*b) h.m_pos; have := h.m_le; omega
  have := mk_assign P (sv base exp m r b e) 4 (by simp [sv]) sqE (b*b%m) hx h.vs hd
  simpa [sv] using this

theorem st_A5 (P : List Cell) {base exp m r b e : Nat} (h : Ok base exp m r b e) :
    pstmt (.assign 5 u64 shrE) (mk P (sv base exp m r b e)) =
      some ⟨mk P (sv base exp m r b (e/2)),none,shrE.nodes+1,P.length+12+shrE.nodes+2⟩ := by
  obtain ⟨_,_,_,_,_,e5⟩ := env_sv P h
  have hd := shrE_value (penv (mk P (sv base exp m r b e))) e h.e_lt e5
  have hx : e/2 < 18446744073709551616 := by have := Nat.div_le_self e 2; have := h.e_lt; omega
  have := mk_assign P (sv base exp m r b e) 5 (by simp [sv]) shrE (e/2) hx h.vs hd
  simpa [sv] using this

abbrev A3 : NStmt := .assign 3 u64 mulE
abbrev A4 : NStmt := .assign 4 u64 sqE
abbrev A5 : NStmt := .assign 5 u64 shrE
abbrev Sk : Command := .primitive .skip
abbrev IfOdd : Command := .branch oddC (.sequence (.scope (.sequence (.primitive A3) Sk)) Sk) Sk
abbrev LBody : Command := .sequence (.scope (.sequence IfOdd (.sequence (.primitive A4) (.sequence (.primitive A5) Sk)))) Sk
abbrev LoopCmd : Command := .whileLoop loopC LBody

theorem pstmt_skip (ps : PS) : pstmt .skip ps = some ⟨ps,none,0,ps.mem.length+ps.bs.length⟩ := rfl

theorem Ok.setR {base exp m r b e : Nat} (h : Ok base exp m r b e) (r' : Nat) (hr : r' < m) : Ok base exp m r' b e :=
  ⟨h.base_lt,h.exp_lt,h.m_pos,h.m_le,hr,h.b_lt,h.e_lt⟩
theorem Ok.setB {base exp m r b e : Nat} (h : Ok base exp m r b e) (b' : Nat) (hb : b' < m) : Ok base exp m r b' e :=
  ⟨h.base_lt,h.exp_lt,h.m_pos,h.m_le,h.r_lt,hb,h.e_lt⟩
theorem Ok.setE {base exp m r b e : Nat} (h : Ok base exp m r b e) (e' : Nat) (he : e' < 18446744073709551616) : Ok base exp m r b e' :=
  ⟨h.base_lt,h.exp_lt,h.m_pos,h.m_le,h.r_lt,h.b_lt,he⟩

theorem take_sv_mem (P : List Cell) (a b c r d e r' d' e' : Nat) :
    (mk P (sv a b c r' d' e')).mem.take (mk P (sv a b c r d e)).mem.length = (mk P (sv a b c r' d' e')).mem := by
  apply List.take_of_length_le
  simp [mk,cm,sv]

theorem take_sv_bs (P : List Cell) (a b c r d e r' d' e' : Nat) :
    (mk P (sv a b c r' d' e')).bs.take (mk P (sv a b c r d e)).bs.length = (mk P (sv a b c r' d' e')).bs := by
  apply List.take_of_length_le
  simp [mk,bmd,sv]

theorem iter_even (P : List Cell) {base exp m r b e : Nat} (h : Ok base exp m r b e) (z : e % 2 = 0) (fu : Nat) :
    ∃ r1, pexec fu LBody (mk P (sv base exp m r b e)) = some r1 ∧
      r1.ps = mk P (sv base exp m r (b*b%m) (e/2)) ∧ r1.ret = none ∧ r1.cost ≤ 40 ∧ r1.need ≤ P.length+12+40 := by
  obtain ⟨_,_,_,_,_,e5⟩ := env_sv P h
  have hc := oddC_value (penv (mk P (sv base exp m r b e))) e h.e_lt e5
  rw [z] at hc
  have hb' : b*b%m < m := Nat.mod_lt _ h.m_pos
  have h4 := h.setB _ hb'
  have h5 := h4.setE (e/2) (by have := Nat.div_le_self e 2; have := h.e_lt; omega)
  have a4 := st_A4 P h
  have a5 := st_A5 P h4
  simp only [pexec,Bind.bind,Option.bind,hc,if_true,pstmt_skip,a4,a5,mk_size,take_sv_mem,take_sv_bs]
  refine ⟨_,rfl,rfl,rfl,?_,?_⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes,sv]

theorem mk_eta (P : List Cell) (vs : List Nat) : (⟨(mk P vs).mem,(mk P vs).bs⟩ : PS) = mk P vs := rfl
theorem int_one_ne : ¬ ((1 : Int) = 0) := by decide

theorem iter_odd (P : List Cell) {base exp m r b e : Nat} (h : Ok base exp m r b e) (z : e % 2 = 1) (fu : Nat) :
    ∃ r1, pexec fu LBody (mk P (sv base exp m r b e)) = some r1 ∧
      r1.ps = mk P (sv base exp m (r*b%m) (b*b%m) (e/2)) ∧ r1.ret = none ∧ r1.cost ≤ 40 ∧ r1.need ≤ P.length+12+40 := by
  obtain ⟨_,_,_,_,_,e5⟩ := env_sv P h
  have hc := oddC_value (penv (mk P (sv base exp m r b e))) e h.e_lt e5
  rw [z] at hc
  have hc' : oddC.denote (penv (mk P (sv base exp m r b e))) = some 1 := by simpa using hc
  have hb' : b*b%m < m := Nat.mod_lt _ h.m_pos
  have hr' : r*b%m < m := Nat.mod_lt _ h.m_pos
  have h3 := h.setR _ hr'
  have h4 := h3.setB _ hb'
  have a3 := st_A3 P h
  have a4 := st_A4 P h3
  have a5 := st_A5 P h4
  simp only [pexec,Bind.bind,Option.bind,hc',pstmt_skip,a3,a4,a5,mk_size,List.take_length,take_sv_mem,take_sv_bs,int_one_ne,if_false,ite_false,mk_eta]
  refine ⟨_,rfl,rfl,rfl,?_,?_⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes,sv]

theorem iter (P : List Cell) {base exp m r b e : Nat} (h : Ok base exp m r b e) (fu : Nat) :
    ∃ r1, pexec fu LBody (mk P (sv base exp m r b e)) = some r1 ∧
      r1.ps = mk P (sv base exp m (if e % 2 = 0 then r else r*b%m) (b*b%m) (e/2)) ∧ r1.ret = none ∧
      r1.cost ≤ 40 ∧ r1.need ≤ P.length+12+40 := by
  rcases Nat.mod_two_eq_zero_or_one e with z | z
  · simpa [z] using iter_even P h z fu
  · have : ¬ e % 2 = 0 := by omega
    simpa [this] using iter_odd P h z fu

def pw (m : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, r, _, _ => r
  | n+1, r, b, e => if e = 0 then r else pw m n (if e % 2 = 0 then r else r*b%m) (b*b%m) (e/2)

theorem pow_sq (b k : Nat) : b^(2*k) = (b*b)^k := by rw [Nat.pow_mul, Nat.pow_two]

theorem mod_pow_sq (r b m k : Nat) : r * (b*b%m)^k % m = r * (b*b)^k % m := by
  have h1 : (b*b%m)^k % m = (b*b)^k % m := (Nat.pow_mod (b*b) k m).symm
  rw [Nat.mul_mod, h1]
  exact (Nat.mul_mod r _ m).symm

theorem mod_pow_sq_odd (r b m k : Nat) : (r*b%m) * (b*b%m)^k % m = r * b * (b*b)^k % m := by
  have h1 : (b*b%m)^k % m = (b*b)^k % m := (Nat.pow_mod (b*b) k m).symm
  rw [Nat.mul_mod, h1, Nat.mod_mod]
  exact (Nat.mul_mod (r*b) _ m).symm

theorem pw_spec (m : Nat) (hm : 0 < m) : ∀ (n r b e : Nat), e < 2^n → r < m → pw m n r b e = r * b^e % m := by
  intro n
  induction n with
  | zero =>
    intro r b e he hr
    have : e = 0 := by simpa using he
    subst this
    simp [pw, Nat.mod_eq_of_lt hr]
  | succ n ih =>
    intro r b e he hr
    by_cases z : e = 0
    · subst z; simp [pw, Nat.mod_eq_of_lt hr]
    · have hz : e / 2 < 2^n := by rw [Nat.pow_succ] at he; omega
      have hb : b*b%m < m := Nat.mod_lt _ hm
      rcases Nat.mod_two_eq_zero_or_one e with ev | od
      · have hr' : (if e % 2 = 0 then r else r*b%m) = r := by simp [ev]
        simp only [pw, z, ite_false, hr']
        rw [ih r (b*b%m) (e/2) hz hr, mod_pow_sq]
        have hp : b^e = (b*b)^(e/2) := by rw [← pow_sq]; congr 1; omega
        rw [hp]
      · have hr' : (if e % 2 = 0 then r else r*b%m) = r*b%m := by simp [od]
        simp only [pw, z, ite_false, hr']
        rw [ih (r*b%m) (b*b%m) (e/2) hz (Nat.mod_lt _ hm), mod_pow_sq_odd]
        have hp : b^e = (b*b)^(e/2) * b := by rw [← pow_sq, ← Nat.pow_succ]; congr 1; omega
        rw [hp]
        simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]


theorem Ok.next {base exp m r b e : Nat} (h : Ok base exp m r b e) :
    Ok base exp m (if e % 2 = 0 then r else r*b%m) (b*b%m) (e/2) := by
  have hb : b*b%m < m := Nat.mod_lt _ h.m_pos
  have hr : (if e % 2 = 0 then r else r*b%m) < m := by
    split
    · exact h.r_lt
    · exact Nat.mod_lt _ h.m_pos
  exact ⟨h.base_lt,h.exp_lt,h.m_pos,h.m_le,hr,hb,by have := Nat.div_le_self e 2; have := h.e_lt; omega⟩

theorem pexec_while (fu : Nat) (c : NExpr) (b : Command) (ps : PS) :
    pexec (fu+1) (.whileLoop c b) ps = (do
      let v ← c.denote (penv ps)
      if v = 0 then some ⟨ps,none,c.nodes+1,ps.mem.length+ps.bs.length+c.nodes+2⟩
      else do
        let r ← pexec (fu+1) b ps
        match r.ret with
        | some _ => none
        | none => do
            let r2 ← pexec fu (.whileLoop c b) r.ps
            some ⟨r2.ps,r2.ret,c.nodes+1+r.cost+r2.cost,
              max (ps.mem.length+ps.bs.length+c.nodes+2) (max r.need r2.need)⟩) := by
  rw [pexec]
  congr

theorem loop_exec (P : List Cell) : ∀ (n fu : Nat), n+1 ≤ fu → ∀ {base exp m r b e : Nat}, Ok base exp m r b e → e < 2^n →
    ∃ r1 bF, pexec fu LoopCmd (mk P (sv base exp m r b e)) = some r1 ∧
      r1.ps = mk P (sv base exp m (pw m n r b e) bF 0) ∧ bF < m ∧ r1.ret = none ∧ r1.cost ≤ 45*n+5 ∧
      r1.need ≤ P.length+12+40 := by
  intro n
  induction n with
  | zero =>
    intro fu hfu base exp m r b e h he
    obtain ⟨fu',rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1,by omega⟩
    have e0 : e = 0 := by simpa using he
    subst e0
    obtain ⟨_,_,_,_,_,e5⟩ := env_sv P h
    have hc := loopC_value (penv (mk P (sv base exp m r b 0))) 0 e5
    have hc0 : loopC.denote (penv (mk P (sv base exp m r b 0))) = some 0 := by simpa using hc
    rw [pexec_while]
    simp only [Bind.bind,Option.bind,hc0,ite_true]
    refine ⟨_,b,rfl,?_,h.b_lt,rfl,?_,?_⟩
    · simp [pw]
    · simp [NExpr.nodes]
    · simp [NExpr.nodes,sv,mk_size]
  | succ n ih =>
    intro fu hfu base exp m r b e h he
    obtain ⟨fu',rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1,by omega⟩
    obtain ⟨_,_,_,_,_,e5⟩ := env_sv P h
    have hc := loopC_value (penv (mk P (sv base exp m r b e))) e e5
    by_cases z : e = 0
    · subst z
      have hc0 : loopC.denote (penv (mk P (sv base exp m r b 0))) = some 0 := by simpa using hc
      rw [pexec_while]
      simp only [Bind.bind,Option.bind,hc0,ite_true]
      refine ⟨_,b,rfl,?_,h.b_lt,rfl,?_,?_⟩
      · simp [pw]
      · simp [NExpr.nodes]
      · simp [NExpr.nodes,sv,mk_size]
    · have hz : e / 2 < 2^n := by rw [Nat.pow_succ] at he; omega
      obtain ⟨r1,hr1,hps,hret,hcost,hneed⟩ := iter P h (fu'+1)
      obtain ⟨r2,bF,hr2,hps2,hbF,hret2,hcost2,hneed2⟩ := ih fu' (by omega) h.next hz
      have hz' : (if e = 0 then (0:Int) else 1) = 1 := by simp [z]
      rw [hz'] at hc
      rw [pexec_while]
      simp only [Bind.bind,Option.bind,hc]
      simp only [int_one_ne,ite_false,hr1,hret]
      rw [hps,hr2]
      refine ⟨_,bF,rfl,?_,hbF,hret2,?_,?_⟩
      · rw [hps2]; simp [pw, z]
      · simp [NExpr.nodes] at *; omega
      · simp [NExpr.nodes,sv,mk_size] at *
        omega

theorem pexec_prim (fu : Nat) (st : NStmt) (ps : PS) : pexec fu (.primitive st) ps = pstmt st ps := by
  rw [pexec]

theorem pexec_seq (fu : Nat) (a b : Command) (ps : PS) : pexec fu (.sequence a b) ps = (do
      let r ← pexec fu a ps
      match r.ret with
      | some _ => some r
      | none => do
          let r2 ← pexec fu b r.ps
          some ⟨r2.ps,r2.ret,r.cost+r2.cost,max r.need r2.need⟩) := by
  rw [pexec]
  congr

theorem seq_some {fu : Nat} {a b : Command} {ps : PS} {r r2 : PR} (h1 : pexec fu a ps = some r) (hr : r.ret = none)
    (h2 : pexec fu b r.ps = some r2) :
    pexec fu (.sequence a b) ps = some ⟨r2.ps,r2.ret,r.cost+r2.cost,max r.need r2.need⟩ := by
  rw [pexec_seq, h1]
  simp only [Bind.bind, Option.bind, hr, h2]

theorem seq_ret {fu : Nat} {a b : Command} {ps : PS} {r : PR} {v : Int} (h1 : pexec fu a ps = some r)
    (hr : r.ret = some v) : pexec fu (.sequence a b) ps = some r := by
  rw [pexec_seq, h1]
  simp only [Bind.bind, Option.bind, hr]

end Proofs.PowModStep
