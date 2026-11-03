import Proofs.Mod61Body
import Proofs.Mod61Math

namespace Proofs.Mul61Body
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership
open Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings Proofs.CppNestedProgram
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows
open Proofs.CppNestedConstruct Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.CppMixedInvoke
open Proofs.DoublingNested Proofs.DoublingPrologue Proofs.FlatVectorStmt Proofs.QuotientFrame
open Proofs.QuotientSearch Proofs.Mod61Body
open Proofs.CppState (Cell)

-- u64 binary operations on natural numbers.
theorem denote_nat_bin (env : Nat → Ty → Option Int) (op : Binary) (f : Nat → Nat → Nat)
    (hf : ∀ x y : Nat, binaryValue op (x : Int) (y : Int) = ((f x y : Nat) : Int)) (e1 e2 : NExpr) (x y : Nat)
    (h1 : e1.denote env = some (x : Int)) (h2 : e2.denote env = some (y : Int))
    (lt : f x y < 18446744073709551616) :
    (NExpr.binary u64 op e1 e2).denote env = some ((f x y : Nat) : Int) := by
  rw [den_binary,h1,h2]
  simp only [Option.bind_some,hf]
  exact Ty.convert_of_valid _ _ (u64_lt _ lt)

theorem add_hf : ∀ x y : Nat, binaryValue .add (x : Int) (y : Int) = (((fun a b => a + b) x y : Nat) : Int) := by
  intro x y; simp [binaryValue]
theorem mul_hf : ∀ x y : Nat, binaryValue .mul (x : Int) (y : Int) = (((fun a b => a * b) x y : Nat) : Int) := by
  intro x y; simp [binaryValue]
theorem sub_hf : ∀ x y : Nat, y ≤ x → binaryValue .sub (x : Int) (y : Int) = (((fun a b => a - b) x y : Nat) : Int) := by
  intro x y h; simp [binaryValue]; omega
theorem shr_hf : ∀ x y : Nat, binaryValue .shr (x : Int) (y : Int) = (((fun a b => a / 2^b) x y : Nat) : Int) := by
  intro x y; simp [binaryValue,Nat.shiftRight_eq_div_pow]
theorem shl_hf : ∀ x y : Nat, binaryValue .shl (x : Int) (y : Int) = (((fun a b => a * 2^b) x y : Nat) : Int) := by
  intro x y; simp [binaryValue]
theorem band_hf : ∀ x y : Nat, binaryValue .band (x : Int) (y : Int) = (((fun a b => a &&& b) x y : Nat) : Int) := by
  intro x y; simp [binaryValue]

theorem lit_i32 (env : Nat → Ty → Option Int) (k : Nat) (h : k < 2147483648) :
    (NExpr.literal i32 (k : Int)).denote env = some (k : Int) := by
  have : i32.valid (k : Int) = true := i32_valid_nat k h
  simp [NExpr.denote,this]


theorem litN_value (env : Nat → Ty → Option Int) (k : Nat) (h : k < 2147483648) :
    (NExpr.literal i32 (k : Int)).denote env = some (k : Int) := lit_i32 env k h

theorem shr_lit (env : Nat → Ty → Option Int) (i : Nat) (x k : Nat) (hx : x < 18446744073709551616)
    (hk : k < 2147483648) (hi : env i u64 = some (x : Int)) :
    (NExpr.binary u64 .shr (.variable u64 i) (.literal i32 (k : Int))).denote env = some ((x / 2^k : Nat) : Int) := by
  have := denote_nat_bin env .shr (fun a b => a / 2^b) shr_hf (.variable u64 i) (.literal i32 (k : Int)) x k
    (by rw [den_variable]; exact hi) (litN_value env k hk)
    (by have := Nat.div_le_self x (2^k); omega)
  exact this

theorem band_pow (env : Nat → Ty → Option Int) (i j : Nat) (x n : Nat) (hx : x < 18446744073709551616)
    (hi : env i u64 = some (x : Int)) (hj : env j u64 = some ((2^n - 1 : Nat) : Int)) :
    (NExpr.binary u64 .band (.variable u64 i) (.variable u64 j)).denote env = some ((x % 2^n : Nat) : Int) := by
  have := denote_nat_bin env .band (fun a b => a &&& b) band_hf (.variable u64 i) (.variable u64 j) x (2^n - 1)
    (by rw [den_variable]; exact hi) (by rw [den_variable]; exact hj)
    (by simp only [Nat.and_two_pow_sub_one_eq_mod]; have := Nat.mod_le x (2^n); omega)
  simpa only [Nat.and_two_pow_sub_one_eq_mod] using this

theorem mul_vars (env : Nat → Ty → Option Int) (i j : Nat) (x y : Nat) (hi : env i u64 = some (x : Int))
    (hj : env j u64 = some (y : Int)) (lt : x * y < 18446744073709551616) :
    (NExpr.binary u64 .mul (.variable u64 i) (.variable u64 j)).denote env = some ((x * y : Nat) : Int) :=
  denote_nat_bin env .mul (fun a b => a * b) mul_hf _ _ x y (by rw [den_variable]; exact hi)
    (by rw [den_variable]; exact hj) lt

abbrev m31E : NExpr := .binary u64 .sub (.binary u64 .mul (.literal u64 1) (.literal u64 2147483648))
  (.cast u64 (.literal i32 1))
abbrev m30E : NExpr := .binary u64 .sub (.binary u64 .mul (.literal u64 1) (.literal u64 1073741824))
  (.cast u64 (.literal i32 1))

theorem m31_value (env : Nat → Ty → Option Int) : m31E.denote env = some 2147483647 := by
  have a : u64.valid 1 = true := by simp [Ty.valid]
  have b : u64.valid 2147483648 = true := by simp [Ty.valid]
  have c : i32.valid 1 = true := by simp [Ty.valid]
  have d : u64.valid 2147483647 = true := by simp [Ty.valid]
  simp [NExpr.denote,a,b,c,binaryValue,Ty.convert_of_valid _ _ a,Ty.convert_of_valid _ _ b,
    Ty.convert_of_valid _ _ d]

theorem m30_value (env : Nat → Ty → Option Int) : m30E.denote env = some 1073741823 := by
  have a : u64.valid 1 = true := by simp [Ty.valid]
  have b : u64.valid 1073741824 = true := by simp [Ty.valid]
  have c : i32.valid 1 = true := by simp [Ty.valid]
  have d : u64.valid 1073741823 = true := by simp [Ty.valid]
  simp [NExpr.denote,a,b,c,binaryValue,Ty.convert_of_valid _ _ a,Ty.convert_of_valid _ _ b,
    Ty.convert_of_valid _ _ d]


def w2 (j : Nat) : Bool := decide (j ≠ 2 ∧ j ≠ 3)

def midOf (a b : Nat) : Nat := (a % 2^31) * (b / 2^31) + (a / 2^31) * (b % 2^31)
def retOf (a b : Nat) : Nat :=
  (a / 2^31) * (b / 2^31) * 2 + midOf a b / 2^30 + (midOf a b % 2^30) * 2^31 + (a % 2^31) * (b % 2^31)

-- All eleven cells of `mul61` once every local is declared.
def full (a b : Nat) : List Int :=
  [(a : Int),(b : Int),2147483647,1073741823,((a / 2^31 : Nat) : Int),((a % 2^31 : Nat) : Int),
   ((b / 2^31 : Nat) : Int),((b % 2^31 : Nat) : Int),((midOf a b : Nat) : Int),((midOf a b / 2^30 : Nat) : Int),
   ((midOf a b % 2^30 : Nat) : Int)]

theorem full_length (a b : Nat) : (full a b).length = 11 := rfl

abbrev QSk (S : NState) (P : List Cell) (B sc : Nat) (a b k : Nat) : Prop :=
  QS S P B sc (cm ((full a b).take k)) (bmd P k w2) (ssl k)

theorem env_k {S : NState} {P : List Cell} {B sc a b k : Nat} (qs : QSk S P B sc a b k) (idx : Nat) (v : Int)
    (hidx : idx < k) (hk : k ≤ 11) (hv : (full a b)[idx]? = some v) (valid : u64.valid v = true) :
    envOf S idx u64 = some v := by
  have hl : ((full a b).take k).length = k := by simp [full_length]; omega
  have qs' : QS S P B sc (cm ((full a b).take k)) (bmd P ((full a b).take k).length w2)
      (ssl ((full a b).take k).length) := by rw [hl]; exact qs
  exact env_cm qs' idx v (by omega) (by rw [List.getElem?_take_of_lt hidx]; exact hv) valid

theorem live_k {S : NState} {P : List Cell} {B sc a b k : Nat} (qs : QSk S P B sc a b k) (hk : k ≤ 11) :
    liveS S = P.length+k-B+k := by
  rw [qs.live_eq]; simp [cm_length,bmd_length,full_length]; omega

theorem decl_k {P : List Cell} {B sc a b k : Nat} {SPB TPB W : Nat} (S : NState) (e : NExpr) (writable : Bool)
    (hk : k < 11) (hw : writable = w2 k) (v : Int) (hv : (full a b)[k]? = some v) (valid : u64.valid v = true)
    (qs : QSk S P B sc a b k) (cq : Cq SPB TPB W S) (cap : liveS S+e.nodes+1 ≤ SPB)
    (scalar : e.scalarOnly = true) (value : e.denote (envOf S) = some v) :
    ∃ t, (NStmt.declare u64 writable e).run S = some ⟨t,none,false⟩ ∧ t.frame = S.frame ∧
      QSk t P B sc a b (k+1) ∧ Cq SPB TPB (W+e.nodes+1) t := by
  have hl : ((full a b).take k).length = k := by simp [full_length]; omega
  have qs' : QS S P B sc (cm ((full a b).take k)) (bmd P ((full a b).take k).length w2)
      (ssl ((full a b).take k).length) := by rw [hl]; exact qs
  have hv' : (full a b)[k]? = some v := hv
  obtain ⟨t,run,fr,qsT,cqT⟩ := decl_cm S e writable v (by rw [hl]; exact hw) valid qs' cq cap scalar value
  refine ⟨t,run,fr,?_,cqT⟩
  have take : (full a b).take (k+1) = (full a b).take k ++ [v] := by
    rw [List.take_add_one]
    simp [hv']
  rw [hl] at qsT
  show QS t P B sc (cm ((full a b).take (k+1))) (bmd P (k+1) w2) (ssl (k+1))
  rw [take]
  exact qsT


theorem mul_bounds (a b : Nat) (ha : a < 2^61) (hb : b < 2^61) :
    (a / 2^31) * (b / 2^31) < 2^60 ∧ (a % 2^31) * (b / 2^31) < 2^61 ∧ (a / 2^31) * (b % 2^31) < 2^61 ∧
    (a % 2^31) * (b % 2^31) < 2^62 ∧ midOf a b < 2^62 ∧ (midOf a b % 2^30) * 2^31 < 2^61 ∧
    midOf a b / 2^30 < 2^32 ∧ retOf a b < 2^64 := by
  have au_lt : a / 2^31 ≤ 2^30 - 1 := by omega
  have bu_lt : b / 2^31 ≤ 2^30 - 1 := by omega
  have ad_lt : a % 2^31 ≤ 2^31 - 1 := by omega
  have bd_lt : b % 2^31 ≤ 2^31 - 1 := by omega
  have p1 : (a / 2^31) * (b / 2^31) ≤ (2^30-1) * (2^30-1) := Nat.mul_le_mul au_lt bu_lt
  have p2 : (a % 2^31) * (b / 2^31) ≤ (2^31-1) * (2^30-1) := Nat.mul_le_mul ad_lt bu_lt
  have p3 : (a / 2^31) * (b % 2^31) ≤ (2^30-1) * (2^31-1) := Nat.mul_le_mul au_lt bd_lt
  have p4 : (a % 2^31) * (b % 2^31) ≤ (2^31-1) * (2^31-1) := Nat.mul_le_mul ad_lt bd_lt
  have m := Proofs.Mod61Math.mul61_math a b (a / 2^31) (a % 2^31) (b / 2^31) (b % 2^31) (midOf a b)
    (midOf a b / 2^30) (midOf a b % 2^30) ha hb rfl rfl rfl rfl rfl rfl rfl
  unfold midOf at *
  unfold retOf
  refine ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,?_⟩
  exact m.1


abbrev v0 : NExpr := .variable u64 0
abbrev auE : NExpr := .binary u64 .shr (.variable u64 0) (.literal i32 31)
abbrev adE : NExpr := .binary u64 .band (.variable u64 0) (.variable u64 2)
abbrev buE : NExpr := .binary u64 .shr (.variable u64 1) (.literal i32 31)
abbrev bdE : NExpr := .binary u64 .band (.variable u64 1) (.variable u64 2)
abbrev midE : NExpr := .binary u64 .add (.binary u64 .mul (.variable u64 5) (.variable u64 6))
  (.binary u64 .mul (.variable u64 4) (.variable u64 7))
abbrev miduE : NExpr := .binary u64 .shr (.variable u64 8) (.literal i32 30)
abbrev middE : NExpr := .binary u64 .band (.variable u64 8) (.variable u64 3)
abbrev retE : NExpr :=
  .binary u64 .add (.binary u64 .add (.binary u64 .add (.binary u64 .mul (.binary u64 .mul (.variable u64 4)
    (.variable u64 6)) (.cast u64 (.literal i32 2))) (.variable u64 9))
    (.binary u64 .shl (.variable u64 10) (.literal i32 31))) (.binary u64 .mul (.variable u64 5) (.variable u64 7))

abbrev mulCmd : Command :=
  (.sequence (.primitive (.declare u64 false m31E)) (.sequence (.primitive (.declare u64 false m30E)) (.sequence (.primitive (.declare u64 true auE)) (.sequence (.primitive (.declare u64 true adE)) (.sequence (.primitive (.declare u64 true buE)) (.sequence (.primitive (.declare u64 true bdE)) (.sequence (.primitive (.declare u64 true midE)) (.sequence (.primitive (.declare u64 true miduE)) (.sequence (.primitive (.declare u64 true middE)) (.sequence (.primitive (.ret retE)) (.primitive .skip)))))))))))

theorem body_eq : Proofs.Mod61Instance.mul61.body = mulCmd := rfl


theorem mul61_run {P : List Cell} {B sc L0 T0 N scq SPB TPB W : Nat} (S : NState) (a b : Nat)
    (ha : a < 2^61) (hb : b < 2^61) (qs : QSk S P B sc a b 2) (fa : FA S.frame L0 T0 scq N)
    (cq : Cq SPB TPB W S) (spb : P.length+11-B+11+60 ≤ SPB) :
    RunsTo mulCmd S fun step => step.returned = some (.scalar ((retOf a b : Nat) : Int)) ∧
      step.breaking = false ∧ ∃ D, step.state = D.charge 1 0 ∧ QSk D P B sc a b 11 ∧
      FA D.frame L0 T0 scq N ∧ Cq SPB TPB (W+200) D := by
  obtain ⟨bn1,bn2,bn3,bn4,bn5,bn6,bn7,bn8⟩ := mul_bounds a b ha hb
  have a64 : a < 18446744073709551616 := by omega
  have b64 : b < 18446744073709551616 := by omega
  have va : u64.valid (a : Int) = true := u64_lt a a64
  have vb : u64.valid (b : Int) = true := u64_lt b b64
  have p31 : u64.valid 2147483647 = true := by simp [Ty.valid]
  have p30 : u64.valid 1073741823 = true := by simp [Ty.valid]
  have eS : (fx SPB TPB).SPB = SPB := rfl
  -- m31
  obtain ⟨s1,run1,fr1,qs1,cq1⟩ := decl_k S m31E false (by omega) (by decide) 2147483647 (by simp [full]) p31 qs cq
    (by rw [live_k qs (by omega)]; simp [NExpr.nodes]; omega) (by simp [NExpr.scalarOnly]) (m31_value _)
  have fa1 : FA s1.frame L0 T0 scq N := fa.of_eq fr1
  -- m30
  obtain ⟨s2,run2,fr2,qs2,cq2⟩ := decl_k s1 m30E false (by omega) (by decide) 1073741823 (by simp [full]) p30 qs1 cq1
    (by rw [live_k qs1 (by omega)]; simp [NExpr.nodes]; omega) (by simp [NExpr.scalarOnly]) (m30_value _)
  have fa2 : FA s2.frame L0 T0 scq N := fa1.of_eq fr2
  -- au
  have e0 := env_k qs2 0 (a : Int) (by omega) (by omega) (by simp [full]) va
  obtain ⟨s3,run3,fr3,qs3,cq3⟩ := decl_k s2 auE true (by omega) (by decide) ((a / 2^31 : Nat) : Int) (by simp [full])
    (u64_lt _ (by omega)) qs2 cq2 (by rw [live_k qs2 (by omega)]; simp [NExpr.nodes]; omega)
    (by simp [NExpr.scalarOnly]) (shr_lit _ 0 a 31 a64 (by omega) e0)
  have fa3 : FA s3.frame L0 T0 scq N := fa2.of_eq fr3
  have M31 : u64.valid ((2^31-1 : Nat) : Int) = true := u64_lt _ (by omega)
  have M30 : u64.valid ((2^30-1 : Nat) : Int) = true := u64_lt _ (by omega)
  -- ad
  have e2 := env_k qs3 2 ((2^31-1 : Nat) : Int) (by omega) (by omega) (by simp [full]) M31
  have e0' := env_k qs3 0 (a : Int) (by omega) (by omega) (by simp [full]) va
  obtain ⟨s4,run4,fr4,qs4,cq4⟩ := decl_k s3 adE true (by omega) (by decide) ((a % 2^31 : Nat) : Int) (by simp [full])
    (u64_lt _ (by omega)) qs3 cq3 (by rw [live_k qs3 (by omega)]; simp [NExpr.nodes]; omega)
    (by simp [NExpr.scalarOnly]) (band_pow _ 0 2 a 31 a64 e0' e2)
  have fa4 : FA s4.frame L0 T0 scq N := fa3.of_eq fr4
  -- bu
  have e1 := env_k qs4 1 (b : Int) (by omega) (by omega) (by simp [full]) vb
  obtain ⟨s5,run5,fr5,qs5,cq5⟩ := decl_k s4 buE true (by omega) (by decide) ((b / 2^31 : Nat) : Int) (by simp [full])
    (u64_lt _ (by omega)) qs4 cq4 (by rw [live_k qs4 (by omega)]; simp [NExpr.nodes]; omega)
    (by simp [NExpr.scalarOnly]) (shr_lit _ 1 b 31 b64 (by omega) e1)
  have fa5 : FA s5.frame L0 T0 scq N := fa4.of_eq fr5
  -- bd
  have f1 := env_k qs5 1 (b : Int) (by omega) (by omega) (by simp [full]) vb
  have f2 := env_k qs5 2 ((2^31-1 : Nat) : Int) (by omega) (by omega) (by simp [full]) M31
  obtain ⟨s6,run6,fr6,qs6,cq6⟩ := decl_k s5 bdE true (by omega) (by decide) ((b % 2^31 : Nat) : Int) (by simp [full])
    (u64_lt _ (by omega)) qs5 cq5 (by rw [live_k qs5 (by omega)]; simp [NExpr.nodes]; omega)
    (by simp [NExpr.scalarOnly]) (band_pow _ 1 2 b 31 b64 f1 f2)
  have fa6 : FA s6.frame L0 T0 scq N := fa5.of_eq fr6
  -- mid
  have g4 := env_k qs6 4 ((a / 2^31 : Nat) : Int) (by omega) (by omega) (by simp [full]) (u64_lt _ (by omega))
  have g5 := env_k qs6 5 ((a % 2^31 : Nat) : Int) (by omega) (by omega) (by simp [full]) (u64_lt _ (by omega))
  have g6 := env_k qs6 6 ((b / 2^31 : Nat) : Int) (by omega) (by omega) (by simp [full]) (u64_lt _ (by omega))
  have g7 := env_k qs6 7 ((b % 2^31 : Nat) : Int) (by omega) (by omega) (by simp [full]) (u64_lt _ (by omega))
  have vmid := denote_nat_bin (envOf s6) .add (fun x y => x + y) add_hf
    (.binary u64 .mul (.variable u64 5) (.variable u64 6)) (.binary u64 .mul (.variable u64 4) (.variable u64 7))
    ((a % 2^31) * (b / 2^31)) ((a / 2^31) * (b % 2^31))
    (mul_vars _ 5 6 _ _ g5 g6 (by omega)) (mul_vars _ 4 7 _ _ g4 g7 (by omega)) (by
      have : midOf a b < 2^62 := bn5
      unfold midOf at this; omega)
  obtain ⟨s7,run7,fr7,qs7,cq7⟩ := decl_k s6 midE true (by omega) (by decide) ((midOf a b : Nat) : Int) (by simp [full])
    (u64_lt _ (by omega)) qs6 cq6 (by rw [live_k qs6 (by omega)]; simp [NExpr.nodes]; omega)
    (by simp [NExpr.scalarOnly]) vmid
  have fa7 : FA s7.frame L0 T0 scq N := fa6.of_eq fr7
  -- midu
  have h8 := env_k qs7 8 ((midOf a b : Nat) : Int) (by omega) (by omega) (by simp [full]) (u64_lt _ (by omega))
  obtain ⟨s8,run8,fr8,qs8,cq8⟩ := decl_k s7 miduE true (by omega) (by decide) ((midOf a b / 2^30 : Nat) : Int)
    (by simp [full]) (u64_lt _ (by omega)) qs7 cq7 (by rw [live_k qs7 (by omega)]; simp [NExpr.nodes]; omega)
    (by simp [NExpr.scalarOnly]) (shr_lit _ 8 (midOf a b) 30 (by omega) (by omega) h8)
  have fa8 : FA s8.frame L0 T0 scq N := fa7.of_eq fr8
  -- midd
  have i8 := env_k qs8 8 ((midOf a b : Nat) : Int) (by omega) (by omega) (by simp [full]) (u64_lt _ (by omega))
  have i3 := env_k qs8 3 ((2^30-1 : Nat) : Int) (by omega) (by omega) (by simp [full]) M30
  obtain ⟨s9,run9,fr9,qs9,cq9⟩ := decl_k s8 middE true (by omega) (by decide) ((midOf a b % 2^30 : Nat) : Int)
    (by simp [full]) (u64_lt _ (by omega)) qs8 cq8 (by rw [live_k qs8 (by omega)]; simp [NExpr.nodes]; omega)
    (by simp [NExpr.scalarOnly]) (band_pow _ 8 3 (midOf a b) 30 (by omega) i8 i3)
  have fa9 : FA s9.frame L0 T0 scq N := fa8.of_eq fr9
  -- return
  have j4 := env_k qs9 4 ((a / 2^31 : Nat) : Int) (by omega) (by omega) (by simp [full]) (u64_lt _ (by omega))
  have j5 := env_k qs9 5 ((a % 2^31 : Nat) : Int) (by omega) (by omega) (by simp [full]) (u64_lt _ (by omega))
  have j6 := env_k qs9 6 ((b / 2^31 : Nat) : Int) (by omega) (by omega) (by simp [full]) (u64_lt _ (by omega))
  have j7 := env_k qs9 7 ((b % 2^31 : Nat) : Int) (by omega) (by omega) (by simp [full]) (u64_lt _ (by omega))
  have j9 := env_k qs9 9 ((midOf a b / 2^30 : Nat) : Int) (by omega) (by omega) (by simp [full]) (u64_lt _ (by omega))
  have j10 := env_k qs9 10 ((midOf a b % 2^30 : Nat) : Int) (by omega) (by omega) (by simp [full])
    (u64_lt _ (by omega))
  have w1 := mul_vars (envOf s9) 4 6 _ _ j4 j6 (by omega)
  have w2' := denote_nat_bin (envOf s9) .mul (fun x y => x * y) mul_hf
    (.binary u64 .mul (.variable u64 4) (.variable u64 6)) (.cast u64 (.literal i32 2))
    ((a / 2^31) * (b / 2^31)) 2 w1 (lit2_value _) (by omega)
  have w3 := denote_nat_bin (envOf s9) .add (fun x y => x + y) add_hf _ (.variable u64 9) _ _ w2'
    (by rw [den_variable]; exact j9) (by omega)
  have w4 := denote_nat_bin (envOf s9) .shl (fun x y => x * 2^y) shl_hf (.variable u64 10) (.literal i32 31)
    (midOf a b % 2^30) 31 (by rw [den_variable]; exact j10) (litN_value _ 31 (by omega)) (by omega)
  have w5 := denote_nat_bin (envOf s9) .add (fun x y => x + y) add_hf _ _ _ _ w3 w4 (by omega)
  have w6 := mul_vars (envOf s9) 5 7 _ _ j5 j7 (by omega)
  have w7 := denote_nat_bin (envOf s9) .add (fun x y => x + y) add_hf _ _ _ _ w5 w6 (by
    unfold retOf at bn8; omega)
  have retVal : retE.denote (envOf s9) = some ((retOf a b : Nat) : Int) := by
    unfold retOf; exact w7
  obtain ⟨u,hu,good⟩ := scalar_eval retE s9 ((retOf a b : Nat) : Int) (by simp [NExpr.scalarOnly]) retVal
  have self := release_self good.1.1
  have run : (NStmt.ret retE).run s9 = some ⟨u.charge 1 0,some (.scalar ((retOf a b : Nat) : Int)),false⟩ := by
    simp [NStmt.run,hu,self]
  have cqU : Cq SPB TPB (W+200) u := by
    have c1 := cq9.good good (by rw [live_k qs9 (by omega)]; simp [NExpr.nodes]; omega)
    exact c1.mono (by simp [NExpr.nodes])
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
  apply RunsTo.primitive run5
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seq
  apply RunsTo.primitive run6
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seq
  apply RunsTo.primitive run7
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seq
  apply RunsTo.primitive run8
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.seq
  apply RunsTo.primitive run9
  refine ⟨rfl,rfl,?_⟩
  apply RunsTo.sequence
  apply RunsTo.primitive run
  exact Or.inl ⟨Or.inl rfl,rfl,rfl,u,rfl,qs9.core good.1,fa9.of_eq (by simpa using good.1.1),cqU⟩

end Proofs.Mul61Body
