import Proofs.Generated.ModInt
import Proofs.PexecKit

namespace Proofs.ModIntExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.StraightLine Proofs.PowModStep
open Proofs.IntSim Proofs.PexecKit Proofs.QuotientSearch Proofs.DoublingNested Proofs.Mod61Body
open Proofs.CppState (Cell)

theorem u32_valid_of (v : Int) (h0 : 0 ≤ v) (h1 : v < 4294967296) : u32.valid v = true := by
  rw [valid_u32]; simp; omega

theorem u32_valid_nat (n : Nat) (h : n < 4294967296) : u32.valid (n : Int) = true :=
  u32_valid_of _ (by omega) (by omega)

theorem convert32 (n : Nat) (h : n < 4294967296) : u32.convert (n : Int) = some (n : Int) :=
  Ty.convert_of_valid _ _ (u32_valid_nat n h)

abbrev addE : NExpr := .binary u32 .add (.variable u32 0) (.variable u32 1)

theorem addE_value (env : Nat → Ty → Option Int) (x y : Nat) (h : x + y < 4294967296)
    (h0 : env 0 u32 = some (x : Int)) (h1 : env 1 u32 = some (y : Int)) :
    addE.denote env = some ((x + y : Nat) : Int) := by
  rw [den_binary, den_variable, den_variable, h0, h1]
  simp only [Option.bind_some, binaryValue]
  have : (x : Int) + (y : Int) = ((x + y : Nat) : Int) := by omega
  rw [this]
  exact convert32 _ h


abbrev geM (m : Nat) : NExpr := .binary bl .ge (.variable u32 0) (.literal u32 (m : Int))
abbrev subM (m : Nat) : NExpr := .binary u32 .sub (.variable u32 0) (.literal u32 (m : Int))
abbrev addM (m : Nat) : NExpr := .binary u32 .add (.variable u32 0) (.literal u32 (m : Int))

theorem lit32_value (env : Nat → Ty → Option Int) (m : Nat) (h : m < 4294967296) :
    (NExpr.literal u32 (m : Int)).denote env = some (m : Int) := by
  simp only [NExpr.denote]
  rw [u32_valid_nat m h]
  rfl

theorem geM_value (env : Nat → Ty → Option Int) (m v : Nat) (hm : m < 4294967296) (hv : v < 4294967296)
    (h0 : env 0 u32 = some (v : Int)) : (geM m).denote env = some (if m ≤ v then 1 else 0) := by
  rw [den_binary, den_variable, h0, lit32_value env m hm]
  simp only [Option.bind_some, binaryValue, convert_bl]
  by_cases c : m ≤ v
  · have : (v : Int) ≥ (m : Int) := by omega
    simp [this, c]
  · have : ¬ ((v : Int) ≥ (m : Int)) := by omega
    simp [this, c]

theorem subM_value (env : Nat → Ty → Option Int) (m v : Nat) (hm : m < 4294967296) (hv : m ≤ v)
    (hv2 : v < 4294967296) (h0 : env 0 u32 = some (v : Int)) : (subM m).denote env = some ((v - m : Nat) : Int) := by
  rw [den_binary, den_variable, h0, lit32_value env m hm]
  simp only [Option.bind_some, binaryValue]
  have : (v : Int) - (m : Int) = ((v - m : Nat) : Int) := by omega
  rw [this]
  exact convert32 _ (by omega)

theorem add_assign_exec (m : Nat) (hm : 2 ≤ m) (hm2 : m ≤ 2147483648) (P : List Cell) (a b x y : Nat)
    (hx : x < m) (hy : y < m) (ha : P[a]? = some ⟨u32,(x : Int)⟩) (hb : P[b]? = some ⟨u32,(y : Int)⟩)
    (hlt : a < P.length) :
    ∃ r, pexec 1 (Proofs.ModIntInstance.ModInt_add_assign m).body ⟨P,[⟨a,true⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = some (((x + y) % m : Nat) : Int) ∧ r.cost ≤ 30 ∧ r.need ≤ P.length+16 ∧
      r.ps = ⟨P.set a ⟨u32,(((x + y) % m : Nat) : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩ := by
  have hxv := u32_valid_nat x (by omega)
  have hyv := u32_valid_nat y (by omega)
  have hs : x + y < 4294967296 := by omega
  have hsv := u32_valid_nat (x + y) hs
  have hmv : m < 4294967296 := by omega
  have e0 : penv ⟨P,[⟨a,true⟩,⟨b,false⟩]⟩ 0 u32 = some (x : Int) :=
    penv_ok _ 0 u32 ⟨a,true⟩ ⟨u32,(x : Int)⟩ rfl ha rfl hxv
  have e1 : penv ⟨P,[⟨a,true⟩,⟨b,false⟩]⟩ 1 u32 = some (y : Int) :=
    penv_ok _ 1 u32 ⟨b,false⟩ ⟨u32,(y : Int)⟩ rfl hb rfl hyv
  have d1 := addE_value (penv ⟨P,[⟨a,true⟩,⟨b,false⟩]⟩) x y hs e0 e1
  have p1 := pstmt_assign_ok ⟨P,[⟨a,true⟩,⟨b,false⟩]⟩ 0 u32 addE ((x + y : Nat) : Int) d1 ⟨a,true⟩
    ⟨u32,(x : Int)⟩ rfl ha rfl hxv rfl _ (convert32 _ hs)
  have cellA : (P.set a (⟨u32,((x + y : Nat) : Int)⟩ : Cell))[a]? = some ⟨u32,((x + y : Nat) : Int)⟩ :=
    List.getElem?_set_self hlt
  have e0' : penv ⟨P.set a ⟨u32,((x + y : Nat) : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩ 0 u32 = some ((x + y : Nat) : Int) :=
    penv_ok _ 0 u32 ⟨a,true⟩ ⟨u32,((x + y : Nat) : Int)⟩ rfl cellA rfl hsv
  have dg := geM_value (penv ⟨P.set a ⟨u32,((x + y : Nat) : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩) m (x + y) hmv hs e0'
  have hlen1 : (P.set a (⟨u32,((x + y : Nat) : Int)⟩ : Cell)).length = P.length := by simp
  have q1 : pexec 1 (.primitive (.assign 0 u32 addE)) ⟨P,[⟨a,true⟩,⟨b,false⟩]⟩ =
      some ⟨⟨P.set a ⟨u32,((x + y : Nat) : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩,none,addE.nodes+1,P.length+2+addE.nodes+2⟩ := by
    rw [pexec_prim, p1]
    rfl
  have hqret : ∀ (v : Nat) (hv : v < 4294967296), pexec 1 (.sequence (.primitive (.ret (.variable u32 0))) Sk)
      ⟨P.set a ⟨u32,(v : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩ =
      some ⟨⟨P.set a ⟨u32,(v : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩,some (v : Int),2,P.length+2+1+2⟩ := by
    intro v hv
    have cellV : (P.set a (⟨u32,(v : Int)⟩ : Cell))[a]? = some ⟨u32,(v : Int)⟩ := List.getElem?_set_self hlt
    have ev : penv ⟨P.set a ⟨u32,(v : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩ 0 u32 = some (v : Int) :=
      penv_ok _ 0 u32 ⟨a,true⟩ ⟨u32,(v : Int)⟩ rfl cellV rfl (u32_valid_nat v hv)
    have pr := pstmt_ret_ok ⟨P.set a ⟨u32,(v : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩ (.variable u32 0) (v : Int)
      (by rw [den_variable]; exact ev)
    refine seq_ret (v := (v : Int)) (by rw [pexec_prim, pr]; simp [NExpr.nodes]) rfl
  have body_eq : (Proofs.ModIntInstance.ModInt_add_assign m).body =
      .sequence (.primitive (.assign 0 u32 addE)) (.sequence (.branch (geM m)
        (.sequence (.scope (.sequence (.primitive (.assign 0 u32 (subM m))) Sk)) Sk) Sk)
        (.sequence (.primitive (.ret (.variable u32 0))) Sk)) := rfl
  rw [body_eq]
  by_cases c : m ≤ x + y
  · have dg1 : (geM m).denote (penv ⟨P.set a ⟨u32,((x + y : Nat) : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩) = some 1 := by
      rw [dg]; simp [c]
    have hsub := subM_value (penv ⟨P.set a ⟨u32,((x + y : Nat) : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩) m (x + y) hmv c hs e0'
    have hres : x + y - m < 4294967296 := by omega
    have p2 := pstmt_assign_ok ⟨P.set a ⟨u32,((x + y : Nat) : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩ 0 u32 (subM m)
      ((x + y - m : Nat) : Int) hsub ⟨a,true⟩ ⟨u32,((x + y : Nat) : Int)⟩ rfl cellA rfl hsv rfl _ (convert32 _ hres)
    have hset : (P.set a (⟨u32,((x + y : Nat) : Int)⟩ : Cell)).set a ⟨u32,((x + y - m : Nat) : Int)⟩ =
        P.set a ⟨u32,((x + y - m : Nat) : Int)⟩ := List.set_set _
    have br := pexec_braced 1 (.assign 0 u32 (subM m)) ⟨P.set a ⟨u32,((x + y : Nat) : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩ _ p2
      rfl (by simp) rfl
    simp only [hset] at br
    have qb := pexec_branch_true 1 (geM m) _ Sk _ 1 dg1 (by decide) _ br
    have mod_eq : (x + y) % m = x + y - m := by
      rw [Nat.mod_eq_sub_mod c, Nat.mod_eq_of_lt (by omega)]
    have qr := hqret (x + y - m) hres
    have q2 := seq_some qb rfl qr
    have q3 := seq_some q1 rfl q2
    refine ⟨_,q3,?_,?_,?_,?_⟩
    · simp [mod_eq]
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]
    · simp [mod_eq]
  · have dg0 : (geM m).denote (penv ⟨P.set a ⟨u32,((x + y : Nat) : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩) = some 0 := by
      rw [dg]; simp [c]
    have qb := pexec_branch_false 1 (geM m) (.sequence (.scope (.sequence (.primitive (.assign 0 u32 (subM m))) Sk)) Sk) Sk
      _ dg0 _ (pexec_skip 1 _)
    have mod_eq : (x + y) % m = x + y := Nat.mod_eq_of_lt (by omega)
    have qr := hqret (x + y) hs
    have q2 := seq_some qb rfl qr
    have q3 := seq_some q1 rfl q2
    refine ⟨_,q3,?_,?_,?_,?_⟩
    · simp [mod_eq]
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]
    · simp [mod_eq]


abbrev subE : NExpr := .binary u32 .sub (.variable u32 0) (.variable u32 1)

theorem subE_value (env : Nat → Ty → Option Int) (x y : Nat) (hx : x < 4294967296) (hy : y < 4294967296)
    (h0 : env 0 u32 = some (x : Int)) (h1 : env 1 u32 = some (y : Int)) :
    subE.denote env = some (((x + 4294967296 - y) % 4294967296 : Nat) : Int) := by
  rw [den_binary, den_variable, den_variable, h0, h1]
  simp only [Option.bind_some, binaryValue, convert_u32]
  have : ((x : Int) - (y : Int)) % 4294967296 = (((x + 4294967296 - y) % 4294967296 : Nat) : Int) := by omega
  rw [this]

theorem addM_value (env : Nat → Ty → Option Int) (m v : Nat) (hm : m < 4294967296) (hv : v < 4294967296)
    (h0 : env 0 u32 = some (v : Int)) : (addM m).denote env = some (((v + m) % 4294967296 : Nat) : Int) := by
  rw [den_binary, den_variable, h0, lit32_value env m hm]
  simp only [Option.bind_some, binaryValue, convert_u32]
  have : ((v : Int) + (m : Int)) % 4294967296 = (((v + m) % 4294967296 : Nat) : Int) := by omega
  rw [this]

theorem sub_assign_exec (m : Nat) (hm : 2 ≤ m) (hm2 : m ≤ 2147483648) (P : List Cell) (a b x y : Nat)
    (hx : x < m) (hy : y < m) (ha : P[a]? = some ⟨u32,(x : Int)⟩) (hb : P[b]? = some ⟨u32,(y : Int)⟩)
    (hlt : a < P.length) :
    ∃ r, pexec 1 (Proofs.ModIntInstance.ModInt_sub_assign m).body ⟨P,[⟨a,true⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = some (((x + m - y) % m : Nat) : Int) ∧ r.cost ≤ 30 ∧ r.need ≤ P.length+16 ∧
      r.ps = ⟨P.set a ⟨u32,(((x + m - y) % m : Nat) : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩ := by
  have hxv := u32_valid_nat x (by omega)
  have hyv := u32_valid_nat y (by omega)
  have hmv : m < 4294967296 := by omega
  obtain ⟨w, hw⟩ : ∃ w, w = (x + 4294967296 - y) % 4294967296 := ⟨_, rfl⟩
  have hwlt : w < 4294967296 := by omega
  have hwv := u32_valid_nat w hwlt
  have e0 : penv ⟨P,[⟨a,true⟩,⟨b,false⟩]⟩ 0 u32 = some (x : Int) :=
    penv_ok _ 0 u32 ⟨a,true⟩ ⟨u32,(x : Int)⟩ rfl ha rfl hxv
  have e1 : penv ⟨P,[⟨a,true⟩,⟨b,false⟩]⟩ 1 u32 = some (y : Int) :=
    penv_ok _ 1 u32 ⟨b,false⟩ ⟨u32,(y : Int)⟩ rfl hb rfl hyv
  have d1 := subE_value (penv ⟨P,[⟨a,true⟩,⟨b,false⟩]⟩) x y (by omega) (by omega) e0 e1
  rw [← hw] at d1
  have p1 := pstmt_assign_ok ⟨P,[⟨a,true⟩,⟨b,false⟩]⟩ 0 u32 subE (w : Int) d1 ⟨a,true⟩
    ⟨u32,(x : Int)⟩ rfl ha rfl hxv rfl _ (convert32 _ hwlt)
  have cellA : (P.set a (⟨u32,(w : Int)⟩ : Cell))[a]? = some ⟨u32,(w : Int)⟩ := List.getElem?_set_self hlt
  have e0' : penv ⟨P.set a ⟨u32,(w : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩ 0 u32 = some (w : Int) :=
    penv_ok _ 0 u32 ⟨a,true⟩ ⟨u32,(w : Int)⟩ rfl cellA rfl hwv
  have dg := geM_value (penv ⟨P.set a ⟨u32,(w : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩) m w hmv hwlt e0'
  have q1 : pexec 1 (.primitive (.assign 0 u32 subE)) ⟨P,[⟨a,true⟩,⟨b,false⟩]⟩ =
      some ⟨⟨P.set a ⟨u32,(w : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩,none,subE.nodes+1,P.length+2+subE.nodes+2⟩ := by
    rw [pexec_prim, p1]
    rfl
  have hqret : ∀ (v : Nat) (hv : v < 4294967296), pexec 1 (.sequence (.primitive (.ret (.variable u32 0))) Sk)
      ⟨P.set a ⟨u32,(v : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩ =
      some ⟨⟨P.set a ⟨u32,(v : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩,some (v : Int),2,P.length+2+1+2⟩ := by
    intro v hv
    have cellV : (P.set a (⟨u32,(v : Int)⟩ : Cell))[a]? = some ⟨u32,(v : Int)⟩ := List.getElem?_set_self hlt
    have ev : penv ⟨P.set a ⟨u32,(v : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩ 0 u32 = some (v : Int) :=
      penv_ok _ 0 u32 ⟨a,true⟩ ⟨u32,(v : Int)⟩ rfl cellV rfl (u32_valid_nat v hv)
    have pr := pstmt_ret_ok ⟨P.set a ⟨u32,(v : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩ (.variable u32 0) (v : Int)
      (by rw [den_variable]; exact ev)
    refine seq_ret (v := (v : Int)) (by rw [pexec_prim, pr]; simp [NExpr.nodes]) rfl
  have body_eq : (Proofs.ModIntInstance.ModInt_sub_assign m).body =
      .sequence (.primitive (.assign 0 u32 subE)) (.sequence (.branch (geM m)
        (.sequence (.scope (.sequence (.primitive (.assign 0 u32 (addM m))) Sk)) Sk) Sk)
        (.sequence (.primitive (.ret (.variable u32 0))) Sk)) := rfl
  rw [body_eq]
  by_cases c : m ≤ w
  · have dg1 : (geM m).denote (penv ⟨P.set a ⟨u32,(w : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩) = some 1 := by
      rw [dg]; simp [c]
    have hadd := addM_value (penv ⟨P.set a ⟨u32,(w : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩) m w hmv hwlt e0'
    obtain ⟨z, hz⟩ : ∃ z, z = (w + m) % 4294967296 := ⟨_, rfl⟩
    have hzlt : z < 4294967296 := by omega
    rw [← hz] at hadd
    have p2 := pstmt_assign_ok ⟨P.set a ⟨u32,(w : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩ 0 u32 (addM m)
      (z : Int) hadd ⟨a,true⟩ ⟨u32,(w : Int)⟩ rfl cellA rfl hwv rfl _ (convert32 _ hzlt)
    have hset : (P.set a (⟨u32,(w : Int)⟩ : Cell)).set a ⟨u32,(z : Int)⟩ = P.set a ⟨u32,(z : Int)⟩ := List.set_set _
    have br := pexec_braced 1 (.assign 0 u32 (addM m)) ⟨P.set a ⟨u32,(w : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩ _ p2
      rfl (by simp) rfl
    simp only [hset] at br
    have qb := pexec_branch_true 1 (geM m) _ Sk _ 1 dg1 (by decide) _ br
    have qr := hqret z hzlt
    have q2 := seq_some qb rfl qr
    have q3 := seq_some q1 rfl q2
    -- here x < y, so w = x + 2^32 - y and z = x + m - y
    have hxy : x < y := by omega
    have hzv : z = x + m - y := by omega
    have mod_eq : (x + m - y) % m = x + m - y := Nat.mod_eq_of_lt (by omega)
    refine ⟨_,q3,?_,?_,?_,?_⟩
    · simp [mod_eq, hzv]
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]
    · simp [mod_eq, hzv]
  · have dg0 : (geM m).denote (penv ⟨P.set a ⟨u32,(w : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩) = some 0 := by
      rw [dg]; simp [c]
    have qb := pexec_branch_false 1 (geM m) (.sequence (.scope (.sequence (.primitive (.assign 0 u32 (addM m))) Sk)) Sk) Sk
      _ dg0 _ (pexec_skip 1 _)
    have qr := hqret w hwlt
    have q2 := seq_some qb rfl qr
    have q3 := seq_some q1 rfl q2
    have hyx : y ≤ x := by omega
    have hwv2 : w = x - y := by omega
    have mod_eq : (x + m - y) % m = x - y := by
      have : x + m - y = (x - y) + m := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    refine ⟨_,q3,?_,?_,?_,?_⟩
    · simp [mod_eq, hwv2]
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]
    · simp [mod_eq, hwv2]


abbrev mulM (m : Nat) : NExpr := .cast u32 (.divrem u64 true (.binary u64 .mul (.cast u64 (.variable u32 0))
  (.cast u64 (.variable u32 1))) (.cast u64 (.literal u32 (m : Int))))

theorem mulM_value (env : Nat → Ty → Option Int) (m x y : Nat) (hm : 0 < m) (hm2 : m < 4294967296)
    (hx : x < m) (hy : y < m) (h0 : env 0 u32 = some (x : Int)) (h1 : env 1 u32 = some (y : Int)) :
    (mulM m).denote env = some ((x * y % m : Nat) : Int) := by
  have hxy : x * y < 18446744073709551616 := by
    have : x * y < m * m := Nat.mul_lt_mul'' hx hy
    have : m * m ≤ 4294967296 * 4294967296 := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hxv : u64.valid (x : Int) = true := u64_lt x (by omega)
  have hyv : u64.valid (y : Int) = true := u64_lt y (by omega)
  have hmv : u64.valid (m : Int) = true := u64_lt m (by omega)
  have lit : u32.valid (m : Int) = true := u32_valid_nat m (by omega)
  have rem := rem_value (x * y) m hm hxy
  simp only [NExpr.denote, h0, h1, lit, ite_true, Option.bind_some, binaryValue]
  rw [Ty.convert_of_valid _ _ hxv, Ty.convert_of_valid _ _ hyv, Ty.convert_of_valid _ _ hmv]
  simp only [Option.bind_some]
  have e1 : (x : Int) * (y : Int) = ((x * y : Nat) : Int) := by omega
  rw [e1, Ty.convert_of_valid _ _ (u64_lt _ hxy)]
  simp only [Option.bind_some]
  rw [rem]
  simp only [Option.bind_some]
  exact convert32 _ (by have := Nat.mod_lt (x * y) hm; omega)


-- `ps.mem[a] := x'; return slot 0` for a reference parameter in slot 0.
theorem exec_assign_ret (fu : Nat) (P : List Cell) (bs : List CppState.Binding) (a x x' : Nat)
    (hb0 : bs[0]? = some ⟨a,true⟩) (ha : P[a]? = some ⟨u32,(x : Int)⟩) (hlt : a < P.length)
    (hx : x < 4294967296) (hx' : x' < 4294967296) (e : NExpr) (d : e.denote (penv ⟨P,bs⟩) = some (x' : Int)) :
    pexec fu (.sequence (.primitive (.assign 0 u32 e)) (.sequence (.primitive (.ret (.variable u32 0))) Sk)) ⟨P,bs⟩ =
      some ⟨⟨P.set a ⟨u32,(x' : Int)⟩,bs⟩,some (x' : Int),e.nodes+1+2,
        max (P.length+bs.length+e.nodes+2) (P.length+bs.length+1+2)⟩ := by
  have p1 := pstmt_assign_ok ⟨P,bs⟩ 0 u32 e (x' : Int) d ⟨a,true⟩ ⟨u32,(x : Int)⟩ hb0 ha rfl (u32_valid_nat x hx) rfl _
    (convert32 _ hx')
  have q1 : pexec fu (.primitive (.assign 0 u32 e)) ⟨P,bs⟩ =
      some ⟨⟨P.set a ⟨u32,(x' : Int)⟩,bs⟩,none,e.nodes+1,P.length+bs.length+e.nodes+2⟩ := by
    rw [pexec_prim, p1]
  have cellV : (P.set a (⟨u32,(x' : Int)⟩ : Cell))[a]? = some ⟨u32,(x' : Int)⟩ := List.getElem?_set_self hlt
  have ev : penv ⟨P.set a ⟨u32,(x' : Int)⟩,bs⟩ 0 u32 = some (x' : Int) :=
    penv_ok _ 0 u32 ⟨a,true⟩ ⟨u32,(x' : Int)⟩ hb0 cellV rfl (u32_valid_nat x' hx')
  have pr := pstmt_ret_ok ⟨P.set a ⟨u32,(x' : Int)⟩,bs⟩ (.variable u32 0) (x' : Int) (by rw [den_variable]; exact ev)
  have q2 : pexec fu (.sequence (.primitive (.ret (.variable u32 0))) Sk) ⟨P.set a ⟨u32,(x' : Int)⟩,bs⟩ =
      some ⟨⟨P.set a ⟨u32,(x' : Int)⟩,bs⟩,some (x' : Int),2,P.length+bs.length+1+2⟩ := by
    refine seq_ret (v := (x' : Int)) (by rw [pexec_prim, pr]; simp [NExpr.nodes]) rfl
  rw [seq_some q1 rfl q2]

theorem mul_assign_exec (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (P : List Cell) (a b x y : Nat)
    (hx : x < m) (hy : y < m) (ha : P[a]? = some ⟨u32,(x : Int)⟩) (hb : P[b]? = some ⟨u32,(y : Int)⟩)
    (hlt : a < P.length) :
    ∃ r, pexec 1 (Proofs.ModIntInstance.ModInt_mul_assign m).body ⟨P,[⟨a,true⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = some ((x * y % m : Nat) : Int) ∧ r.cost ≤ 30 ∧ r.need ≤ P.length+30 ∧
      r.ps = ⟨P.set a ⟨u32,((x * y % m : Nat) : Int)⟩,[⟨a,true⟩,⟨b,false⟩]⟩ := by
  have hxv := u32_valid_nat x (by omega)
  have hyv := u32_valid_nat y (by omega)
  have e0 : penv ⟨P,[⟨a,true⟩,⟨b,false⟩]⟩ 0 u32 = some (x : Int) :=
    penv_ok _ 0 u32 ⟨a,true⟩ ⟨u32,(x : Int)⟩ rfl ha rfl hxv
  have e1 : penv ⟨P,[⟨a,true⟩,⟨b,false⟩]⟩ 1 u32 = some (y : Int) :=
    penv_ok _ 1 u32 ⟨b,false⟩ ⟨u32,(y : Int)⟩ rfl hb rfl hyv
  have d := mulM_value (penv ⟨P,[⟨a,true⟩,⟨b,false⟩]⟩) m x y (by omega) hm2 hx hy e0 e1
  have body_eq : (Proofs.ModIntInstance.ModInt_mul_assign m).body =
      .sequence (.primitive (.assign 0 u32 (mulM m))) (.sequence (.primitive (.ret (.variable u32 0))) Sk) := rfl
  have hlt32 : x * y % m < 4294967296 := by have := Nat.mod_lt (x * y) (show 0 < m by omega); omega
  have q := exec_assign_ret 1 P [⟨a,true⟩,⟨b,false⟩] a x (x * y % m) rfl ha hlt (by omega) hlt32 (mulM m) d
  rw [body_eq]
  refine ⟨_,q,rfl,?_,?_,rfl⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes]


theorem exec_ret0 (fu : Nat) (P : List Cell) (bs : List CppState.Binding) (a v : Nat) (hb0 : bs[0]? = some ⟨a,true⟩)
    (hlt : a < P.length) (hv : v < 4294967296) :
    pexec fu (.sequence (.primitive (.ret (.variable u32 0))) Sk) ⟨P.set a ⟨u32,(v : Int)⟩,bs⟩ =
      some ⟨⟨P.set a ⟨u32,(v : Int)⟩,bs⟩,some (v : Int),2,P.length+bs.length+1+2⟩ := by
  have cellV : (P.set a (⟨u32,(v : Int)⟩ : Cell))[a]? = some ⟨u32,(v : Int)⟩ := List.getElem?_set_self hlt
  have ev : penv ⟨P.set a ⟨u32,(v : Int)⟩,bs⟩ 0 u32 = some (v : Int) :=
    penv_ok _ 0 u32 ⟨a,true⟩ ⟨u32,(v : Int)⟩ hb0 cellV rfl (u32_valid_nat v hv)
  have pr := pstmt_ret_ok ⟨P.set a ⟨u32,(v : Int)⟩,bs⟩ (.variable u32 0) (v : Int) (by rw [den_variable]; exact ev)
  refine seq_ret (v := (v : Int)) (by rw [pexec_prim, pr]; simp [NExpr.nodes]) rfl

abbrev castE (n : Nat) : NExpr := .cast u32 (.literal i32 (n : Int))

theorem castE_value (env : Nat → Ty → Option Int) (n : Nat) (h : n < 2147483648) :
    (castE n).denote env = some (n : Int) := by
  have l : i32.valid (n : Int) = true := by simp [Ty.valid]; omega
  simp only [NExpr.denote, l, ite_true, Option.bind_some]
  exact convert32 n (by omega)

abbrev eqLast (m : Nat) : NExpr := .binary bl .eq (.variable u32 0) (.binary u32 .sub (.literal u32 (m : Int)) (castE 1))
abbrev incE : NExpr := .binary u32 .add (.variable u32 0) (castE 1)
abbrev decE : NExpr := .binary u32 .sub (.variable u32 0) (castE 1)
abbrev eqZero : NExpr := .binary bl .eq (.variable u32 0) (castE 0)
abbrev lastE (m : Nat) : NExpr := .binary u32 .sub (.literal u32 (m : Int)) (castE 1)

theorem lastE_value (env : Nat → Ty → Option Int) (m : Nat) (hm : 1 ≤ m) (hm2 : m < 4294967296) :
    (lastE m).denote env = some ((m - 1 : Nat) : Int) := by
  rw [den_binary, lit32_value env m hm2, castE_value env 1 (by omega)]
  simp only [Option.bind_some, binaryValue]
  have : (m : Int) - ((1 : Nat) : Int) = ((m - 1 : Nat) : Int) := by omega
  rw [this]
  exact convert32 _ (by omega)

theorem eqLast_value (env : Nat → Ty → Option Int) (m x : Nat) (hm : 1 ≤ m) (hm2 : m < 4294967296) (hx : x < 4294967296)
    (h0 : env 0 u32 = some (x : Int)) : (eqLast m).denote env = some (if x = m - 1 then 1 else 0) := by
  rw [den_binary, den_variable, h0, lastE_value env m hm hm2]
  simp only [Option.bind_some, binaryValue, convert_bl]
  by_cases c : x = m - 1
  · have : ((x : Int) == ((m - 1 : Nat) : Int)) = true := by simp [c]
    simp [this, c]
  · have : ((x : Int) == ((m - 1 : Nat) : Int)) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    simp [this, c]

theorem incE_value (env : Nat → Ty → Option Int) (x : Nat) (hx : x + 1 < 4294967296) (h0 : env 0 u32 = some (x : Int)) :
    incE.denote env = some ((x + 1 : Nat) : Int) := by
  rw [den_binary, den_variable, h0, castE_value env 1 (by omega)]
  simp only [Option.bind_some, binaryValue]
  have : (x : Int) + ((1 : Nat) : Int) = ((x + 1 : Nat) : Int) := by omega
  rw [this]
  exact convert32 _ hx

theorem decE_value (env : Nat → Ty → Option Int) (x : Nat) (hx : 1 ≤ x) (hx2 : x < 4294967296) (h0 : env 0 u32 = some (x : Int)) :
    decE.denote env = some ((x - 1 : Nat) : Int) := by
  rw [den_binary, den_variable, h0, castE_value env 1 (by omega)]
  simp only [Option.bind_some, binaryValue]
  have : (x : Int) - ((1 : Nat) : Int) = ((x - 1 : Nat) : Int) := by omega
  rw [this]
  exact convert32 _ (by omega)

theorem eqZero_value (env : Nat → Ty → Option Int) (x : Nat) (hx : x < 4294967296) (h0 : env 0 u32 = some (x : Int)) :
    eqZero.denote env = some (if x = 0 then 1 else 0) := by
  rw [den_binary, den_variable, h0, castE_value env 0 (by omega)]
  simp only [Option.bind_some, binaryValue, convert_bl]
  by_cases c : x = 0
  · subst c; simp
  · have : ((x : Int) == ((0 : Nat) : Int)) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    simp [this, c]


theorem increment_exec (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (P : List Cell) (a x : Nat)
    (hx : x < m) (ha : P[a]? = some ⟨u32,(x : Int)⟩) (hlt : a < P.length) :
    ∃ r, pexec 1 (Proofs.ModIntInstance.ModInt_increment m).body ⟨P,[⟨a,true⟩]⟩ = some r ∧
      r.ret = some (((x + 1) % m : Nat) : Int) ∧ r.cost ≤ 30 ∧ r.need ≤ P.length+30 ∧
      r.ps = ⟨P.set a ⟨u32,(((x + 1) % m : Nat) : Int)⟩,[⟨a,true⟩]⟩ := by
  have hxv := u32_valid_nat x (by omega)
  have e0 : penv ⟨P,[⟨a,true⟩]⟩ 0 u32 = some (x : Int) := penv_ok _ 0 u32 ⟨a,true⟩ ⟨u32,(x : Int)⟩ rfl ha rfl hxv
  have dg := eqLast_value (penv ⟨P,[⟨a,true⟩]⟩) m x (by omega) hm2 (by omega) e0
  have body_eq : (Proofs.ModIntInstance.ModInt_increment m).body =
      .sequence (.branch (eqLast m) (.sequence (.scope (.sequence (.primitive (.assign 0 u32 (castE 0))) Sk)) Sk)
        (.sequence (.scope (.sequence (.primitive (.assign 0 u32 incE)) Sk)) Sk))
        (.sequence (.primitive (.ret (.variable u32 0))) Sk) := rfl
  rw [body_eq]
  by_cases c : x = m - 1
  · have dg1 : (eqLast m).denote (penv ⟨P,[⟨a,true⟩]⟩) = some 1 := by rw [dg]; simp [c]
    have d := castE_value (penv ⟨P,[⟨a,true⟩]⟩) 0 (by omega)
    have p1 := pstmt_assign_ok ⟨P,[⟨a,true⟩]⟩ 0 u32 (castE 0) ((0 : Nat) : Int) d ⟨a,true⟩ ⟨u32,(x : Int)⟩ rfl ha rfl hxv rfl _
      (convert32 0 (by omega))
    have br := pexec_braced 1 (.assign 0 u32 (castE 0)) ⟨P,[⟨a,true⟩]⟩ _ p1 rfl (by simp) rfl
    have qb := pexec_branch_true 1 (eqLast m) _ (.sequence (.scope (.sequence (.primitive (.assign 0 u32 incE)) Sk)) Sk) _ 1 dg1 (by decide) _ br
    have qr := exec_ret0 1 P [⟨a,true⟩] a 0 rfl hlt (by omega)
    have q2 := seq_some qb rfl (by simpa using qr)
    have hmod : (x + 1) % m = 0 := by
      have : x + 1 = m := by omega
      rw [this, Nat.mod_self]
    refine ⟨_,q2,?_,?_,?_,?_⟩
    · simp [hmod]
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]
    · simp [hmod]
  · have dg0 : (eqLast m).denote (penv ⟨P,[⟨a,true⟩]⟩) = some 0 := by rw [dg]; simp [c]
    have d := incE_value (penv ⟨P,[⟨a,true⟩]⟩) x (by omega) e0
    have p1 := pstmt_assign_ok ⟨P,[⟨a,true⟩]⟩ 0 u32 incE ((x + 1 : Nat) : Int) d ⟨a,true⟩ ⟨u32,(x : Int)⟩ rfl ha rfl hxv rfl _
      (convert32 _ (by omega))
    have br := pexec_braced 1 (.assign 0 u32 incE) ⟨P,[⟨a,true⟩]⟩ _ p1 rfl (by simp) rfl
    have qb := pexec_branch_false 1 (eqLast m) (.sequence (.scope (.sequence (.primitive (.assign 0 u32 (castE 0))) Sk)) Sk) _ _ dg0 _ br
    have qr := exec_ret0 1 P [⟨a,true⟩] a (x + 1) rfl hlt (by omega)
    have q2 := seq_some qb rfl (by simpa using qr)
    have hmod : (x + 1) % m = x + 1 := Nat.mod_eq_of_lt (by omega)
    refine ⟨_,q2,?_,?_,?_,?_⟩
    · simp [hmod]
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]
    · simp [hmod]


theorem decrement_exec (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (P : List Cell) (a x : Nat)
    (hx : x < m) (ha : P[a]? = some ⟨u32,(x : Int)⟩) (hlt : a < P.length) :
    ∃ r, pexec 1 (Proofs.ModIntInstance.ModInt_decrement m).body ⟨P,[⟨a,true⟩]⟩ = some r ∧
      r.ret = some (((x + m - 1) % m : Nat) : Int) ∧ r.cost ≤ 30 ∧ r.need ≤ P.length+30 ∧
      r.ps = ⟨P.set a ⟨u32,(((x + m - 1) % m : Nat) : Int)⟩,[⟨a,true⟩]⟩ := by
  have hxv := u32_valid_nat x (by omega)
  have e0 : penv ⟨P,[⟨a,true⟩]⟩ 0 u32 = some (x : Int) := penv_ok _ 0 u32 ⟨a,true⟩ ⟨u32,(x : Int)⟩ rfl ha rfl hxv
  have dg := eqZero_value (penv ⟨P,[⟨a,true⟩]⟩) x (by omega) e0
  have body_eq : (Proofs.ModIntInstance.ModInt_decrement m).body =
      .sequence (.branch eqZero (.sequence (.scope (.sequence (.primitive (.assign 0 u32 (lastE m))) Sk)) Sk)
        (.sequence (.scope (.sequence (.primitive (.assign 0 u32 decE)) Sk)) Sk))
        (.sequence (.primitive (.ret (.variable u32 0))) Sk) := rfl
  rw [body_eq]
  by_cases c : x = 0
  · have dg1 : eqZero.denote (penv ⟨P,[⟨a,true⟩]⟩) = some 1 := by rw [dg]; simp [c]
    have d := lastE_value (penv ⟨P,[⟨a,true⟩]⟩) m (by omega) hm2
    have p1 := pstmt_assign_ok ⟨P,[⟨a,true⟩]⟩ 0 u32 (lastE m) ((m - 1 : Nat) : Int) d ⟨a,true⟩ ⟨u32,(x : Int)⟩ rfl ha rfl hxv rfl _
      (convert32 _ (by omega))
    have br := pexec_braced 1 (.assign 0 u32 (lastE m)) ⟨P,[⟨a,true⟩]⟩ _ p1 rfl (by simp) rfl
    have qb := pexec_branch_true 1 eqZero _ (.sequence (.scope (.sequence (.primitive (.assign 0 u32 decE)) Sk)) Sk) _ 1 dg1
      (by decide) _ br
    have qr := exec_ret0 1 P [⟨a,true⟩] a (m - 1) rfl hlt (by omega)
    have q2 := seq_some qb rfl (by simpa using qr)
    have hmod : (x + m - 1) % m = m - 1 := by
      have : x + m - 1 = m - 1 := by omega
      rw [this, Nat.mod_eq_of_lt (by omega)]
    refine ⟨_,q2,?_,?_,?_,?_⟩
    · simp [hmod]
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]
    · simp [hmod]
  · have dg0 : eqZero.denote (penv ⟨P,[⟨a,true⟩]⟩) = some 0 := by rw [dg]; simp [c]
    have d := decE_value (penv ⟨P,[⟨a,true⟩]⟩) x (by omega) (by omega) e0
    have p1 := pstmt_assign_ok ⟨P,[⟨a,true⟩]⟩ 0 u32 decE ((x - 1 : Nat) : Int) d ⟨a,true⟩ ⟨u32,(x : Int)⟩ rfl ha rfl hxv rfl _
      (convert32 _ (by omega))
    have br := pexec_braced 1 (.assign 0 u32 decE) ⟨P,[⟨a,true⟩]⟩ _ p1 rfl (by simp) rfl
    have qb := pexec_branch_false 1 eqZero (.sequence (.scope (.sequence (.primitive (.assign 0 u32 (lastE m))) Sk)) Sk) _ _ dg0 _ br
    have qr := exec_ret0 1 P [⟨a,true⟩] a (x - 1) rfl hlt (by omega)
    have q2 := seq_some qb rfl (by simpa using qr)
    have hmod : (x + m - 1) % m = x - 1 := by
      have : x + m - 1 = (x - 1) + m := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    refine ⟨_,q2,?_,?_,?_,?_⟩
    · simp [hmod]
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]
    · simp [hmod]


theorem get_tail (P L : List Cell) (j : Nat) : (P ++ L)[P.length + j]? = L[j]? := by
  rw [List.getElem?_append_right (by omega)]
  simp

abbrev neZero : NExpr := .binary bl .ne (.variable u32 0) (castE 0)
abbrev negE (m : Nat) : NExpr := .binary u32 .sub (.literal u32 (m : Int)) (.variable u32 0)

theorem neZero_value (env : Nat → Ty → Option Int) (x : Nat) (hx : x < 4294967296) (h0 : env 0 u32 = some (x : Int)) :
    neZero.denote env = some (if x = 0 then 0 else 1) := by
  rw [den_binary, den_variable, h0, castE_value env 0 (by omega)]
  simp only [Option.bind_some, binaryValue, convert_bl]
  by_cases c : x = 0
  · subst c; simp
  · have : ((x : Int) != ((0 : Nat) : Int)) = true := by simp; omega
    simp [this, c]

theorem negE_value (env : Nat → Ty → Option Int) (m x : Nat) (hm : m < 4294967296) (hx : x ≤ m)
    (h0 : env 0 u32 = some (x : Int)) : (negE m).denote env = some ((m - x : Nat) : Int) := by
  rw [den_binary, den_variable, h0, lit32_value env m hm]
  simp only [Option.bind_some, binaryValue]
  have : (m : Int) - (x : Int) = ((m - x : Nat) : Int) := by omega
  rw [this]
  exact convert32 _ (by omega)

theorem neg_exec (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (P : List Cell) (a x : Nat)
    (hx : x < m) (ha : P[a]? = some ⟨u32,(x : Int)⟩) (hlt : a < P.length) :
    ∃ r, pexec 1 (Proofs.ModIntInstance.ModInt_sub_unary m).body ⟨P,[⟨a,false⟩]⟩ = some r ∧
      r.ret = some (((if x = 0 then 0 else m - x) : Nat) : Int) ∧ r.cost ≤ 60 ∧ r.need ≤ P.length+40 ∧
      ∃ L, r.ps.mem = P ++ L := by
  have hxv := u32_valid_nat x (by omega)
  have z0 := castE_value (fun _ _ => none) 0 (by omega)
  let c0 : Cell := ⟨u32,((0 : Nat) : Int)⟩
  have z0v : u32.valid ((0 : Nat) : Int) = true := u32_valid_nat 0 (by omega)
  -- first declaration: the inlined constructor result
  have s1 := pstmt_declare_ok ⟨P,[⟨a,false⟩]⟩ u32 true (castE 0) ((0 : Nat) : Int)
    (castE_value _ 0 (by omega)) ((0 : Nat) : Int) (convert32 0 (by omega))
  have q1 : pexec 1 (.primitive (.declare u32 true (castE 0))) ⟨P,[⟨a,false⟩]⟩ =
      some ⟨⟨P ++ [c0],[⟨a,false⟩,⟨P.length,true⟩]⟩,none,(castE 0).nodes+1,P.length+1+(castE 0).nodes+4⟩ := by
    rw [pexec_prim, s1]; rfl
  -- second declaration: r = that value
  have e1 : penv ⟨P ++ [c0],[⟨a,false⟩,⟨P.length,true⟩]⟩ 1 u32 = some ((0 : Nat) : Int) :=
    penv_ok _ 1 u32 ⟨P.length,true⟩ c0 rfl (by simpa using get_tail P [c0] 0) rfl z0v
  have s2 := pstmt_declare_ok ⟨P ++ [c0],[⟨a,false⟩,⟨P.length,true⟩]⟩ u32 true (.variable u32 1) ((0 : Nat) : Int)
    (by rw [den_variable]; exact e1) ((0 : Nat) : Int) (convert32 0 (by omega))
  have hl1 : (P ++ [c0]).length = P.length + 1 := by simp
  have q2 : pexec 1 (.primitive (.declare u32 true (.variable u32 1))) ⟨P ++ [c0],[⟨a,false⟩,⟨P.length,true⟩]⟩ =
      some ⟨⟨P ++ [c0,c0],[⟨a,false⟩,⟨P.length,true⟩,⟨P.length+1,true⟩]⟩,none,(NExpr.variable u32 1).nodes+1,
        (P ++ [c0]).length+2+(NExpr.variable u32 1).nodes+4⟩ := by
    rw [pexec_prim, s2]
    simp only [hl1, List.append_assoc]
    rfl
  have body_eq : (Proofs.ModIntInstance.ModInt_sub_unary m).body =
      .sequence (.primitive (.declare u32 true (castE 0))) (.sequence (.primitive (.declare u32 true (.variable u32 1)))
        (.sequence (.branch neZero (.sequence (.scope (.sequence (.primitive (.assign 2 u32 (negE m))) Sk)) Sk) Sk)
          (.sequence (.primitive (.ret (.variable u32 2))) Sk))) := rfl
  rw [body_eq]
  have ha2 : (P ++ [c0,c0])[a]? = some ⟨u32,(x : Int)⟩ := by
    rw [List.getElem?_append_left hlt]; exact ha
  have e0 : penv ⟨P ++ [c0,c0],[⟨a,false⟩,⟨P.length,true⟩,⟨P.length+1,true⟩]⟩ 0 u32 = some (x : Int) :=
    penv_ok _ 0 u32 ⟨a,false⟩ ⟨u32,(x : Int)⟩ rfl ha2 rfl hxv
  have dg := neZero_value (penv ⟨P ++ [c0,c0],[⟨a,false⟩,⟨P.length,true⟩,⟨P.length+1,true⟩]⟩) x (by omega) e0
  by_cases c : x = 0
  · have dg0 : neZero.denote (penv ⟨P ++ [c0,c0],[⟨a,false⟩,⟨P.length,true⟩,⟨P.length+1,true⟩]⟩) = some 0 := by
      rw [dg]; simp [c]
    have qb := pexec_branch_false 1 neZero (.sequence (.scope (.sequence (.primitive (.assign 2 u32 (negE m))) Sk)) Sk) Sk
      _ dg0 _ (pexec_skip 1 _)
    have cell2 : (P ++ [c0,c0])[P.length + 1]? = some c0 := by simpa using get_tail P [c0,c0] 1
    have er : penv ⟨P ++ [c0,c0],[⟨a,false⟩,⟨P.length,true⟩,⟨P.length+1,true⟩]⟩ 2 u32 = some ((0 : Nat) : Int) :=
      penv_ok _ 2 u32 ⟨P.length+1,true⟩ c0 rfl cell2 rfl z0v
    have pr := pstmt_ret_ok ⟨P ++ [c0,c0],[⟨a,false⟩,⟨P.length,true⟩,⟨P.length+1,true⟩]⟩ (.variable u32 2) ((0 : Nat) : Int)
      (by rw [den_variable]; exact er)
    have qr : pexec 1 (.sequence (.primitive (.ret (.variable u32 2))) Sk)
        ⟨P ++ [c0,c0],[⟨a,false⟩,⟨P.length,true⟩,⟨P.length+1,true⟩]⟩ = _ :=
      seq_ret (v := ((0 : Nat) : Int)) (by rw [pexec_prim, pr]) rfl
    have q3 := seq_some qb rfl qr
    have q4 := seq_some q2 rfl q3
    have q5 := seq_some q1 rfl q4
    refine ⟨_,q5,?_,?_,?_,[c0,c0],?_⟩
    · simp [c]
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]
    · rfl
  · have dg1 : neZero.denote (penv ⟨P ++ [c0,c0],[⟨a,false⟩,⟨P.length,true⟩,⟨P.length+1,true⟩]⟩) = some 1 := by
      rw [dg]; simp [c]
    have dn := negE_value (penv ⟨P ++ [c0,c0],[⟨a,false⟩,⟨P.length,true⟩,⟨P.length+1,true⟩]⟩) m x hm2 (by omega) e0
    have cell2 : (P ++ [c0,c0])[P.length + 1]? = some c0 := by simpa using get_tail P [c0,c0] 1
    have p3 := pstmt_assign_ok ⟨P ++ [c0,c0],[⟨a,false⟩,⟨P.length,true⟩,⟨P.length+1,true⟩]⟩ 2 u32 (negE m)
      ((m - x : Nat) : Int) dn ⟨P.length+1,true⟩ c0 rfl cell2 rfl z0v rfl _ (convert32 _ (by omega))
    have hset : (P ++ [c0,c0]).set (P.length+1) (⟨u32,((m - x : Nat) : Int)⟩ : Cell) = P ++ [c0,⟨u32,((m - x : Nat) : Int)⟩] := by
      rw [List.set_append_right _ _ (by omega)]
      simp
    have br := pexec_braced 1 (.assign 2 u32 (negE m)) ⟨P ++ [c0,c0],[⟨a,false⟩,⟨P.length,true⟩,⟨P.length+1,true⟩]⟩ _ p3
      rfl (by simp) rfl
    simp only [hset] at br
    have qb := pexec_branch_true 1 neZero _ Sk _ 1 dg1 (by decide) _ br
    have cell3 : (P ++ [c0,(⟨u32,((m - x : Nat) : Int)⟩ : Cell)])[P.length + 1]? = some ⟨u32,((m - x : Nat) : Int)⟩ := by
      simpa using get_tail P [c0,(⟨u32,((m - x : Nat) : Int)⟩ : Cell)] 1
    have er : penv ⟨P ++ [c0,⟨u32,((m - x : Nat) : Int)⟩],[⟨a,false⟩,⟨P.length,true⟩,⟨P.length+1,true⟩]⟩ 2 u32 =
        some ((m - x : Nat) : Int) :=
      penv_ok _ 2 u32 ⟨P.length+1,true⟩ ⟨u32,((m - x : Nat) : Int)⟩ rfl cell3 rfl (u32_valid_nat _ (by omega))
    have pr := pstmt_ret_ok ⟨P ++ [c0,⟨u32,((m - x : Nat) : Int)⟩],[⟨a,false⟩,⟨P.length,true⟩,⟨P.length+1,true⟩]⟩
      (.variable u32 2) ((m - x : Nat) : Int) (by rw [den_variable]; exact er)
    have qr : pexec 1 (.sequence (.primitive (.ret (.variable u32 2))) Sk)
        ⟨P ++ [c0,⟨u32,((m - x : Nat) : Int)⟩],[⟨a,false⟩,⟨P.length,true⟩,⟨P.length+1,true⟩]⟩ = _ :=
      seq_ret (v := ((m - x : Nat) : Int)) (by rw [pexec_prim, pr]) rfl
    have q3 := seq_some qb rfl qr
    have q4 := seq_some q2 rfl q3
    have q5 := seq_some q1 rfl q4
    refine ⟨_,q5,?_,?_,?_,[c0,⟨u32,((m - x : Nat) : Int)⟩],?_⟩
    · simp [c]
    · simp [NExpr.nodes]
    · simp [NExpr.nodes]
    · rfl


abbrev castM64 (m : Nat) : NExpr := .cast s64 (.literal u32 (m : Int))
abbrev newEv (m i : Nat) : NExpr := .cast u32 (.divrem s64 true (.binary s64 .add (.divrem s64 true (.variable s64 i)
  (castM64 m)) (castM64 m)) (castM64 m))
abbrev newE (m : Nat) : NExpr := newEv m 0

theorem s64_valid_of (v : Int) (h0 : -9223372036854775808 ≤ v) (h1 : v < 9223372036854775808) : s64.valid v = true := by
  rw [valid_s64]; exact decide_eq_true ⟨h0, h1⟩

theorem s64_valid_nat (n : Nat) (h : n < 4294967296) : s64.valid (n : Int) = true := by
  rw [valid_s64]; exact decide_eq_true ⟨by omega, by omega⟩

theorem castM64_value (env : Nat → Ty → Option Int) (m : Nat) (hm : m < 4294967296) :
    (castM64 m).denote env = some (m : Int) := by
  have l : u32.valid (m : Int) = true := u32_valid_nat m hm
  rw [den_cast, den_literal, if_pos l, Option.bind_some]
  exact convert_s64 _ (by omega) (by omega)

theorem newEv_value (env : Nat → Ty → Option Int) (m i : Nat) (v : Int) (hm : 0 < m) (hm2 : m < 4294967296)
    (hv : s64.valid v = true) (h0 : env i s64 = some v) : (newEv m i).denote env = some (v % (m : Int)) := by
  have hv' : -9223372036854775808 ≤ v ∧ v < 9223372036854775808 := by
    rw [valid_s64] at hv; simpa using hv
  have hM : (m : Int) ≠ 0 := by omega
  have t1 := Int.natAbs_tdiv_le_natAbs v (m : Int)
  have hs1 : 0 ≤ v → 0 ≤ v.tdiv (m : Int) := fun h => Int.tdiv_nonneg h (by omega)
  have hs2 : v < 0 → v.tdiv (m : Int) ≤ 0 := fun h => by
    have := Int.tdiv_nonneg (a := -v) (by omega) (show 0 ≤ (m : Int) by omega)
    rw [Int.neg_tdiv] at this; omega
  have t2 := Int.lt_tmod_of_pos v (show (0 : Int) < (m : Int) by omega)
  have t3 := Int.tmod_lt_of_pos v (show (0 : Int) < (m : Int) by omega)
  have hq : s64.valid (v.tdiv (m : Int)) = true := s64_valid_of _ (by omega) (by omega)
  have hr : s64.valid (v.tmod (m : Int)) = true := s64_valid_of _ (by omega) (by omega)
  have hs : s64.valid (v.tmod (m : Int) + (m : Int)) = true := s64_valid_of _ (by omega) (by omega)
  have u1 := Int.natAbs_tdiv_le_natAbs (v.tmod (m : Int) + (m : Int)) (m : Int)
  have u2 := Int.tmod_lt_of_pos (v.tmod (m : Int) + (m : Int)) (show (0 : Int) < (m : Int) by omega)
  have u3 := Int.tmod_nonneg (m : Int) (show (0 : Int) ≤ v.tmod (m : Int) + (m : Int) by omega)
  have hq2 : s64.valid ((v.tmod (m : Int) + (m : Int)).tdiv (m : Int)) = true := s64_valid_of _ (by omega) (by omega)
  have hr2 : s64.valid ((v.tmod (m : Int) + (m : Int)).tmod (m : Int)) = true := s64_valid_of _ (by omega) (by omega)
  have fin : (v.tmod (m : Int) + (m : Int)).tmod (m : Int) = v % (m : Int) := by
    rw [Int.tmod_eq_emod_of_nonneg (by omega), Int.add_emod_right, Int.tmod_def, Int.sub_eq_add_neg]
    have : -((m : Int) * v.tdiv (m : Int)) = (m : Int) * (-(v.tdiv (m : Int))) := by rw [Int.mul_neg]
    rw [this, Int.add_mul_emod_self_left]
  rw [show newEv m i = .cast u32 (.divrem s64 true (.binary s64 .add (.divrem s64 true (.variable s64 i) (castM64 m))
    (castM64 m)) (castM64 m)) from rfl]
  rw [den_cast, den_divrem, den_binary, den_divrem, den_variable, h0, castM64_value env m hm2]
  simp only [Option.bind_some]
  rw [checkedDivRem_remainder_exact s64 _ _ hM hq hr]
  simp only [Option.bind_some]
  rw [binaryValue, convert_s64 _ (by omega) (by omega)]
  simp only [Option.bind_some]
  rw [checkedDivRem_remainder_exact s64 _ _ hM hq2 hr2, fin]
  simp only [Option.bind_some]
  have hlt : v % (m : Int) < 4294967296 := by have := Int.emod_lt_of_pos v (show (0 : Int) < (m : Int) by omega); omega
  have hge : 0 ≤ v % (m : Int) := Int.emod_nonneg v hM
  rw [convert_u32]
  congr 1
  omega


theorem exec_ret (fu : Nat) (ps : PS) (e : NExpr) (v : Int) (hv : e.denote (penv ps) = some v) :
    pexec fu (.sequence (.primitive (.ret e)) Sk) ps = some ⟨ps,some v,e.nodes+1,ps.mem.length+ps.bs.length+e.nodes+2⟩ := by
  have pr := pstmt_ret_ok ps e v hv
  exact seq_ret (v := v) (by rw [pexec_prim, pr]) rfl

abbrev eqXY : NExpr := .binary bl .eq (.variable u32 0) (.variable u32 1)
abbrev neXY : NExpr := .binary bl .ne (.variable u32 0) (.variable u32 1)

theorem eqXY_value (env : Nat → Ty → Option Int) (x y : Nat) (h0 : env 0 u32 = some (x : Int)) (h1 : env 1 u32 = some (y : Int)) :
    eqXY.denote env = some (if x = y then 1 else 0) := by
  rw [den_binary, den_variable, den_variable, h0, h1]
  simp only [Option.bind_some, binaryValue, convert_bl]
  by_cases c : x = y
  · subst c; simp
  · have : ((x : Int) == (y : Int)) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
    simp [this, c]

theorem neXY_value (env : Nat → Ty → Option Int) (x y : Nat) (h0 : env 0 u32 = some (x : Int)) (h1 : env 1 u32 = some (y : Int)) :
    neXY.denote env = some (if x = y then 0 else 1) := by
  rw [den_binary, den_variable, den_variable, h0, h1]
  simp only [Option.bind_some, binaryValue, convert_bl]
  by_cases c : x = y
  · subst c; simp
  · have : ((x : Int) != (y : Int)) = true := by simp; omega
    simp [this, c]

theorem eq_exec (m : Nat) (P : List Cell) (a b x y : Nat) (hx : x < m) (hy : y < m) (hm : m < 4294967296)
    (ha : P[a]? = some ⟨u32,(x : Int)⟩) (hb : P[b]? = some ⟨u32,(y : Int)⟩) :
    ∃ r, pexec 1 (Proofs.ModIntInstance.ModInt_eq m).body ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = some (if x = y then 1 else 0) ∧ r.cost ≤ 10 ∧ r.need ≤ P.length+16 ∧ r.ps = ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ := by
  have e0 : penv ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ 0 u32 = some (x : Int) :=
    penv_ok _ 0 u32 ⟨a,false⟩ ⟨u32,(x : Int)⟩ rfl ha rfl (u32_valid_nat x (by omega))
  have e1 : penv ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ 1 u32 = some (y : Int) :=
    penv_ok _ 1 u32 ⟨b,false⟩ ⟨u32,(y : Int)⟩ rfl hb rfl (u32_valid_nat y (by omega))
  have q := exec_ret 1 _ eqXY _ (eqXY_value _ x y e0 e1)
  refine ⟨_,q,rfl,?_,?_,rfl⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes]

theorem ne_exec (m : Nat) (P : List Cell) (a b x y : Nat) (hx : x < m) (hy : y < m) (hm : m < 4294967296)
    (ha : P[a]? = some ⟨u32,(x : Int)⟩) (hb : P[b]? = some ⟨u32,(y : Int)⟩) :
    ∃ r, pexec 1 (Proofs.ModIntInstance.ModInt_ne m).body ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ = some r ∧
      r.ret = some (if x = y then 0 else 1) ∧ r.cost ≤ 10 ∧ r.need ≤ P.length+16 ∧ r.ps = ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ := by
  have e0 : penv ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ 0 u32 = some (x : Int) :=
    penv_ok _ 0 u32 ⟨a,false⟩ ⟨u32,(x : Int)⟩ rfl ha rfl (u32_valid_nat x (by omega))
  have e1 : penv ⟨P,[⟨a,false⟩,⟨b,false⟩]⟩ 1 u32 = some (y : Int) :=
    penv_ok _ 1 u32 ⟨b,false⟩ ⟨u32,(y : Int)⟩ rfl hb rfl (u32_valid_nat y (by omega))
  have q := exec_ret 1 _ neXY _ (neXY_value _ x y e0 e1)
  refine ⟨_,q,rfl,?_,?_,rfl⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes]

theorem get_exec (m : Nat) (P : List Cell) (a x : Nat) (hx : x < m) (hm : m < 4294967296)
    (ha : P[a]? = some ⟨u32,(x : Int)⟩) :
    ∃ r, pexec 1 (Proofs.ModIntInstance.ModInt_get m).body ⟨P,[⟨a,false⟩]⟩ = some r ∧
      r.ret = some (x : Int) ∧ r.cost ≤ 10 ∧ r.need ≤ P.length+16 ∧ r.ps = ⟨P,[⟨a,false⟩]⟩ := by
  have e0 : penv ⟨P,[⟨a,false⟩]⟩ 0 u32 = some (x : Int) :=
    penv_ok _ 0 u32 ⟨a,false⟩ ⟨u32,(x : Int)⟩ rfl ha rfl (u32_valid_nat x (by omega))
  have q := exec_ret 1 _ (.variable u32 0) _ (by rw [den_variable]; exact e0)
  refine ⟨_,q,rfl,?_,?_,rfl⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes]

theorem new0_exec (m : Nat) (P : List Cell) :
    ∃ r, pexec 1 (Proofs.ModIntInstance.ModInt_new0 m).body ⟨P,[]⟩ = some r ∧
      r.ret = some 0 ∧ r.cost ≤ 10 ∧ r.need ≤ P.length+16 ∧ r.ps = ⟨P,[]⟩ := by
  have q := exec_ret 1 ⟨P,[]⟩ (castE 0) ((0 : Nat) : Int) (castE_value _ 0 (by omega))
  refine ⟨_,q,rfl,?_,?_,rfl⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes]


theorem newE_value (env : Nat → Ty → Option Int) (m : Nat) (v : Int) (hm : 0 < m) (hm2 : m < 4294967296)
    (hv : s64.valid v = true) (h0 : env 0 s64 = some v) : (newE m).denote env = some (v % (m : Int)) :=
  newEv_value env m 0 v hm hm2 hv h0

set_option maxHeartbeats 2000000 in
theorem new1_exec (m : Nat) (hm : 0 < m) (hm2 : m < 4294967296) (P : List Cell) (v : Int) (hv : s64.valid v = true) :
    ∃ r, pexec 1 (Proofs.ModIntInstance.ModInt_new1 m).body ⟨P ++ [⟨s64,v⟩],[⟨P.length,true⟩]⟩ = some r ∧
      r.ret = some (v % (m : Int)) ∧ r.cost ≤ 30 ∧ r.need ≤ P.length+40 ∧ r.ps = ⟨P ++ [⟨s64,v⟩],[⟨P.length,true⟩]⟩ := by
  have body_eq : (Proofs.ModIntInstance.ModInt_new1 m).body = .sequence (.primitive (.ret (newE m))) Sk := rfl
  have e0 : penv ⟨P ++ [⟨s64,v⟩],[⟨P.length,true⟩]⟩ 0 s64 = some v :=
    penv_ok _ 0 s64 ⟨P.length,true⟩ ⟨s64,v⟩ rfl (by simpa using get_tail P [⟨s64,v⟩] 0) rfl hv
  have d := newE_value (penv ⟨P ++ [⟨s64,v⟩],[⟨P.length,true⟩]⟩) m v hm hm2 hv e0
  have q := exec_ret 1 ⟨P ++ [⟨s64,v⟩],[⟨P.length,true⟩]⟩ (newE m) _ d
  rw [body_eq]
  refine ⟨_,q,rfl,?_,?_,rfl⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes]

end Proofs.ModIntExec
