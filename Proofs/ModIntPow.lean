import Proofs.ModIntExec

namespace Proofs.ModIntPow
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.StraightLine Proofs.PowModStep
open Proofs.IntSim Proofs.PexecKit Proofs.QuotientSearch Proofs.DoublingNested Proofs.Mod61Body Proofs.ModIntExec
open Proofs.CppState (Cell)

abbrev mulS (m i j : Nat) : NExpr := .cast u32 (.divrem u64 true (.binary u64 .mul (.cast u64 (.variable u32 i))
  (.cast u64 (.variable u32 j))) (.cast u64 (.literal u32 (m : Int))))

theorem mulS_value (env : Nat → Ty → Option Int) (m i j x y : Nat) (hm : 0 < m) (hm2 : m < 4294967296)
    (hx : x < m) (hy : y < m) (h0 : env i u32 = some (x : Int)) (h1 : env j u32 = some (y : Int)) :
    (mulS m i j).denote env = some ((x * y % m : Nat) : Int) := by
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

abbrev loopCond : NExpr := .cast bl (.variable u64 1)
abbrev oddCond : NExpr := .cast bl (.binary u64 .band (.variable u64 1) (.cast u64 (.literal i32 1)))
abbrev shrN : NExpr := .binary u64 .shr (.variable u64 1) (.literal i32 1)

theorem loopCond_value (env : Nat → Ty → Option Int) (n : Nat) (h : env 1 u64 = some (n : Int)) :
    loopCond.denote env = some (if n = 0 then 0 else 1) := by
  rw [den_cast, den_variable, h]
  simp only [Option.bind_some, convert_bl]
  by_cases c : n = 0
  · subst c; simp
  · have : ((n : Int) == 0) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; omega
    simp [this, c]

theorem oddCond_value (env : Nat → Ty → Option Int) (n : Nat) (hn : n < 18446744073709551616)
    (h : env 1 u64 = some (n : Int)) : oddCond.denote env = some (if n % 2 = 0 then 0 else 1) := by
  have l1 : i32.valid 1 = true := by simp [Ty.valid]
  have b : u64.valid ((n % 2 : Nat) : Int) = true := u64_lt _ (by have := Nat.mod_le n 2; omega)
  have c1 : u64.convert 1 = some 1 := Ty.convert_of_valid _ _ (by simp [Ty.valid])
  rw [den_cast, den_binary, den_variable, h, den_cast, den_literal, if_pos l1]
  simp only [Option.bind_some]
  rw [c1]
  simp only [Option.bind_some, binaryValue, Int.toNat_natCast]
  have hb : (1 : Int).toNat = 1 := rfl
  simp only [hb, Nat.and_one_is_mod]
  rw [Ty.convert_of_valid _ _ b]
  simp only [Option.bind_some, convert_bl]
  rcases Nat.mod_two_eq_zero_or_one n with z | z
  · rw [z]; simp
  · rw [z]; simp

theorem shrN_value (env : Nat → Ty → Option Int) (n : Nat) (hn : n < 18446744073709551616)
    (h : env 1 u64 = some (n : Int)) : shrN.denote env = some ((n / 2 : Nat) : Int) := by
  have v : u64.valid ((n / 2 : Nat) : Int) = true := u64_lt _ (by have := Nat.div_le_self n 2; omega)
  have lit : i32.valid 1 = true := by simp [Ty.valid]
  rw [den_binary, den_variable, h]
  simp only [Option.bind_some, NExpr.denote, lit, ite_true, binaryValue, Int.toNat_natCast, Nat.shiftRight_eq_div_pow]
  simpa using Ty.convert_of_valid _ _ v


def cells (n y r c : Nat) : List Cell :=
  [⟨u64,(n : Int)⟩,⟨u32,(y : Int)⟩,⟨s64,1⟩,⟨u32,(c : Int)⟩,⟨u32,(r : Int)⟩]

def binds (a pl : Nat) : List CppState.Binding :=
  [⟨a,false⟩,⟨pl,true⟩,⟨pl+1,true⟩,⟨pl+2,true⟩,⟨pl+3,true⟩,⟨pl+4,true⟩]

def pstate (P : List Cell) (a n y r c : Nat) : PS := ⟨P ++ cells n y r c, binds a P.length⟩

theorem pstate_size (P : List Cell) (a n y r c : Nat) :
    (pstate P a n y r c).mem.length + (pstate P a n y r c).bs.length = P.length + 11 := by
  simp [pstate, cells, binds]

theorem mem_n (P : List Cell) (a n y r c : Nat) : (pstate P a n y r c).mem[P.length]? = some ⟨u64,(n : Int)⟩ := by
  have := get_tail P (cells n y r c) 0
  simpa [pstate, cells] using this

theorem mem_y (P : List Cell) (a n y r c : Nat) : (pstate P a n y r c).mem[P.length + 1]? = some ⟨u32,(y : Int)⟩ := by
  have := get_tail P (cells n y r c) 1
  exact this.trans rfl

theorem mem_r (P : List Cell) (a n y r c : Nat) : (pstate P a n y r c).mem[P.length + 4]? = some ⟨u32,(r : Int)⟩ := by
  have := get_tail P (cells n y r c) 4
  exact this.trans rfl

theorem env_x (P : List Cell) (a x n y r c : Nat) (hx : x < 4294967296) (ha : P[a]? = some ⟨u32,(x : Int)⟩) (hlt : a < P.length) :
    penv (pstate P a n y r c) 0 u32 = some (x : Int) := by
  refine penv_ok _ 0 u32 ⟨a,false⟩ ⟨u32,(x : Int)⟩ rfl ?_ rfl (u32_valid_nat x hx)
  show (P ++ cells n y r c)[a]? = _
  rw [List.getElem?_append_left hlt]; exact ha

theorem env_n (P : List Cell) (a n y r c : Nat) (hn : n < 18446744073709551616) :
    penv (pstate P a n y r c) 1 u64 = some (n : Int) := by
  refine penv_ok _ 1 u64 ⟨P.length,true⟩ ⟨u64,(n : Int)⟩ rfl ?_ rfl (u64_lt n hn)
  exact mem_n P a n y r c

theorem env_y (P : List Cell) (a n y r c : Nat) (hy : y < 4294967296) :
    penv (pstate P a n y r c) 2 u32 = some (y : Int) := by
  refine penv_ok _ 2 u32 ⟨P.length+1,true⟩ ⟨u32,(y : Int)⟩ rfl ?_ rfl (u32_valid_nat y hy)
  exact mem_y P a n y r c

theorem env_r (P : List Cell) (a n y r c : Nat) (hr : r < 4294967296) :
    penv (pstate P a n y r c) 5 u32 = some (r : Int) := by
  refine penv_ok _ 5 u32 ⟨P.length+4,true⟩ ⟨u32,(r : Int)⟩ rfl ?_ rfl (u32_valid_nat r hr)
  exact mem_r P a n y r c

theorem assign_n (P : List Cell) (a n y r c : Nat) (hn : n < 18446744073709551616) (e : NExpr) (n' : Nat)
    (hn' : n' < 18446744073709551616) (d : e.denote (penv (pstate P a n y r c)) = some (n' : Int)) :
    pstmt (.assign 1 u64 e) (pstate P a n y r c) =
      some ⟨pstate P a n' y r c,none,e.nodes+1,P.length+11+e.nodes+2⟩ := by
  have h := pstmt_assign_ok (pstate P a n y r c) 1 u64 e (n' : Int) d ⟨P.length,true⟩ ⟨u64,(n : Int)⟩ rfl
    (mem_n P a n y r c) rfl (u64_lt n hn) rfl _ (Ty.convert_of_valid _ _ (u64_lt n' hn'))
  rw [h, pstate_size]
  simp only [pstate, cells]
  rw [List.set_append_right _ _ (by omega)]
  simp

theorem assign_y (P : List Cell) (a n y r c : Nat) (hy : y < 4294967296) (e : NExpr) (y' : Nat)
    (hy' : y' < 4294967296) (d : e.denote (penv (pstate P a n y r c)) = some (y' : Int)) :
    pstmt (.assign 2 u32 e) (pstate P a n y r c) =
      some ⟨pstate P a n y' r c,none,e.nodes+1,P.length+11+e.nodes+2⟩ := by
  have h := pstmt_assign_ok (pstate P a n y r c) 2 u32 e (y' : Int) d ⟨P.length+1,true⟩ ⟨u32,(y : Int)⟩ rfl
    (mem_y P a n y r c) rfl (u32_valid_nat y hy) rfl _ (convert32 y' hy')
  rw [h, pstate_size]
  simp only [pstate, cells]
  rw [List.set_append_right _ _ (by omega)]
  simp

theorem assign_r (P : List Cell) (a n y r c : Nat) (hr : r < 4294967296) (e : NExpr) (r' : Nat)
    (hr' : r' < 4294967296) (d : e.denote (penv (pstate P a n y r c)) = some (r' : Int)) :
    pstmt (.assign 5 u32 e) (pstate P a n y r c) =
      some ⟨pstate P a n y r' c,none,e.nodes+1,P.length+11+e.nodes+2⟩ := by
  have h := pstmt_assign_ok (pstate P a n y r c) 5 u32 e (r' : Int) d ⟨P.length+4,true⟩ ⟨u32,(r : Int)⟩ rfl
    (mem_r P a n y r c) rfl (u32_valid_nat r hr) rfl _ (convert32 r' hr')
  rw [h, pstate_size]
  simp only [pstate, cells]
  rw [List.set_append_right _ _ (by omega)]
  simp


abbrev oddThen (m : Nat) : Command := .sequence (.scope (.sequence (.primitive (.assign 5 u32 (mulS m 5 2))) Sk)) Sk
abbrev powBody (m : Nat) : Command :=
  .sequence (.scope (.sequence (.branch oddCond (oddThen m) Sk)
    (.sequence (.primitive (.assign 2 u32 (mulS m 2 2))) (.sequence (.primitive (.assign 1 u64 shrN)) Sk)))) Sk

abbrev powTail (m : Nat) : Command :=
  .sequence (.primitive (.assign 2 u32 (mulS m 2 2))) (.sequence (.primitive (.assign 1 u64 shrN)) Sk)

theorem tail_exec (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (P : List Cell) (a n y r c : Nat)
    (hy : y < m) (hn : n < 18446744073709551616) (fu : Nat) :
    ∃ r2, pexec fu (powTail m) (pstate P a n y r c) = some r2 ∧
      r2.ps = pstate P a (n / 2) (y * y % m) r c ∧ r2.ret = none ∧ r2.cost ≤ 30 ∧ r2.need ≤ P.length + 30 := by
  have ey := env_y P a n y r c (by omega)
  have hyy : y * y % m < m := Nat.mod_lt _ (by omega)
  have hn2 : n / 2 < 18446744073709551616 := by have := Nat.div_le_self n 2; omega
  have dy := mulS_value (penv (pstate P a n y r c)) m 2 2 y y (by omega) hm2 hy hy ey ey
  have s1 := assign_y P a n y r c (by omega) (mulS m 2 2) (y * y % m) (by omega) dy
  have q1 : pexec fu (.primitive (.assign 2 u32 (mulS m 2 2))) (pstate P a n y r c) =
      some ⟨pstate P a n (y * y % m) r c,none,(mulS m 2 2).nodes+1,P.length+11+(mulS m 2 2).nodes+2⟩ := by
    rw [pexec_prim, s1]
  have en := env_n P a n (y * y % m) r c hn
  have dn := shrN_value (penv (pstate P a n (y * y % m) r c)) n hn en
  have s2 := assign_n P a n (y * y % m) r c hn shrN (n / 2) hn2 dn
  have q2 : pexec fu (.primitive (.assign 1 u64 shrN)) (pstate P a n (y * y % m) r c) =
      some ⟨pstate P a (n / 2) (y * y % m) r c,none,shrN.nodes+1,P.length+11+shrN.nodes+2⟩ := by
    rw [pexec_prim, s2]
  have q3 := seq_some q2 rfl (pexec_skip fu (pstate P a (n / 2) (y * y % m) r c))
  have q4 := seq_some q1 rfl q3
  refine ⟨_,q4,rfl,rfl,?_,?_⟩
  · simp [NExpr.nodes]
  · simp [NExpr.nodes, pstate_size]


theorem pstate_lens (P : List Cell) (a n y r c n' y' r' c' : Nat) :
    (pstate P a n' y' r' c').mem.length = (pstate P a n y r c).mem.length ∧
    (pstate P a n' y' r' c').bs.length = (pstate P a n y r c).bs.length := by
  simp [pstate, cells, binds]

theorem pow_iter (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (P : List Cell) (a x n y r c : Nat)
    (hx : x < m) (hy : y < m) (hr : r < m) (hn : n < 18446744073709551616)
    (ha : P[a]? = some ⟨u32,(x : Int)⟩) (hlt : a < P.length) (fu : Nat) :
    ∃ r1, pexec fu (powBody m) (pstate P a n y r c) = some r1 ∧
      r1.ps = pstate P a (n / 2) (y * y % m) (if n % 2 = 0 then r else r * y % m) c ∧ r1.ret = none ∧
      r1.cost ≤ 70 ∧ r1.need ≤ P.length + 40 := by
  have en := env_n P a n y r c hn
  have er := env_r P a n y r c (by omega)
  have ey := env_y P a n y r c (by omega)
  have dc := oddCond_value (penv (pstate P a n y r c)) n hn en
  have hry : r * y % m < m := Nat.mod_lt _ (by omega)
  -- the branch, then the tail in the state it leaves, inside the loop body's scope
  have key : ∀ (r' : Nat) (hr' : r' < m) (br : PR), pexec fu (.branch oddCond (oddThen m) Sk) (pstate P a n y r c) = some br →
      br.ret = none → br.ps = pstate P a n y r' c → br.cost ≤ 30 → br.need ≤ P.length + 30 →
      ∃ r1, pexec fu (powBody m) (pstate P a n y r c) = some r1 ∧ r1.ps = pstate P a (n / 2) (y * y % m) r' c ∧
        r1.ret = none ∧ r1.cost ≤ 70 ∧ r1.need ≤ P.length + 40 := by
    intro r' hr' br hbr hret hps hcost hneed
    obtain ⟨r2,h2,h2ps,h2ret,h2cost,h2need⟩ := tail_exec m hm hm2 P a n y r' c hy hn fu
    rw [← hps] at h2
    have q1 := seq_some hbr hret h2
    have hl := pstate_lens P a n y r c (n / 2) (y * y % m) r' c
    have q2 := pexec_scope fu _ (pstate P a n y r c) _ q1
    rw [h2ps] at q2
    have q3 := scope_take (pstate P a n y r c) (pstate P a (n / 2) (y * y % m) r' c) hl.1 hl.2
    simp only [q3] at q2
    have q4 := seq_some q2 (by simpa using h2ret) (pexec_skip fu (pstate P a (n / 2) (y * y % m) r' c))
    refine ⟨_,q4,rfl,by simpa using h2ret,?_,?_⟩
    · simp; omega
    · simp [pstate_size]; omega
  rcases Nat.mod_two_eq_zero_or_one n with z | z
  · have d0 : oddCond.denote (penv (pstate P a n y r c)) = some 0 := by rw [dc]; simp [z]
    have qb := pexec_branch_false fu oddCond (oddThen m) Sk _ d0 _ (pexec_skip fu _)
    obtain ⟨r1,h1,h2,h3,h4,h5⟩ := key r hr _ qb rfl rfl (by simp [NExpr.nodes]) (by simp [NExpr.nodes, pstate_size])
    refine ⟨r1,h1,?_,h3,h4,h5⟩
    simp [z, h2]
  · have d1 : oddCond.denote (penv (pstate P a n y r c)) = some 1 := by rw [dc]; simp [z]
    have dm := mulS_value (penv (pstate P a n y r c)) m 5 2 r y (by omega) hm2 hr hy er ey
    have s1 := assign_r P a n y r c (by omega) (mulS m 5 2) (r * y % m) (by omega) dm
    have br := pexec_braced fu (.assign 5 u32 (mulS m 5 2)) (pstate P a n y r c) _ s1 rfl
      (pstate_lens P a n y r c n y (r * y % m) c).1 (pstate_lens P a n y r c n y (r * y % m) c).2
    have qb := pexec_branch_true fu oddCond (oddThen m) Sk _ 1 d1 (by decide) _ br
    obtain ⟨r1,h1,h2,h3,h4,h5⟩ := key (r * y % m) hry _ qb rfl rfl (by simp [NExpr.nodes, pstate_size]) (by simp [NExpr.nodes, pstate_size])
    refine ⟨r1,h1,?_,h3,h4,h5⟩
    have : ¬ n % 2 = 0 := by omega
    simp [this, h2]


abbrev powLoop (m : Nat) : Command := .whileLoop loopCond (powBody m)

theorem pow_loop (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (P : List Cell) (a x c : Nat) (hx : x < m)
    (ha : P[a]? = some ⟨u32,(x : Int)⟩) (hlt : a < P.length) :
    ∀ (k fu : Nat), k + 1 ≤ fu → ∀ (n y r : Nat), y < m → r < m → n < 2 ^ k → n < 18446744073709551616 →
      ∃ r1 yF, pexec fu (powLoop m) (pstate P a n y r c) = some r1 ∧
        r1.ps = pstate P a 0 yF (pw m k r y n) c ∧ yF < m ∧ r1.ret = none ∧ r1.cost ≤ 80 * k + 5 ∧
        r1.need ≤ P.length + 40 := by
  intro k
  induction k with
  | zero =>
    intro fu hfu n y r hy hr hn hn64
    obtain ⟨fu',rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1,by omega⟩
    have n0 : n = 0 := by simpa using hn
    subst n0
    have en := env_n P a 0 y r c (by omega)
    have hc := loopCond_value (penv (pstate P a 0 y r c)) 0 en
    have hc0 : loopCond.denote (penv (pstate P a 0 y r c)) = some 0 := by simpa using hc
    rw [pexec_while]
    simp only [Bind.bind, Option.bind, hc0, ite_true]
    refine ⟨_,y,rfl,?_,hy,rfl,?_,?_⟩
    · simp [pw]
    · simp [NExpr.nodes]
    · simp [NExpr.nodes, pstate_size]
  | succ k ih =>
    intro fu hfu n y r hy hr hn hn64
    obtain ⟨fu',rfl⟩ : ∃ fu', fu = fu'+1 := ⟨fu-1,by omega⟩
    have en := env_n P a n y r c hn64
    have hc := loopCond_value (penv (pstate P a n y r c)) n en
    by_cases z : n = 0
    · subst z
      have hc0 : loopCond.denote (penv (pstate P a 0 y r c)) = some 0 := by simpa using hc
      rw [pexec_while]
      simp only [Bind.bind, Option.bind, hc0, ite_true]
      refine ⟨_,y,rfl,?_,hy,rfl,?_,?_⟩
      · simp [pw]
      · simp [NExpr.nodes]
      · simp [NExpr.nodes, pstate_size]
    · have hc1 : loopCond.denote (penv (pstate P a n y r c)) = some 1 := by simpa [z] using hc
      have hz : n / 2 < 2 ^ k := by rw [Nat.pow_succ] at hn; omega
      obtain ⟨r1,hr1,hps,hret,hcost,hneed⟩ := pow_iter m hm hm2 P a x n y r c hx hy hr hn64 ha hlt (fu' + 1)
      have hy' : y * y % m < m := Nat.mod_lt _ (by omega)
      have hr' : (if n % 2 = 0 then r else r * y % m) < m := by
        split
        · exact hr
        · exact Nat.mod_lt _ (by omega)
      obtain ⟨r2,yF,hr2,hps2,hyF,hret2,hcost2,hneed2⟩ := ih fu' (by omega) (n / 2) (y * y % m)
        (if n % 2 = 0 then r else r * y % m) hy' hr' hz (by omega)
      rw [pexec_while]
      simp only [Bind.bind, Option.bind, hc1]
      simp only [int_one_ne, ite_false, hr1, hret]
      rw [hps, hr2]
      refine ⟨_,yF,rfl,?_,hyF,hret2,?_,?_⟩
      · rw [hps2]; simp [pw, z]
      · simp [NExpr.nodes] at *; omega
      · simp [NExpr.nodes, pstate_size] at *; omega


abbrev castOne : NExpr := .cast s64 (.literal i32 1)

theorem castOne_value (env : Nat → Ty → Option Int) : castOne.denote env = some 1 := by
  have l : i32.valid 1 = true := by simp [Ty.valid]
  rw [den_cast, den_literal, if_pos l, Option.bind_some]
  exact convert_s64 _ (by omega) (by omega)

theorem one_mod (m : Nat) (hm : 2 ≤ m) : (1 : Int) % (m : Int) = ((1 : Nat) : Int) := by
  have h1 : (1 : Int) < (m : Int) := by omega
  exact Int.emod_eq_of_lt (by omega) h1

def bsK (a pl k : Nat) : List CppState.Binding := ⟨a,false⟩ :: (List.range k).map fun j => ⟨pl + j,true⟩

def stK (P : List Cell) (a : Nat) (L : List Cell) : PS := ⟨P ++ L, bsK a P.length L.length⟩

theorem pstate_eq (P : List Cell) (a n y r c : Nat) : pstate P a n y r c = stK P a (cells n y r c) := by
  simp [pstate, stK, cells, binds, bsK, List.range_succ]

theorem stK_size (P L : List Cell) (a : Nat) : (stK P a L).mem.length + (stK P a L).bs.length = P.length + 2 * L.length + 1 := by
  simp [stK, bsK]; omega

theorem stK_env0 (P L : List Cell) (a x : Nat) (hx : x < 4294967296) (ha : P[a]? = some ⟨u32,(x : Int)⟩) (hlt : a < P.length) :
    penv (stK P a L) 0 u32 = some (x : Int) := by
  refine penv_ok _ 0 u32 ⟨a,false⟩ ⟨u32,(x : Int)⟩ rfl ?_ rfl (u32_valid_nat x hx)
  show (P ++ L)[a]? = _
  rw [List.getElem?_append_left hlt]; exact ha

theorem stK_envL (P L : List Cell) (a j : Nat) (cell : Cell) (ty : Ty) (hj : L[j]? = some cell) (ht : cell.type = ty)
    (hv : ty.valid cell.value = true) : penv (stK P a L) (j + 1) ty = some cell.value := by
  have hlt : j < L.length := (List.getElem?_eq_some_iff.mp hj).1
  refine penv_ok _ (j + 1) ty ⟨P.length + j,true⟩ cell ?_ ?_ ht hv
  · simp [stK, bsK, hlt]
  · show (P ++ L)[P.length + j]? = _
    rw [get_tail]; exact hj

theorem stK_declare (P L : List Cell) (a : Nat) (ty : Ty) (e : NExpr) (v : Int) (hv : e.denote (penv (stK P a L)) = some v)
    (hc : ty.convert v = some v) :
    pstmt (.declare ty true e) (stK P a L) =
      some ⟨stK P a (L ++ [⟨ty,v⟩]),none,e.nodes+1,P.length+2*L.length+1+e.nodes+4⟩ := by
  rw [pstmt_declare_ok _ ty true e v hv v hc]
  have hl : (stK P a L).mem.length = P.length + L.length := by simp [stK]
  have h1 : (stK P a L).mem ++ [⟨ty,v⟩] = (stK P a (L ++ [⟨ty,v⟩])).mem := by simp [stK]
  have h2 : (stK P a L).bs ++ [⟨(stK P a L).mem.length,true⟩] = (stK P a (L ++ [⟨ty,v⟩])).bs := by
    simp [stK, bsK, List.range_succ, hl, Nat.add_comm]
  have h3 := stK_size P L a
  rw [h1, h2]
  have : (stK P a L).mem.length + (stK P a L).bs.length + e.nodes + 4 = P.length + 2 * L.length + 1 + e.nodes + 4 := by omega
  rw [this]

abbrev powPre (m : Nat) (tail : Command) : Command :=
  .sequence (.primitive (.declare u32 true (.variable u32 0)))
    (.sequence (.primitive (.declare s64 true castOne))
      (.sequence (.primitive (.declare u32 true (newEv m 3)))
        (.sequence (.primitive (.declare u32 true (.variable u32 4))) (.sequence (powLoop m) tail))))

-- The copy of `*this`, the converted literal, the constructor value, `r`, the loop; then any tail.
theorem pow_pre_exec (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (P : List Cell) (a x n : Nat) (hx : x < m)
    (hn : n < 18446744073709551616) (ha : P[a]? = some ⟨u32,(x : Int)⟩) (hlt : a < P.length) (tail : Command)
    (ht : ∀ yF, yF < m → ∃ rt, pexec 70 tail (pstate P a 0 yF ((x ^ n) % m) 1) = some rt) :
    ∃ yF r1 rt, yF < m ∧ pexec 70 tail (pstate P a 0 yF ((x ^ n) % m) 1) = some rt ∧
      pexec 70 (powPre m tail) (stK P a [⟨u64,(n : Int)⟩]) = some r1 ∧
      r1.ps = rt.ps ∧ r1.ret = rt.ret ∧ r1.cost ≤ 80 * 64 + 40 + rt.cost ∧ r1.need ≤ max (P.length + 40) rt.need := by
  have hxv : x < 4294967296 := by omega
  let N : Cell := ⟨u64,(n : Int)⟩
  let X : Cell := ⟨u32,(x : Int)⟩
  let T : Cell := ⟨s64,1⟩
  let C : Cell := ⟨u32,((1 : Nat) : Int)⟩
  -- 1: y = *this
  have e1 := stK_env0 P [N] a x hxv ha hlt
  have s1 := stK_declare P [N] a u32 (.variable u32 0) (x : Int) (by rw [den_variable]; exact e1) (convert32 x hxv)
  have q1 : pexec 70 (.primitive (.declare u32 true (.variable u32 0))) (stK P a [N]) =
      some ⟨stK P a [N, X],none,(NExpr.variable u32 0).nodes+1,P.length+2*[N].length+1+(NExpr.variable u32 0).nodes+4⟩ := by
    rw [pexec_prim, s1]; rfl
  -- 2: the converted literal 1
  have s2 := stK_declare P [N, X] a s64 castOne 1 (castOne_value _) (convert_s64 _ (by omega) (by omega))
  have q2 : pexec 70 (.primitive (.declare s64 true castOne)) (stK P a [N, X]) =
      some ⟨stK P a [N, X, T],none,castOne.nodes+1,P.length+2*[N, X].length+1+castOne.nodes+4⟩ := by
    rw [pexec_prim, s2]; rfl
  -- 3: the constructor expression
  have e3 : penv (stK P a [N, X, T]) 3 s64 = some 1 :=
    stK_envL P [N, X, T] a 2 T s64 rfl rfl (s64_valid_of 1 (by omega) (by omega))
  have d3 := newEv_value (penv (stK P a [N, X, T])) m 3 1 (by omega) hm2 (s64_valid_of 1 (by omega) (by omega)) e3
  have c1 : (1 : Int) % (m : Int) = ((1 : Nat) : Int) := one_mod m hm
  rw [c1] at d3
  have s3 := stK_declare P [N, X, T] a u32 (newEv m 3) ((1 : Nat) : Int) d3 (convert32 1 (by omega))
  have q3 : pexec 70 (.primitive (.declare u32 true (newEv m 3))) (stK P a [N, X, T]) =
      some ⟨stK P a [N, X, T, C],none,(newEv m 3).nodes+1,P.length+2*[N, X, T].length+1+(newEv m 3).nodes+4⟩ := by
    rw [pexec_prim, s3]; rfl
  -- 4: r = the constructed value
  have e4 : penv (stK P a [N, X, T, C]) 4 u32 = some ((1 : Nat) : Int) :=
    stK_envL P [N, X, T, C] a 3 C u32 rfl rfl (u32_valid_nat 1 (by omega))
  have s4 := stK_declare P [N, X, T, C] a u32 (.variable u32 4) ((1 : Nat) : Int) (by rw [den_variable]; exact e4) (convert32 1 (by omega))
  have q4 : pexec 70 (.primitive (.declare u32 true (.variable u32 4))) (stK P a [N, X, T, C]) =
      some ⟨stK P a [N, X, T, C, C],none,(NExpr.variable u32 4).nodes+1,P.length+2*[N, X, T, C].length+1+(NExpr.variable u32 4).nodes+4⟩ := by
    rw [pexec_prim, s4]; rfl
  -- 5: the loop
  have hS4 : stK P a [N, X, T, C, C] = pstate P a n x 1 1 := by
    rw [pstate_eq]; rfl
  obtain ⟨rl, yF, hl, hlps, hyF, hlret, hlcost, hlneed⟩ :=
    pow_loop m hm hm2 P a x 1 hx ha hlt 64 70 (by omega) n x 1 hx (by omega) (by simpa using hn) hn
  rw [← hS4] at hl
  have hrF : pw m 64 1 x n = (x ^ n) % m := by
    have := pw_spec m (by omega) 64 1 x n (by simpa using hn) (by omega)
    simpa [Nat.one_mul] using this
  obtain ⟨rt, hrt⟩ := ht yF hyF
  have hrt' : pexec 70 tail rl.ps = some rt := by rw [hlps, hrF]; exact hrt
  have q5 := seq_some hl hlret hrt'
  have q6 := seq_some q4 rfl q5
  have q7 := seq_some q3 rfl q6
  have q8 := seq_some q2 rfl q7
  have q9 := seq_some q1 rfl q8
  refine ⟨yF,_,rt,hyF,hrt,q9,rfl,rfl,?_,?_⟩
  · simp [NExpr.nodes] at *; omega
  · simp [NExpr.nodes, pstate_size] at *; omega

theorem pow_exec (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (P : List Cell) (a x n : Nat) (hx : x < m)
    (hn : n < 18446744073709551616) (ha : P[a]? = some ⟨u32,(x : Int)⟩) (hlt : a < P.length) :
    ∃ r1 yF, pexec 70 (Proofs.ModIntInstance.ModInt_pow m).body ⟨P ++ [⟨u64,(n : Int)⟩],[⟨a,false⟩,⟨P.length,true⟩]⟩ = some r1 ∧
      r1.ret = some (((x ^ n) % m : Nat) : Int) ∧ r1.cost ≤ 80 * 64 + 50 ∧ r1.need ≤ P.length + 40 ∧
      r1.ps = pstate P a 0 yF ((x ^ n) % m) 1 := by
  have body_eq : (Proofs.ModIntInstance.ModInt_pow m).body = powPre m (.sequence (.primitive (.ret (.variable u32 5))) Sk) := rfl
  have hS0 : (⟨P ++ [⟨u64,(n : Int)⟩],[⟨a,false⟩,⟨P.length,true⟩]⟩ : PS) = stK P a [⟨u64,(n : Int)⟩] := by simp [stK, bsK]
  rw [body_eq, hS0]
  have hrlt : (x ^ n) % m < m := Nat.mod_lt _ (by omega)
  have hrlt2 : (x ^ n) % m < 4294967296 := by omega
  have ht : ∀ yF, yF < m → ∃ rt, pexec 70 (.sequence (.primitive (.ret (.variable u32 5))) Sk)
      (pstate P a 0 yF ((x ^ n) % m) 1) = some rt := by
    intro yF hy
    have er := env_r P a 0 yF ((x ^ n) % m) 1 hrlt2
    exact ⟨_,exec_ret 70 _ (.variable u32 5) _ (by rw [den_variable]; exact er)⟩
  obtain ⟨yF,r1,rt,hyF,hrt,hr1,hps,hret,hcost,hneed⟩ :=
    pow_pre_exec m hm hm2 P a x n hx hn ha hlt _ ht
  have er := env_r P a 0 yF ((x ^ n) % m) 1 hrlt2
  have hrt2 := exec_ret 70 (pstate P a 0 yF ((x ^ n) % m) 1) (.variable u32 5) _ (by rw [den_variable]; exact er)
  rw [hrt2] at hrt
  cases hrt
  refine ⟨r1,yF,hr1,?_,?_,?_,?_⟩
  · simp [hret]
  · simp [NExpr.nodes] at hcost ⊢; omega
  · simp [NExpr.nodes, pstate_size] at hneed ⊢; omega
  · simp [hps]


abbrev expE (m : Nat) : NExpr := .cast u64 (.binary u32 .sub (.literal u32 (m : Int)) (castE 2))

theorem expE_value (env : Nat → Ty → Option Int) (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) :
    (expE m).denote env = some ((m - 2 : Nat) : Int) := by
  rw [den_cast, den_binary, lit32_value env m hm2, castE_value env 2 (by omega)]
  simp only [Option.bind_some, binaryValue]
  have : (m : Int) - ((2 : Nat) : Int) = ((m - 2 : Nat) : Int) := by omega
  rw [this, convert32 _ (by omega)]
  simp only [Option.bind_some]
  exact Ty.convert_of_valid _ _ (u64_lt _ (by omega))

abbrev invTail : Command := .sequence (.primitive (.declare u32 true (.variable u32 5)))
  (.sequence (.primitive (.ret (.variable u32 6))) Sk)

theorem inv_exec (m : Nat) (hm : 2 ≤ m) (hm2 : m < 4294967296) (P : List Cell) (a x : Nat) (hx : x < m) (hx0 : x ≠ 0)
    (ha : P[a]? = some ⟨u32,(x : Int)⟩) (hlt : a < P.length) :
    ∃ r1, pexec 70 (Proofs.ModIntInstance.ModInt_inv m).body ⟨P,[⟨a,false⟩]⟩ = some r1 ∧
      r1.ret = some (((x ^ (m - 2)) % m : Nat) : Int) ∧ r1.cost ≤ 80 * 64 + 100 ∧ r1.need ≤ P.length + 60 ∧
      ∃ L, r1.ps.mem = P ++ L := by
  have hxv : x < 4294967296 := by omega
  have body_eq : (Proofs.ModIntInstance.ModInt_inv m).body =
      .sequence (.primitive (.check neZero)) (.sequence (.primitive (.declare u64 true (expE m)))
        (powPre m invTail)) := rfl
  have hS0 : (⟨P,[⟨a,false⟩]⟩ : PS) = stK P a [] := by simp [stK, bsK]
  rw [body_eq, hS0]
  -- the assertion
  have e0 := stK_env0 P [] a x hxv ha hlt
  have dz := neZero_value (penv (stK P a [])) x hxv e0
  have d1 : neZero.denote (penv (stK P a [])) = some 1 := by rw [dz]; simp [hx0]
  have pc : pstmt (.check neZero) (stK P a []) =
      some ⟨stK P a [],none,neZero.nodes+1,(stK P a []).mem.length+(stK P a []).bs.length+neZero.nodes+2⟩ := by
    simp only [pstmt, Bind.bind, Option.bind, d1]
    simp
  have q1 : pexec 70 (.primitive (.check neZero)) (stK P a []) =
      some ⟨stK P a [],none,neZero.nodes+1,(stK P a []).mem.length+(stK P a []).bs.length+neZero.nodes+2⟩ := by
    rw [pexec_prim, pc]
  -- n = m - 2
  have dn := expE_value (penv (stK P a [])) m hm hm2
  have s2 := stK_declare P [] a u64 (expE m) ((m - 2 : Nat) : Int) dn (Ty.convert_of_valid _ _ (u64_lt _ (by omega)))
  have q2 : pexec 70 (.primitive (.declare u64 true (expE m))) (stK P a []) =
      some ⟨stK P a [⟨u64,((m - 2 : Nat) : Int)⟩],none,(expE m).nodes+1,P.length+2*([] : List Cell).length+1+(expE m).nodes+4⟩ := by
    rw [pexec_prim, s2]
    rfl
  -- the power, then the tail
  have hrlt : (x ^ (m - 2)) % m < m := Nat.mod_lt _ (by omega)
  have hrlt2 : (x ^ (m - 2)) % m < 4294967296 := by omega
  have htfull : ∀ yF, yF < m → ∃ L rt, pexec 70 invTail (pstate P a 0 yF ((x ^ (m - 2)) % m) 1) = some rt ∧
      rt.ps = stK P a L ∧ rt.ret = some (((x ^ (m - 2)) % m : Nat) : Int) ∧ rt.cost ≤ 20 ∧ rt.need ≤ P.length + 40 := by
    intro yF hy
    have hst : pstate P a 0 yF ((x ^ (m - 2)) % m) 1 = stK P a (cells 0 yF ((x ^ (m - 2)) % m) 1) := pstate_eq _ _ _ _ _ _
    rw [hst]
    have e5 : penv (stK P a (cells 0 yF ((x ^ (m - 2)) % m) 1)) 5 u32 = some (((x ^ (m - 2)) % m : Nat) : Int) :=
      stK_envL P _ a 4 ⟨u32,(((x ^ (m - 2)) % m : Nat) : Int)⟩ u32 rfl rfl (u32_valid_nat _ hrlt2)
    have s3 := stK_declare P (cells 0 yF ((x ^ (m - 2)) % m) 1) a u32 (.variable u32 5) (((x ^ (m - 2)) % m : Nat) : Int)
      (by rw [den_variable]; exact e5) (convert32 _ hrlt2)
    have q3 : pexec 70 (.primitive (.declare u32 true (.variable u32 5))) (stK P a (cells 0 yF ((x ^ (m - 2)) % m) 1)) =
        some ⟨stK P a (cells 0 yF ((x ^ (m - 2)) % m) 1 ++ [⟨u32,(((x ^ (m - 2)) % m : Nat) : Int)⟩]),none,
          (NExpr.variable u32 5).nodes+1,P.length+2*(cells 0 yF ((x ^ (m - 2)) % m) 1).length+1+(NExpr.variable u32 5).nodes+4⟩ := by
      rw [pexec_prim, s3]
    have e6 : penv (stK P a (cells 0 yF ((x ^ (m - 2)) % m) 1 ++ [⟨u32,(((x ^ (m - 2)) % m : Nat) : Int)⟩])) 6 u32 =
        some (((x ^ (m - 2)) % m : Nat) : Int) :=
      stK_envL P _ a 5 ⟨u32,(((x ^ (m - 2)) % m : Nat) : Int)⟩ u32 rfl rfl (u32_valid_nat _ hrlt2)
    have q4 := exec_ret 70 (stK P a (cells 0 yF ((x ^ (m - 2)) % m) 1 ++ [⟨u32,(((x ^ (m - 2)) % m : Nat) : Int)⟩])) (.variable u32 6) _
      (by rw [den_variable]; exact e6)
    refine ⟨_,_,seq_some q3 rfl q4,rfl,rfl,?_,?_⟩
    · simp [NExpr.nodes]
    · simp [NExpr.nodes, stK_size, cells]
  have ht : ∀ yF, yF < m → ∃ rt, pexec 70 invTail (pstate P a 0 yF ((x ^ (m - 2)) % m) 1) = some rt := by
    intro yF hy
    obtain ⟨L,rt,h,_⟩ := htfull yF hy
    exact ⟨rt,h⟩
  have hn : m - 2 < 18446744073709551616 := by omega
  obtain ⟨yF,r1,rt,hyF,hrt,hr1,hps,hret,hcost,hneed⟩ :=
    pow_pre_exec m hm hm2 P a x (m - 2) hx hn ha hlt invTail ht
  obtain ⟨L,rt',hrt',hrtps,hrtret,hrtcost,hrtneed⟩ := htfull yF hyF
  rw [hrt'] at hrt
  cases hrt
  have q5 := seq_some q2 rfl hr1
  have q6 := seq_some q1 rfl q5
  refine ⟨_,q6,?_,?_,?_,L,?_⟩
  · simp [hret, hrtret]
  · simp [NExpr.nodes, stK, bsK] at *; omega
  · simp [NExpr.nodes, stK, bsK] at *; omega
  · simp [hps, hrtps, stK]

end Proofs.ModIntPow
