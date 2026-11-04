import Proofs.ScalarRefs
import Proofs.ShiftN
import Proofs.GcdU64Call
import Proofs.Generated.Ratio

namespace Proofs.RatioCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.PowModStep Proofs.StraightLine
open Proofs.QuotientSearch Proofs.Mod61Body Proofs.DoublingNested Proofs.PexecKit Proofs.ShiftN Proofs.IntervalCall
open Proofs.GcdU64Call
open Proofs.CppState (Cell)

/-- The state `mk P vs` with the bindings `B` in front. -/
def shPS (B : List CppState.Binding) (ps : PS) : PS := ⟨ps.mem, B ++ ps.bs⟩

abbrev nB (a0 a1 a2 : Nat) : List CppState.Binding := [⟨a0,false⟩,⟨a1,false⟩,⟨a2,false⟩]

theorem cmp0_value (op : Binary) (hop : op = .ne ∨ op = .eq) (i : Nat) (env : Nat → Ty → Option Int) (b : Nat)
    (h1 : env i u64 = some (b : Int)) :
    (NExpr.binary bl op (.variable u64 i) c0E).denote env =
      some (if (op = .eq) = (b = 0) then 1 else 0) := by
  rw [den_binary,den_variable,h1,c0_value]
  simp only [Option.bind_some,binaryValue]
  rcases hop with rfl | rfl
  · by_cases z : b = 0
    · subst z; simpa using Ty.convert_of_valid bl 0 (by simp [Ty.valid])
    · have : ((b : Int) != 0) = true := by simp [z]
      simp only [this,if_true,z]
      simpa using Ty.convert_of_valid bl 1 (by simp [Ty.valid])
  · by_cases z : b = 0
    · subst z; simpa using Ty.convert_of_valid bl 1 (by simp [Ty.valid])
    · have : ((b : Int) == 0) = false := by simp [z]
      simp only [this,z]
      simpa using Ty.convert_of_valid bl 0 (by simp [Ty.valid])


abbrev normCmd (retZ retM : NExpr) : Command :=
  .sequence (.primitive (.check (.binary bl .ne (.variable u64 2) c0E)))
  (.sequence (.primitive (.declare u64 true (.variable u64 1)))
  (.sequence (.primitive (.declare u64 true (.variable u64 2)))
  (.sequence (gLoop.shN 3)
  (.sequence (.branch (.binary bl .eq (.variable u64 1) c0E)
      (.sequence (.scope (.sequence (.primitive (.ret retZ)) Sk)) Sk) Sk)
  (.sequence (.primitive (.ret retM)) Sk)))))

theorem norm_s_body : Proofs.RatioInstance.Ratio_normalize_s.body =
    normCmd c0E (.variable u64 0) := rfl
theorem norm_n_body : Proofs.RatioInstance.Ratio_normalize_n.body =
    normCmd c0E (.divrem u64 false (.variable u64 1) (.variable u64 3)) := rfl
theorem norm_d_body : Proofs.RatioInstance.Ratio_normalize_d.body =
    normCmd c1E (.divrem u64 false (.variable u64 2) (.variable u64 3)) := rfl


theorem refs_env (P : List Cell) (a0 a1 a2 : Nat) (s n d : Nat) (hs : s < 18446744073709551616)
    (hn : n < 18446744073709551616) (hd : d < 18446744073709551616)
    (h0 : P[a0]? = some ⟨u64,(s : Int)⟩) (h1 : P[a1]? = some ⟨u64,(n : Int)⟩) (h2 : P[a2]? = some ⟨u64,(d : Int)⟩)
    (mem : List Cell) (Y : List CppState.Binding) (L : List Cell) (hm : mem = P ++ L) :
    penv ⟨mem, nB a0 a1 a2 ++ Y⟩ 0 u64 = some (s : Int) ∧ penv ⟨mem, nB a0 a1 a2 ++ Y⟩ 1 u64 = some (n : Int) ∧
      penv ⟨mem, nB a0 a1 a2 ++ Y⟩ 2 u64 = some (d : Int) := by
  subst hm
  have l0 : a0 < P.length := (List.getElem?_eq_some_iff.mp h0).1
  have l1 : a1 < P.length := (List.getElem?_eq_some_iff.mp h1).1
  have l2 : a2 < P.length := (List.getElem?_eq_some_iff.mp h2).1
  refine ⟨?_, ?_, ?_⟩
  · refine penv_ok _ 0 u64 ⟨a0,false⟩ ⟨u64,(s : Int)⟩ rfl ?_ rfl (u64_lt _ hs)
    show (P ++ L)[a0]? = _
    rw [List.getElem?_append_left l0]; exact h0
  · refine penv_ok _ 1 u64 ⟨a1,false⟩ ⟨u64,(n : Int)⟩ rfl ?_ rfl (u64_lt _ hn)
    show (P ++ L)[a1]? = _
    rw [List.getElem?_append_left l1]; exact h1
  · refine penv_ok _ 2 u64 ⟨a2,false⟩ ⟨u64,(d : Int)⟩ rfl ?_ rfl (u64_lt _ hd)
    show (P ++ L)[a2]? = _
    rw [List.getElem?_append_left l2]; exact h2


theorem norm_exec (P : List Cell) (a0 a1 a2 : Nat) (s n d : Nat) (hs : s < 18446744073709551616)
    (hn : n < 18446744073709551616) (hd : d < 18446744073709551616) (hd0 : d ≠ 0)
    (h0 : P[a0]? = some ⟨u64,(s : Int)⟩) (h1 : P[a1]? = some ⟨u64,(n : Int)⟩) (h2 : P[a2]? = some ⟨u64,(d : Int)⟩)
    (fu : Nat) (hfu : gsteps n d + 1 ≤ fu) (retZ retM : NExpr) (z m : Int) (hzn : retZ.nodes ≤ 10) (hmn : retM.nodes ≤ 10)
    (hZ : n = 0 → retZ.denote (penv (shPS (nB a0 a1 a2) (mk P [Nat.gcd n d, 0]))) = some z)
    (hM : n ≠ 0 → retM.denote (penv (shPS (nB a0 a1 a2) (mk P [Nat.gcd n d, 0]))) = some m) :
    ∃ r : PR, pexec fu (normCmd retZ retM) ⟨P, nB a0 a1 a2⟩ = some r ∧ r.ret = some (if n = 0 then z else m) ∧
      r.cost ≤ 40 * gsteps n d + 100 ∧ r.need ≤ P.length + 40 ∧ ∃ L, r.ps.mem = P ++ L := by
  have E := fun (mem : List Cell) (Y : List CppState.Binding) (L : List Cell) (hm : mem = P ++ L) =>
    refs_env P a0 a1 a2 s n d hs hn hd h0 h1 h2 mem Y L hm
  -- the check
  have E0 := E P [] [] (by simp)
  have cD := cmp0_value .ne (Or.inl rfl) 2 (penv ⟨P, nB a0 a1 a2 ++ []⟩) d E0.2.2
  have cD' : (NExpr.binary bl .ne (.variable u64 2) c0E).denote (penv ⟨P, nB a0 a1 a2⟩) = some 1 := by
    simpa [hd0] using cD
  have s1 := pstmt_check_ok ⟨P, nB a0 a1 a2⟩ _ 1 cD' (by decide)
  have q1 : pexec fu (.primitive (.check (.binary bl .ne (.variable u64 2) c0E))) ⟨P, nB a0 a1 a2⟩ = _ :=
    (pexec_prim fu _ _).trans s1
  -- declarations
  have d1 : (NExpr.variable u64 1).denote (penv ⟨P, nB a0 a1 a2⟩) = some (n : Int) := by
    rw [den_variable]; simpa using E0.2.1
  have s2 := pstmt_declare_ok ⟨P, nB a0 a1 a2⟩ u64 true (.variable u64 1) (n : Int) d1 (n : Int)
    (Ty.convert_of_valid _ _ (u64_lt _ hn))
  have q2 := (pexec_prim fu _ _).trans s2
  have E1 := E (P ++ [(⟨u64,(n : Int)⟩ : Cell)]) [⟨P.length,true⟩] [(⟨u64,(n : Int)⟩ : Cell)] rfl
  have d2 : (NExpr.variable u64 2).denote (penv ⟨P ++ [(⟨u64,(n : Int)⟩ : Cell)], nB a0 a1 a2 ++ [⟨P.length,true⟩]⟩) =
      some (d : Int) := by
    rw [den_variable]; exact E1.2.2
  have s3 := pstmt_declare_ok ⟨P ++ [(⟨u64,(n : Int)⟩ : Cell)], nB a0 a1 a2 ++ [⟨P.length,true⟩]⟩ u64 true (.variable u64 2)
    (d : Int) d2 (d : Int) (Ty.convert_of_valid _ _ (u64_lt _ hd))
  have q3 := (pexec_prim fu _ _).trans s3
  have heq : (⟨P ++ [(⟨u64,(n : Int)⟩ : Cell)] ++ [(⟨u64,(d : Int)⟩ : Cell)],
      nB a0 a1 a2 ++ [⟨P.length,true⟩] ++ [⟨(P ++ [(⟨u64,(n : Int)⟩ : Cell)]).length,true⟩]⟩ : PS) =
      shPS (nB a0 a1 a2) (mk P [n, d]) := by
    simp [shPS, mk, cm, bmd, List.range_succ]
  -- the loop
  obtain ⟨rL, hL, pL, retL, cL, nL⟩ := g_loop P d n hn hd fu hfu
  have t4 := pexec_sh fu gLoop (mk P [n, d]) (nB a0 a1 a2)
  have hlsh : pexec fu (gLoop.shN 3) (shPS (nB a0 a1 a2) (mk P [n, d])) = some (shR (nB a0 a1 a2) rL) := by
    have : (gLoop.shN 3) = gLoop.shN (nB a0 a1 a2).length := rfl
    rw [this]
    show pexec fu (gLoop.shN (nB a0 a1 a2).length) ⟨(mk P [n,d]).mem, nB a0 a1 a2 ++ (mk P [n,d]).bs⟩ = _
    rw [t4, hL]; rfl
  have hsL : shR (nB a0 a1 a2) rL = ⟨shPS (nB a0 a1 a2) (mk P [Nat.gcd n d, 0]), none, rL.cost, rL.need + 3⟩ := by
    simp only [shR, shPS]
    rw [pL, retL]; rfl
  -- the branch and the return
  have hg : Nat.gcd n d < 18446744073709551616 := by
    by_cases z : n = 0
    · subst z; rw [Nat.gcd_zero_left]; exact hd
    · have := Nat.gcd_le_left d (show 0 < n by omega); omega
  obtain ⟨PF, hPF⟩ : ∃ PF : PS, PF = shPS (nB a0 a1 a2) (mk P [Nat.gcd n d, 0]) := ⟨_, rfl⟩
  rw [← hPF] at hZ hM hsL
  have EF := E (mk P [Nat.gcd n d, 0]).mem (mk P [Nat.gcd n d, 0]).bs (cm (([Nat.gcd n d, 0] : List Nat).map Nat.cast)) rfl
  have cB := cmp0_value .eq (Or.inr rfl) 1 (penv PF) n (by rw [hPF]; exact EF.2.1)
  have hsize := mk_size P [Nat.gcd n d, 0]
  simp only [List.length_cons, List.length_nil] at hsize
  have hPFlen : PF.mem.length + PF.bs.length = P.length + 4 + 3 := by
    rw [hPF]; simp only [shPS, List.length_append]; simp; omega
  obtain ⟨rT, hT, hTret, hTps, hTc, hTn⟩ : ∃ rT : PR, pexec fu
      (.sequence (.branch (.binary bl .eq (.variable u64 1) c0E)
        (.sequence (.scope (.sequence (.primitive (.ret retZ)) Sk)) Sk) Sk)
        (.sequence (.primitive (.ret retM)) Sk)) PF = some rT ∧
      rT.ret = some (if n = 0 then z else m) ∧ rT.ps = PF ∧ rT.cost ≤ 40 ∧ rT.need ≤ P.length + 40 := by
    by_cases hn0 : n = 0
    · have hc1 : (NExpr.binary bl .eq (.variable u64 1) c0E).denote (penv PF) = some 1 := by
        rw [cB]; simp [hn0]
      have rz := pstmt_ret_ok PF retZ z (hZ hn0)
      have i1 := seq_ret (fu := fu) (b := Sk) (a := .primitive (.ret retZ)) (ps := PF) (by rw [pexec_prim]; exact rz) rfl
      have i2 := pexec_scope fu _ PF _ i1
      simp only [List.take_length] at i2
      have i3 := seq_ret (fu := fu) (b := Sk) (a := .scope (.sequence (.primitive (.ret retZ)) Sk)) (ps := PF) i2 rfl
      have br := pexec_branch_true fu _ _ Sk PF 1 hc1 (by decide) _ i3
      have fin := seq_ret (fu := fu) (b := .sequence (.primitive (.ret retM)) Sk) br rfl
      refine ⟨_, fin, by simp [hn0], rfl, ?_, ?_⟩
      · simp [NExpr.nodes] at *; omega
      · simp [NExpr.nodes] at *; omega
    · have hc0 : (NExpr.binary bl .eq (.variable u64 1) c0E).denote (penv PF) = some 0 := by
        rw [cB]; simp [hn0]
      have rm := pstmt_ret_ok PF retM m (hM hn0)
      have br := pexec_branch_false fu (.binary bl .eq (.variable u64 1) c0E)
        (.sequence (.scope (.sequence (.primitive (.ret retZ)) Sk)) Sk) Sk PF hc0 _ (pexec_skip fu PF)
      have j1 := seq_ret (fu := fu) (b := Sk) (a := .primitive (.ret retM)) (ps := PF) (by rw [pexec_prim]; exact rm) rfl
      have fin := seq_some br rfl j1
      refine ⟨_, fin, by simp [hn0], rfl, ?_, ?_⟩
      · simp [NExpr.nodes] at *; omega
      · simp [NExpr.nodes] at *; omega
  -- assemble
  have c4 := seq_some hlsh (by rw [hsL]) (by rw [hsL]; exact hT)
  have c3 := seq_some q3 rfl (by rw [heq]; exact c4)
  have c2 := seq_some q2 rfl c3
  have c1 := seq_some q1 rfl c2
  refine ⟨_, c1, ?_, ?_, ?_, ?_⟩
  · simpa using hTret
  · simp only [hsL, hTps] at *
    simp [NExpr.nodes] at *
    omega
  · simp only [hsL, hTps] at *
    simp [NExpr.nodes, mk_size] at *
    omega
  · refine ⟨cm (([Nat.gcd n d, 0] : List Nat).map Nat.cast), ?_⟩
    simp only [hTps, hPF, shPS, mk]


theorem final_env (P : List Cell) (a0 a1 a2 : Nat) (s n d : Nat) (hs : s < 18446744073709551616)
    (hn : n < 18446744073709551616) (hd : d < 18446744073709551616) (hg : Nat.gcd n d < 18446744073709551616)
    (h0 : P[a0]? = some ⟨u64,(s : Int)⟩) (h1 : P[a1]? = some ⟨u64,(n : Int)⟩) (h2 : P[a2]? = some ⟨u64,(d : Int)⟩) :
    penv (shPS (nB a0 a1 a2) (mk P [Nat.gcd n d, 0])) 0 u64 = some (s : Int) ∧
    penv (shPS (nB a0 a1 a2) (mk P [Nat.gcd n d, 0])) 1 u64 = some (n : Int) ∧
    penv (shPS (nB a0 a1 a2) (mk P [Nat.gcd n d, 0])) 2 u64 = some (d : Int) ∧
    penv (shPS (nB a0 a1 a2) (mk P [Nat.gcd n d, 0])) 3 u64 = some ((Nat.gcd n d : Nat) : Int) := by
  have E := refs_env P a0 a1 a2 s n d hs hn hd h0 h1 h2 (mk P [Nat.gcd n d, 0]).mem (mk P [Nat.gcd n d, 0]).bs
    (cm (([Nat.gcd n d, 0] : List Nat).map Nat.cast)) rfl
  refine ⟨E.1, E.2.1, E.2.2, ?_⟩
  have hv : ∀ x ∈ [Nat.gcd n d, 0], x < 18446744073709551616 := by intro x hx; simp at hx; omega
  have k := penv_mk P [Nat.gcd n d, 0] hv 0 (by simp)
  have b0 : (mk P [Nat.gcd n d, 0]).bs[0]? = some ⟨P.length+0,true⟩ := by simp [mk,bmd]
  have m0 : (mk P [Nat.gcd n d, 0]).mem[P.length+0]? = some ⟨u64,((Nat.gcd n d : Nat) : Int)⟩ := by
    rw [mk_mem, List.getElem?_append_right (by omega)]
    simp [cm]
  refine penv_ok _ 3 u64 ⟨P.length+0,true⟩ ⟨u64,((Nat.gcd n d : Nat) : Int)⟩ ?_ m0 rfl (u64_lt _ hg)
  show (nB a0 a1 a2 ++ (mk P [Nat.gcd n d, 0]).bs)[3]? = _
  rw [List.getElem?_append_right (by simp)]
  simpa using b0


theorem div_ret (i : Nat) (env : Nat → Ty → Option Int) (x g : Nat) (hx : x < 18446744073709551616) (hg0 : 0 < g)
    (hi : env i u64 = some (x : Int)) (h3 : env 3 u64 = some (g : Int)) :
    (NExpr.divrem u64 false (.variable u64 i) (.variable u64 3)).denote env = some ((x / g : Nat) : Int) := by
  rw [den_divrem, den_variable, den_variable, hi, h3]
  simp only [Option.bind_some]
  exact div_value x g hg0 hx

theorem gcd_pos_n (n d : Nat) (hn : n ≠ 0) : 0 < Nat.gcd n d := Nat.gcd_pos_of_pos_left d (by omega)

theorem gcd_lt (n d : Nat) (hn : n < 18446744073709551616) (hd : d < 18446744073709551616) :
    Nat.gcd n d < 18446744073709551616 := by
  by_cases z : n = 0
  · subst z; rw [Nat.gcd_zero_left]; exact hd
  · have := Nat.gcd_le_left d (show 0 < n by omega); omega

theorem norm_n_exec (P : List Cell) (a0 a1 a2 : Nat) (s n d : Nat) (hs : s < 18446744073709551616)
    (hn : n < 18446744073709551616) (hd : d < 18446744073709551616) (hd0 : d ≠ 0)
    (h0 : P[a0]? = some ⟨u64,(s : Int)⟩) (h1 : P[a1]? = some ⟨u64,(n : Int)⟩) (h2 : P[a2]? = some ⟨u64,(d : Int)⟩)
    (fu : Nat) (hfu : gsteps n d + 1 ≤ fu) :
    ∃ r : PR, pexec fu Proofs.RatioInstance.Ratio_normalize_n.body ⟨P, nB a0 a1 a2⟩ = some r ∧
      r.ret = some (((if n = 0 then 0 else n / Nat.gcd n d : Nat)) : Int) ∧
      r.cost ≤ 40 * gsteps n d + 100 ∧ r.need ≤ P.length + 40 ∧ ∃ L, r.ps.mem = P ++ L := by
  have F := final_env P a0 a1 a2 s n d hs hn hd (gcd_lt n d hn hd) h0 h1 h2
  have := norm_exec P a0 a1 a2 s n d hs hn hd hd0 h0 h1 h2 fu hfu c0E (.divrem u64 false (.variable u64 1) (.variable u64 3))
    0 ((n / Nat.gcd n d : Nat) : Int) (by simp [NExpr.nodes]) (by simp [NExpr.nodes])
    (fun _ => c0_value _) (fun hn0 => div_ret 1 _ n _ hn (gcd_pos_n n d hn0) F.2.1 F.2.2.2)
  rw [norm_n_body]
  by_cases hn0 : n = 0 <;> simpa [hn0] using this

theorem norm_d_exec (P : List Cell) (a0 a1 a2 : Nat) (s n d : Nat) (hs : s < 18446744073709551616)
    (hn : n < 18446744073709551616) (hd : d < 18446744073709551616) (hd0 : d ≠ 0)
    (h0 : P[a0]? = some ⟨u64,(s : Int)⟩) (h1 : P[a1]? = some ⟨u64,(n : Int)⟩) (h2 : P[a2]? = some ⟨u64,(d : Int)⟩)
    (fu : Nat) (hfu : gsteps n d + 1 ≤ fu) :
    ∃ r : PR, pexec fu Proofs.RatioInstance.Ratio_normalize_d.body ⟨P, nB a0 a1 a2⟩ = some r ∧
      r.ret = some (((if n = 0 then 1 else d / Nat.gcd n d : Nat)) : Int) ∧
      r.cost ≤ 40 * gsteps n d + 100 ∧ r.need ≤ P.length + 40 ∧ ∃ L, r.ps.mem = P ++ L := by
  have F := final_env P a0 a1 a2 s n d hs hn hd (gcd_lt n d hn hd) h0 h1 h2
  have := norm_exec P a0 a1 a2 s n d hs hn hd hd0 h0 h1 h2 fu hfu c1E (.divrem u64 false (.variable u64 2) (.variable u64 3))
    1 ((d / Nat.gcd n d : Nat) : Int) (by simp [NExpr.nodes]) (by simp [NExpr.nodes])
    (fun _ => c1_value _) (fun hn0 => div_ret 2 _ d _ hd (gcd_pos_n n d hn0) F.2.2.1 F.2.2.2)
  rw [norm_d_body]
  by_cases hn0 : n = 0 <;> simpa [hn0] using this

theorem norm_s_exec (P : List Cell) (a0 a1 a2 : Nat) (s n d : Nat) (hs : s < 18446744073709551616)
    (hn : n < 18446744073709551616) (hd : d < 18446744073709551616) (hd0 : d ≠ 0)
    (h0 : P[a0]? = some ⟨u64,(s : Int)⟩) (h1 : P[a1]? = some ⟨u64,(n : Int)⟩) (h2 : P[a2]? = some ⟨u64,(d : Int)⟩)
    (fu : Nat) (hfu : gsteps n d + 1 ≤ fu) :
    ∃ r : PR, pexec fu Proofs.RatioInstance.Ratio_normalize_s.body ⟨P, nB a0 a1 a2⟩ = some r ∧
      r.ret = some (((if n = 0 then 0 else s : Nat)) : Int) ∧
      r.cost ≤ 40 * gsteps n d + 100 ∧ r.need ≤ P.length + 40 ∧ ∃ L, r.ps.mem = P ++ L := by
  have F := final_env P a0 a1 a2 s n d hs hn hd (gcd_lt n d hn hd) h0 h1 h2
  have := norm_exec P a0 a1 a2 s n d hs hn hd hd0 h0 h1 h2 fu hfu c0E (.variable u64 0)
    0 (s : Int) (by simp [NExpr.nodes]) (by simp [NExpr.nodes])
    (fun _ => c0_value _) (fun _ => by rw [den_variable]; exact F.1)
  rw [norm_s_body]
  by_cases hn0 : n = 0 <;> simpa [hn0] using this


open Proofs.CppVector Proofs.CppVectorStore Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedSim Proofs.CppNestedEval Proofs.CppNestedStmt Proofs.CppNestedRows Proofs.CppNestedConstruct
open Proofs.CppNestedHoare Proofs.CppNestedScope Proofs.DoublingPrologue Proofs.DoublingCall Proofs.QuotientFrame
open Proofs.ScalarCall Proofs.ScalarStraight Proofs.IntSim Proofs.ExtremaCall

theorem prep_refs3t (caller : NState) (params : List CppVectorBindings.Parameter)
    (t1 t2 t3 : Ty) (s1 s2 s3 : Nat) (b1 b2 b3 : CppState.Binding) (v1 v2 v3 : Int)
    (hp : params = [.scalar t1 true false,.scalar t2 true false,.scalar t3 true false])
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (c2 : caller.scalarCell s2 t2 = some (b2,⟨t2,v2⟩))
    (c3 : caller.scalarCell s3 t3 = some (b3,⟨t3,v3⟩))
    (valid : caller.frame.state.wellFormed = true) :
    ∃ Sinit, prepare caller params [.scalarReference s1,.scalarReference s2,.scalarReference s3] = some Sinit ∧
      Sinit.slots = [.scalar 0,.scalar 1,.scalar 2] ∧ Sinit.scalars.memory = callerP caller ∧
      Sinit.scalars.bindings = [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩] ∧
      Sinit.scalars.baseMemory = caller.scalars.baseMemory ∧ Sinit.scope = caller.scope+1 ∧
      Sinit.frame = ⟨caller.frame.state,caller.frame.rootWritable,[]⟩ ∧
      Sinit.scalars.work = caller.scalars.work+7 ∧ caller.scalars.peak ≤ Sinit.scalars.peak := by
  obtain ⟨i1,_,_,m1,_,w1⟩ := scalarCell_facts c1
  obtain ⟨i2,_,_,m2,_,w2⟩ := scalarCell_facts c2
  obtain ⟨i3,_,_,m3,_,w3⟩ := scalarCell_facts c3
  have l1 : b1.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m1).1
  have l2 : b2.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m2).1
  have l3 : b3.address < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp m3).1
  have c2' : (caller.charge 1 1).scalarCell s2 t2 = some (b2,⟨t2,v2⟩) := c2
  have c3' : ((caller.charge 1 1).charge 1 1).scalarCell s3 t3 = some (b3,⟨t3,v3⟩) := c3
  have pad : ∀ (t : Ty) (b : CppState.Binding) (v : Int), b.address < caller.scalars.memory.length →
      caller.scalars.memory[b.address]? = some ⟨t,v⟩ →
      (caller.scalars.memory ++ List.replicate (caller.scalars.bindings.length + caller.frame.bindings.length)
        (⟨bl,0⟩ : Cell))[b.address]? = some ⟨t,v⟩ := by
    intro t b v lt h; rw [List.getElem?_append_left lt]; exact h
  have h1 := pad t1 b1 v1 l1 m1
  have h2 := pad t2 b2 v2 l2 m2
  have h3 := pad t3 b3 v3 l3 m3
  rw [hp]
  simp [prepare,valid,resolveAll,resolve,c1,c2',c3']
  simp [bindAll,bindOne,CppState.bindArgument,callerP,NState.observe,CppState.State.observe,h1,h2,h3,w1,w2,w3]
  simp only [charge_scalar_peak, charge_work]
  refine ⟨trivial, ?_⟩
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  refine Nat.le_trans ?_ (Nat.le_max_left _ _)
  exact Nat.le_max_left _ _


theorem refs3t_correct (prog : NProgram) (tn : Ty) (t1 t2 t3 : Ty)
    (hp : prog.parameters = [.scalar t1 true false,.scalar t2 true false,.scalar t3 true false])
    (hr : prog.result = ResultKind.scalar tn) (hbody : Scalar prog.body = true)
    (caller : NState) (s1 s2 s3 : Nat) (b1 b2 b3 : CppState.Binding) (v1 v2 v3 : Int)
    (c1 : caller.scalarCell s1 t1 = some (b1,⟨t1,v1⟩))
    (c2 : caller.scalarCell s2 t2 = some (b2,⟨t2,v2⟩))
    (c3 : caller.scalarCell s3 t3 = some (b3,⟨t3,v3⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (fu : Nat) (v : Int) (hv : tn.valid v = true) (C : Nat)
    (hex : ∀ P : List Cell, P = callerP caller →
      ∃ r, pexec fu prog.body ⟨P,[⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩]⟩ = some r ∧
        r.ret = some v ∧ r.cost ≤ C ∧ r.need ≤ P.length+100 ∧
        r.ps.mem.take caller.scalars.memory.length = caller.scalars.memory) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference s1,.scalarReference s2,.scalarReference s3] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference s1,.scalarReference s2,.scalarReference s3] = .finished (res,.scalar v) ∧
      ScalarPost2 caller Sinit res 0 (C+60) caller.scalars.memory := by
  obtain ⟨Sinit,hprep,sSlots,sMem,sBind,sBase,sScope,sFrame,sWork,sPeak⟩ :=
    prep_refs3t caller _ t1 t2 t3 s1 s2 s3 b1 b2 b3 v1 v2 v3 hp c1 c2 c3 valid
  have hlen : (callerP caller).length = caller.scalars.memory.length +
      (caller.scalars.bindings.length+caller.frame.bindings.length) := by simp [callerP]
  have takeM : (callerP caller).take caller.scalars.memory.length = caller.scalars.memory := by
    simp only [callerP]; exact List.take_left' rfl
  obtain ⟨r,hexec,hret,hcost,hneed,hrps⟩ := hex (callerP caller) rfl
  have hpost := call_scalar caller prog [.scalarReference s1,.scalarReference s2,.scalarReference s3] Sinit
    (callerP caller) [⟨b1.address,false⟩,⟨b2.address,false⟩,⟨b3.address,false⟩] hprep
    (by rw [sSlots]; rfl) sMem sBind sBase sScope sFrame sPeak
    (by omega) (by rw [takeM]) valid lengths strict base hbody fu r hexec _ hret tn hr hv
    (by omega) (by simp) 0 (C+60) (by omega)
  obtain ⟨fuel,res,hrun,post⟩ := hpost
  refine ⟨Sinit,fuel,res,hprep,hrun,?_⟩
  rw [hrps] at post
  exact post


theorem callerP_get (caller : NState) (a : Nat) (c : Cell) (h : caller.scalars.memory[a]? = some c) :
    (callerP caller)[a]? = some c := by
  have lt : a < caller.scalars.memory.length := (List.getElem?_eq_some_iff.mp h).1
  simp only [callerP, List.append_assoc]
  rw [List.getElem?_append_left lt]
  exact h

set_option maxHeartbeats 4000000 in
theorem norm_correct (prog : NProgram)
    (hp : prog.parameters = [.scalar u64 true false,.scalar u64 true false,.scalar u64 true false])
    (hr : prog.result = ResultKind.scalar u64) (hbody : Scalar prog.body = true)
    (caller : NState) (s1 s2 s3 : Nat) (b1 b2 b3 : CppState.Binding) (s n d : Nat)
    (hs : s < 18446744073709551616) (hn : n < 18446744073709551616) (hd : d < 18446744073709551616) (hd0 : d ≠ 0)
    (c1 : caller.scalarCell s1 u64 = some (b1,⟨u64,(s : Int)⟩))
    (c2 : caller.scalarCell s2 u64 = some (b2,⟨u64,(n : Int)⟩))
    (c3 : caller.scalarCell s3 u64 = some (b3,⟨u64,(d : Int)⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (v : Nat) (hv : v < 18446744073709551616)
    (ex : ∀ (P : List Cell) (a0 a1 a2 : Nat), P[a0]? = some ⟨u64,(s : Int)⟩ → P[a1]? = some ⟨u64,(n : Int)⟩ →
      P[a2]? = some ⟨u64,(d : Int)⟩ → ∃ r : PR, pexec (gsteps n d + 1) prog.body ⟨P, nB a0 a1 a2⟩ = some r ∧
        r.ret = some (v : Int) ∧ r.cost ≤ 40 * gsteps n d + 100 ∧ r.need ≤ P.length + 40 ∧ ∃ L, r.ps.mem = P ++ L) :
    ∃ Sinit fuel res, prepare caller prog.parameters [.scalarReference s1,.scalarReference s2,.scalarReference s3] = some Sinit ∧
      prog.callFuel fuel caller [.scalarReference s1,.scalarReference s2,.scalarReference s3] = .finished (res,.scalar (v : Int)) ∧
      ScalarPost2 caller Sinit res 0 (80 * Nat.log2 d + 200) caller.scalars.memory := by
  have hsteps : gsteps n d ≤ 2 * Nat.log2 d + 1 := gsteps_le d n (by omega)
  refine refs3t_correct prog u64 u64 u64 u64 hp hr hbody caller s1 s2 s3 b1 b2 b3 _ _ _ c1 c2 c3 valid lengths strict base
    (gsteps n d + 1) (v : Int) (u64_lt _ hv) (80 * Nat.log2 d + 140) ?_
  intro P hP
  subst hP
  obtain ⟨_,_,_,m1,_,_⟩ := scalarCell_facts c1
  obtain ⟨_,_,_,m2,_,_⟩ := scalarCell_facts c2
  obtain ⟨_,_,_,m3,_,_⟩ := scalarCell_facts c3
  obtain ⟨r, e, ret, cost, need, L, hL⟩ := ex (callerP caller) b1.address b2.address b3.address
    (callerP_get caller _ _ m1) (callerP_get caller _ _ m2) (callerP_get caller _ _ m3)
  refine ⟨r, e, ret, by omega, by omega, ?_⟩
  rw [hL]
  have lt : caller.scalars.memory.length ≤ (callerP caller).length := by simp [callerP]
  rw [List.take_append_of_le_length lt]
  simp only [callerP]; exact List.take_left' rfl


/-- `normalize(r)` for `r = (s, n, d)` (`d != 0`): the numerator of the reduced ratio. -/
theorem Ratio_normalize_n_correct (caller : NState) (s1 s2 s3 : Nat) (b1 b2 b3 : CppState.Binding) (s n d : Nat)
    (hs : s < 18446744073709551616) (hn : n < 18446744073709551616) (hd : d < 18446744073709551616) (hd0 : d ≠ 0)
    (c1 : caller.scalarCell s1 u64 = some (b1,⟨u64,(s : Int)⟩))
    (c2 : caller.scalarCell s2 u64 = some (b2,⟨u64,(n : Int)⟩))
    (c3 : caller.scalarCell s3 u64 = some (b3,⟨u64,(d : Int)⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.RatioInstance.Ratio_normalize_n.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3] = some Sinit ∧
      Proofs.RatioInstance.Ratio_normalize_n.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3] =
        .finished (res,.scalar (((if n = 0 then 0 else n / Nat.gcd n d) : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res 0 (80 * Nat.log2 d + 200) caller.scalars.memory :=
  norm_correct Proofs.RatioInstance.Ratio_normalize_n rfl rfl (by decide) caller s1 s2 s3 b1 b2 b3 s n d hs hn hd hd0
    c1 c2 c3 valid lengths strict base (if n = 0 then 0 else n / Nat.gcd n d) ((by split <;> first | omega | exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hn))
    (fun P a0 a1 a2 h0 h1 h2 => norm_n_exec P a0 a1 a2 s n d hs hn hd hd0 h0 h1 h2 _ (Nat.le_refl _))

/-- `normalize(r)` for `r = (s, n, d)` (`d != 0`): the denominator of the reduced ratio. -/
theorem Ratio_normalize_d_correct (caller : NState) (s1 s2 s3 : Nat) (b1 b2 b3 : CppState.Binding) (s n d : Nat)
    (hs : s < 18446744073709551616) (hn : n < 18446744073709551616) (hd : d < 18446744073709551616) (hd0 : d ≠ 0)
    (c1 : caller.scalarCell s1 u64 = some (b1,⟨u64,(s : Int)⟩))
    (c2 : caller.scalarCell s2 u64 = some (b2,⟨u64,(n : Int)⟩))
    (c3 : caller.scalarCell s3 u64 = some (b3,⟨u64,(d : Int)⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.RatioInstance.Ratio_normalize_d.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3] = some Sinit ∧
      Proofs.RatioInstance.Ratio_normalize_d.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3] =
        .finished (res,.scalar (((if n = 0 then 1 else d / Nat.gcd n d) : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res 0 (80 * Nat.log2 d + 200) caller.scalars.memory :=
  norm_correct Proofs.RatioInstance.Ratio_normalize_d rfl rfl (by decide) caller s1 s2 s3 b1 b2 b3 s n d hs hn hd hd0
    c1 c2 c3 valid lengths strict base (if n = 0 then 1 else d / Nat.gcd n d) ((by split <;> first | omega | exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hd))
    (fun P a0 a1 a2 h0 h1 h2 => norm_d_exec P a0 a1 a2 s n d hs hn hd hd0 h0 h1 h2 _ (Nat.le_refl _))

/-- `normalize(r)` for `r = (s, n, d)` (`d != 0`): the sign of the reduced ratio. -/
theorem Ratio_normalize_s_correct (caller : NState) (s1 s2 s3 : Nat) (b1 b2 b3 : CppState.Binding) (s n d : Nat)
    (hs : s < 18446744073709551616) (hn : n < 18446744073709551616) (hd : d < 18446744073709551616) (hd0 : d ≠ 0)
    (c1 : caller.scalarCell s1 u64 = some (b1,⟨u64,(s : Int)⟩))
    (c2 : caller.scalarCell s2 u64 = some (b2,⟨u64,(n : Int)⟩))
    (c3 : caller.scalarCell s3 u64 = some (b3,⟨u64,(d : Int)⟩))
    (valid : caller.frame.state.wellFormed = true)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner c, caller.frame.state.forest.context owner = some c → c ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ Sinit fuel res, prepare caller Proofs.RatioInstance.Ratio_normalize_s.parameters
        [.scalarReference s1,.scalarReference s2,.scalarReference s3] = some Sinit ∧
      Proofs.RatioInstance.Ratio_normalize_s.callFuel fuel caller
        [.scalarReference s1,.scalarReference s2,.scalarReference s3] =
        .finished (res,.scalar (((if n = 0 then 0 else s) : Nat) : Int)) ∧
      ScalarPost2 caller Sinit res 0 (80 * Nat.log2 d + 200) caller.scalars.memory :=
  norm_correct Proofs.RatioInstance.Ratio_normalize_s rfl rfl (by decide) caller s1 s2 s3 b1 b2 b3 s n d hs hn hd hd0
    c1 c2 c3 valid lengths strict base (if n = 0 then 0 else s) (by split <;> omega)
    (fun P a0 a1 a2 h0 h1 h2 => norm_s_exec P a0 a1 a2 s n d hs hn hd hd0 h0 h1 h2 _ (Nat.le_refl _))

end Proofs.RatioCall
