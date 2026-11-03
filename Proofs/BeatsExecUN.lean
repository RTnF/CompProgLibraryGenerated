import Proofs.BeatsExecAA
import Proofs.CountrZeroExec
namespace Proofs.BeatsExec
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.StraightLine Proofs.VecExpr Proofs.VecStraight Proofs.VecStmt
open Proofs.VecWrite Proofs.VecKitW Proofs.GenState Proofs.MultiVec Proofs.MultiKit Proofs.ForLoopM Proofs.ForLoopC
open Proofs.ForLoopB
open Proofs.ForLoop (ci gS_take)
open Proofs.CppState (Cell)
open Proofs.IntSim Proofs.QuotientSearch Proofs.DoublingNested Proofs.PrefixSumsCall Proofs.VectorFillCall
open Proofs.PowModStep (Sk int_one_ne)
open Proofs.VectorSumCall (conv_signed)
open Proofs.LowerBoundIndexCall (validN)
open Proofs.BellmanFordExec

abbrev uAsg (o c : Nat) : Command := .sequence (.scope (.sequence (.primitive (.assign c s64 (bX o))) Sk)) Sk
abbrev UNBRA (o : Nat) : Command :=
  .branch (.binary bT .eq (aVar (o + 4)) (aVar (o + 5))) (uAsg o (o + 7))
    (.sequence (.scope (.sequence (.branch (.binary bT .eq (aVar (o + 4)) (aVar (o + 6))) (uAsg o (o + 8)) Sk) Sk)) Sk)
abbrev UNBRB (o : Nat) : Command :=
  .branch (.logical true (.binary bT .ne (aVar (o + 9)) (bInf o)) (.binary bT .lt (bX o) (aVar (o + 9)))) (uAsg o (o + 9)) Sk
abbrev UNt11 (o : Nat) : Command := Sk
abbrev UNt10 (o : Nat) : Command := .sequence (bW 8 (aVar (o + 9)) o) Sk
abbrev UNt9 (o : Nat) : Command := .sequence (UNBRB o) (UNt10 o)
abbrev UNt8 (o : Nat) : Command := .sequence (aDecl (aRd o 8)) (UNt9 o)
abbrev UNt7 (o : Nat) : Command := .sequence (bW 4 (aVar (o + 8)) o) (UNt8 o)
abbrev UNt6 (o : Nat) : Command := .sequence (bW 3 (aVar (o + 7)) o) (UNt7 o)
abbrev UNt5 (o : Nat) : Command := .sequence (bW 0 (bX o) o) (UNt6 o)
abbrev UNt4 (o : Nat) : Command := .sequence (UNBRA o) (UNt5 o)
abbrev UNt3 (o : Nat) : Command := .sequence (aDecl (aVar (o + 6))) (UNt4 o)
abbrev UNt2 (o : Nat) : Command := .sequence (aDecl (aVar (o + 5))) (UNt3 o)
abbrev UNt1 (o : Nat) : Command := .sequence (aDecl (aRd o 4)) (UNt2 o)
abbrev UN (o : Nat) : Command := .sequence (aDecl (aRd o 0)) (.sequence (aDecl (aRd o 3)) (UNt1 o))


def un1 (b : BS) (k : Nat) (x NMN NSN LVP : Int) : BS := { b with mxv := b.mxv.set k x }
def un2 (b : BS) (k : Nat) (x NMN NSN LVP : Int) : BS := { un1 b k x NMN NSN LVP with mnv := b.mnv.set k NMN }
def un3 (b : BS) (k : Nat) (x NMN NSN LVP : Int) : BS := { un2 b k x NMN NSN LVP with smn := b.smn.set k NSN }
def un4 (b : BS) (k : Nat) (x NMN NSN LVP : Int) : BS := { un3 b k x NMN NSN LVP with lval := b.lval.set k LVP }

/-- The result of `update_node_max` on the vectors. -/
def unmB (b : BS) (inf x : Int) (k : Nat) : BS :=
  { b with
    mxv := b.mxv.set k x
    mnv := b.mnv.set k (if b.mxv.getD k 0 = b.mnv.getD k 0 then x else b.mnv.getD k 0)
    smn := b.smn.set k (if ¬ (b.mxv.getD k 0 = b.mnv.getD k 0) ∧ b.mxv.getD k 0 = b.smn.getD k 0 then x else b.smn.getD k 0)
    lval := b.lval.set k (if (b.lval.getD k 0 ≠ inf ∧ x < b.lval.getD k 0) then x else b.lval.getD k 0) }

theorem den_andc (mv : MV) (vv : Nat → List Int) (env : Nat → Ty → Option Int) (l r : NExpr) (p q : Prop) [Decidable p] [Decidable q]
    (hl : vdenM mv vv env l = some (if p then 1 else 0)) (hr : vdenM mv vv env r = some (if q then 1 else 0))
    (hls : l.scalarOnly = true) (hrs : r.scalarOnly = true) :
    vdenM mv vv env (.logical true l r) = some (if p ∧ q then 1 else 0) := by
  rw [vdenM_scalar _ _ _ _ (by simp [NExpr.scalarOnly, hls, hrs])]
  rw [vdenM_scalar _ _ _ _ hls] at hl
  rw [vdenM_scalar _ _ _ _ hrs] at hr
  rw [Proofs.CountrZeroExec.den_and, hl, Option.bind_some]
  by_cases hp : p
  · by_cases hq : q
    · simp [hp, hq, hr]
    · simp [hp, hq, hr]
  · simp [hp]

set_option maxHeartbeats 0 in
theorem unm_exec (mv : MV) (hnv : mv.nv = 15) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64) (b : BS) (P : List Cell)
    (inf x : Int) (n k : Nat) (hk : k < M31) (hinf : s64.valid inf = true) (hninf : s64.valid (-inf) = true)
    (hx : s64.valid x = true) (hl0 : k < b.mxv.length) (hl3 : k < b.mnv.length)
    (hl4 : k < b.smn.length) (hl8 : k < b.lval.length)
    (hv0 : ∀ w ∈ b.mxv, s64.valid w = true) (hv3 : ∀ w ∈ b.mnv, s64.valid w = true)
    (hv4 : ∀ w ∈ b.smn, s64.valid w = true) (hv8 : ∀ w ∈ b.lval, s64.valid w = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (UN (mv.nv + pre.length)) (gS P (pre ++ [cs inf, ci n, ci k, cs x])) (VVB b) = some r ∧
      r.ret = none ∧ r.vv = VVB (unmB b inf x k) ∧ r.cost ≤ 3000 ∧ r.wk ≤ 4 := by
  classical
  have hm0 := getD_mem_valid b.mxv k hl0 hv0
  have hm3 := getD_mem_valid b.mnv k hl3 hv3
  have hm4 := getD_mem_valid b.smn k hl4 hv4
  have hm8 := getD_mem_valid b.lval k hl8 hv8
  unfold unmB
  generalize hD0 : b.mxv.getD k 0 = mx at *
  generalize hD3 : b.mnv.getD k 0 = mn at *
  generalize hD4 : b.smn.getD k 0 = sn at *
  generalize hD8 : b.lval.getD k 0 = lv at *
  obtain ⟨NMN, hNMN⟩ : ∃ v : Int, v = (if mx = mn then x else mn) := ⟨_, rfl⟩
  obtain ⟨NSN, hNSN⟩ : ∃ v : Int, v = (if ¬ (mx = mn) ∧ mx = sn then x else sn) := ⟨_, rfl⟩
  obtain ⟨LVP, hLVP⟩ : ∃ v : Int, v = (if (lv ≠ inf ∧ x < lv) then x else lv) := ⟨_, rfl⟩
  rw [← hNMN, ← hNSN, ← hLVP]
  have vNMN : s64.valid NMN = true := by
    rw [hNMN]; by_cases h : mx = mn
    · rw [if_pos h]; exact hx
    · rw [if_neg h]; exact hm3
  have vNSN : s64.valid NSN = true := by
    rw [hNSN]; by_cases h : ¬ (mx = mn) ∧ mx = sn
    · rw [if_pos h]; exact hx
    · rw [if_neg h]; exact hm4
  have vLVP : s64.valid LVP = true := by
    rw [hLVP]; by_cases h : (lv ≠ inf ∧ x < lv)
    · rw [if_pos h]; exact hx
    · rw [if_neg h]; exact hm8
  have db := fun (ext : List Cell) => dens_base mv P (pre ++ [cs inf, ci n, ci k, cs x] ++ ext) pre.length inf x k hk
    (base_lookup pre ext inf x k n).1 (base_lookup pre ext inf x k n).2.1 (base_lookup pre ext inf x k n).2.2 hinf hninf hx
  have hdn : ∀ (ext : List Cell) (vv : Nat → List Int), (bIx (mv.nv + pre.length)).denote (penvN mv.nv (gS P (pre ++ [cs inf, ci n, ci k, cs x] ++ ext))) = some (k : Int) := by
    intro ext vv
    have := (db ext vv).1
    rwa [vdenM_scalar _ _ _ _ rfl] at this
  have db0 := dens_base mv P (pre ++ [cs inf, ci n, ci k, cs x]) pre.length inf x k hk
    (by simpa using (base_lookup pre [] inf x k n).1) (by simpa using (base_lookup pre [] inf x k n).2.1)
    (by simpa using (base_lookup pre [] inf x k n).2.2) hinf hninf hx
  have hdn0 : ∀ (vv : Nat → List Int), (bIx (mv.nv + pre.length)).denote (penvN mv.nv (gS P (pre ++ [cs inf, ci n, ci k, cs x]))) = some (k : Int) := by
    intro vv
    have := (db0 vv).1
    rwa [vdenM_scalar _ _ _ _ rfl] at this
  obtain ⟨r11, h11, hr11, hp11, hv11, hc11, hw11⟩ : ∃ r11 : PRM, pexecM mv fu Sk (gS P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩, ⟨s64, LVP⟩])) (VVB (un4 b k x NMN NSN LVP)) = some r11 ∧
      r11.ret = none ∧ r11.ps = gS P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩, ⟨s64, LVP⟩]) ∧ r11.vv = VVB (un4 b k x NMN NSN LVP) ∧ r11.cost ≤ 0 ∧ r11.wk ≤ 0 :=
    ⟨_, pexecM_skip _ _ _ _, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
  -- S10: lval[k] = LVP
  obtain ⟨r10, h10, hr10, hp10, hv10, hc10, hn10, hw10⟩ := seq_write mv fu (gS P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩, ⟨s64, LVP⟩])) (VVB (un3 b k x NMN NSN LVP)) 8 (by omega) s64
    (hty 8 (by omega)) (bIx (mv.nv + pre.length)) (aVar ((mv.nv + pre.length) + 9)) LVP k
    (den_cellvar mv P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩, ⟨s64, LVP⟩]) (pre.length + 9) _ (by omega) LVP (cell_at pre [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩, ⟨s64, LVP⟩] inf x 5 _ rfl (pre.length + 9) n k (by omega)) vLVP _)
    ((db [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩, ⟨s64, LVP⟩] _).1) (by rw [VVB_get8]; exact hl8) vLVP Sk r11 (by rw [VVB_get8, VVB_upd8]; exact h11) hr11
    100 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 200)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S9: if (lv != inf && x < lv) lv = x
  have e8 : ((pre ++ [cs inf, ci n, ci k, cs x]) ++ ([⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩, ⟨s64, lv⟩] : List Cell)).set (pre.length + 9) (⟨s64, if (lv ≠ inf ∧ x < lv) then x else lv⟩ : Cell) = ((pre ++ [cs inf, ci n, ci k, cs x]) ++ ([⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩, ⟨s64, LVP⟩] : List Cell)) := by
    rw [hLVP]
    have i9 : pre.length + 9 = (pre ++ [cs inf, ci n, ci k, cs x]).length + 5 := by simp
    rw [i9, set_app_idx (pre ++ [cs inf, ci n, ci k, cs x]) _ 5 _ (by simp)]
    simp
  obtain ⟨r9, h9, hr9, hp9, hv9, hc9, hn9, hw9⟩ := seq_sbranch2 mv fu P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩, ⟨s64, lv⟩]) (VVB (un3 b k x NMN NSN LVP)) (pre.length + 9) (by simp) s64
    (.logical true (.binary bT .ne (aVar ((mv.nv + pre.length) + 9)) (bInf (mv.nv + pre.length))) (.binary bT .lt (bX (mv.nv + pre.length)) (aVar ((mv.nv + pre.length) + 9)))) (bX (mv.nv + pre.length)) (lv ≠ inf ∧ x < lv) x x ⟨s64, lv⟩
    (den_andc mv _ _ _ _ (lv ≠ inf) (x < lv)
      (by rw [den_cmp mv _ _ .ne _ _ lv inf (den_cellvar mv P _ (pre.length + 9) _ (by omega) lv (cell_at pre [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩, ⟨s64, lv⟩] inf x 5 _ rfl (pre.length + 9) n k (by omega)) hm8 _) ((db [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩, ⟨s64, lv⟩] _).2.2.1) rfl rfl]; exact ne_conv _ _)
      (by rw [den_cmp mv _ _ .lt _ _ x lv ((db [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩, ⟨s64, lv⟩] _).2.1) (den_cellvar mv P _ (pre.length + 9) _ (by omega) lv (cell_at pre [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩, ⟨s64, lv⟩] inf x 5 _ rfl (pre.length + 9) n k (by omega)) hm8 _) rfl rfl]; exact lt_conv _ _) rfl rfl)
    (fun h => (db [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩, ⟨s64, lv⟩] _).2.1) (cell_at pre [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩, ⟨s64, lv⟩] inf x 5 _ rfl (pre.length + 9) n k (by omega)) rfl hm8 (fun h => conv_signed s64 rfl rfl _ hx)
    (UNt10 (mv.nv + pre.length)) r10 (by rw [e8]; exact h10) hr10 200 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes])
    (P.length + 2 * pre.length + 200) (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S8: long long lv = lval[k]
  obtain ⟨r8, h8, hr8, hp8, hv8', hc8, hn8, hw8⟩ := seq_decl mv fu P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩]) (VVB (un3 b k x NMN NSN LVP)) s64 (aRd (mv.nv + pre.length) 8) lv lv
    (den_rd mv (VVB (un3 b k x NMN NSN LVP)) _ 8 (by omega) (hty 8 (by omega)) lv (bIx (mv.nv + pre.length)) rfl k (by rw [VVB_get8]; exact hl8) (by rw [VVB_get8]; exact hD8) (by rw [VVB_get8]; exact hv8) (hdn [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩] (VVB b))) (conv_signed s64 rfl rfl _ hm8) (UNt9 (mv.nv + pre.length)) r9
    (by rw [List.append_assoc]; exact h9) hr9
  -- S7: smn[k] = NSN
  obtain ⟨r7, h7, hr7, hp7, hv7, hc7, hn7, hw7⟩ := seq_write mv fu (gS P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩])) (VVB (un2 b k x NMN NSN LVP)) 4 (by omega) s64
    (hty 4 (by omega)) (bIx (mv.nv + pre.length)) (aVar ((mv.nv + pre.length) + 8)) NSN k
    (den_cellvar mv P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩]) (pre.length + 8) _ (by omega) NSN (cell_at pre [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩] inf x 4 _ rfl (pre.length + 8) n k (by omega)) vNSN _)
    ((db [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩] _).1) (by rw [VVB_get4]; exact hl4) vNSN (UNt8 (mv.nv + pre.length)) r8 (by rw [VVB_get4, VVB_upd4]; exact h8) hr8
    100 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 200)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S6: mnv[k] = NMN
  obtain ⟨r6, h6, hr6, hp6, hv6, hc6, hn6, hw6⟩ := seq_write mv fu (gS P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩])) (VVB (un1 b k x NMN NSN LVP)) 3 (by omega) s64
    (hty 3 (by omega)) (bIx (mv.nv + pre.length)) (aVar ((mv.nv + pre.length) + 7)) NMN k
    (den_cellvar mv P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩]) (pre.length + 7) _ (by omega) NMN (cell_at pre [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩] inf x 3 _ rfl (pre.length + 7) n k (by omega)) vNMN _)
    ((db [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩] _).1) (by rw [VVB_get3]; exact hl3) vNMN (UNt7 (mv.nv + pre.length)) r7 (by rw [VVB_get3, VVB_upd3]; exact h7) hr7
    100 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 200)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S5: mxv[k] = x
  obtain ⟨r5, h5, hr5, hp5, hv5, hc5, hn5, hw5⟩ := seq_write mv fu (gS P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩])) (VVB b) 0 (by omega) s64
    (hty 0 (by omega)) (bIx (mv.nv + pre.length)) (bX (mv.nv + pre.length)) x k ((db [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩] _).2.1) ((db [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩] _).1) (by rw [VVB_get0]; exact hl0) hx (UNt6 (mv.nv + pre.length)) r6
    (by rw [VVB_get0, VVB_upd0]; exact h6) hr6
    100 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 200)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S4: if (mx == mn) nmn = x; else if (mx == sn) nsn = x
  have e6 : ((((pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) ++ ([⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, mn⟩, ⟨s64, sn⟩] : List Cell))).set (pre.length + 7) (⟨s64, if mx = mn then x else mn⟩ : Cell)).set (pre.length + 8)
      (⟨s64, if ¬ (mx = mn) ∧ mx = sn then x else sn⟩ : Cell) = ((pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) ++ ([⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, NMN⟩, ⟨s64, NSN⟩] : List Cell)) := by
    rw [hNMN, hNSN]
    have i7 : pre.length + 7 = (pre ++ [cs inf, ci n, ci k, cs x]).length + 3 := by simp
    have i8 : pre.length + 8 = (pre ++ [cs inf, ci n, ci k, cs x]).length + 4 := by simp
    rw [i7, set_app_idx (pre ++ [cs inf, ci n, ci k, cs x]) _ 3 _ (by simp), i8, set_app_idx (pre ++ [cs inf, ci n, ci k, cs x]) _ 4 _ (by simp)]
    simp
  obtain ⟨r4, h4, hr4, hp4, hv4', hc4, hn4, hw4⟩ := seq_sbranch_elif mv fu P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, mn⟩, ⟨s64, sn⟩]) (VVB b) (pre.length + 7) (pre.length + 8)
    (by omega) (by simp) (by simp) s64 (.binary bT .eq (aVar ((mv.nv + pre.length) + 4)) (aVar ((mv.nv + pre.length) + 5))) (.binary bT .eq (aVar ((mv.nv + pre.length) + 4)) (aVar ((mv.nv + pre.length) + 6)))
    (bX (mv.nv + pre.length)) (bX (mv.nv + pre.length)) (mx = mn) (mx = sn) x x ⟨s64, mn⟩ ⟨s64, sn⟩
    (by rw [den_cmp mv _ _ .eq _ _ mx mn (den_cellvar mv P _ (pre.length + 4) _ (by omega) mx (cell_at pre [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, mn⟩, ⟨s64, sn⟩] inf x 0 _ rfl (pre.length + 4) n k (by omega)) hm0 _) (den_cellvar mv P _ (pre.length + 5) _ (by omega) mn (cell_at pre [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, mn⟩, ⟨s64, sn⟩] inf x 1 _ rfl (pre.length + 5) n k (by omega)) hm3 _) rfl rfl]; exact Proofs.BellmanFordPExec.eq_convP _ _)
    (fun _ => by rw [den_cmp mv _ _ .eq _ _ mx sn (den_cellvar mv P _ (pre.length + 4) _ (by omega) mx (cell_at pre [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, mn⟩, ⟨s64, sn⟩] inf x 0 _ rfl (pre.length + 4) n k (by omega)) hm0 _) (den_cellvar mv P _ (pre.length + 6) _ (by omega) sn (cell_at pre [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, mn⟩, ⟨s64, sn⟩] inf x 2 _ rfl (pre.length + 6) n k (by omega)) hm4 _) rfl rfl]; exact Proofs.BellmanFordPExec.eq_convP _ _)
    (fun _ => (db [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, mn⟩, ⟨s64, sn⟩] _).2.1) (fun _ _ => (db [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, mn⟩, ⟨s64, sn⟩] _).2.1)
    (cell_at pre [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, mn⟩, ⟨s64, sn⟩] inf x 3 _ rfl (pre.length + 7) n k (by omega)) (cell_at pre [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, mn⟩, ⟨s64, sn⟩] inf x 4 _ rfl (pre.length + 8) n k (by omega))
    rfl rfl hm3 hm4 (fun _ => conv_signed s64 rfl rfl _ hx) (fun _ _ => conv_signed s64 rfl rfl _ hx)
    (UNt5 (mv.nv + pre.length)) r5 (by rw [e6]; exact h5) hr5 300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes])
    (P.length + 2 * pre.length + 300) (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S3: nsn = sn (copy of the local)
  obtain ⟨r3, h3, hr3, hp3, hv3', hc3, hn3, hw3⟩ := seq_decl mv fu P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, mn⟩]) (VVB b) s64 (aVar ((mv.nv + pre.length) + 6)) sn sn
    (den_cellvar mv P _ (pre.length + 6) _ (by omega) sn (cell_at pre [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩, ⟨s64, mn⟩] inf x 2 _ rfl (pre.length + 6) n k (by omega)) hm4 (VVB b)) (conv_signed s64 rfl rfl _ hm4) (UNt4 (mv.nv + pre.length)) r4
    (by rw [List.append_assoc]; exact h4) hr4
  -- S2: nmn = mn
  obtain ⟨r2, h2, hr2, hp2, hv2', hc2, hn2, hw2⟩ := seq_decl mv fu P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩]) (VVB b) s64 (aVar ((mv.nv + pre.length) + 5)) mn mn
    (den_cellvar mv P _ (pre.length + 5) _ (by omega) mn (cell_at pre [⟨s64, mx⟩, ⟨s64, mn⟩, ⟨s64, sn⟩] inf x 1 _ rfl (pre.length + 5) n k (by omega)) hm3 (VVB b)) (conv_signed s64 rfl rfl _ hm3) (UNt3 (mv.nv + pre.length)) r3
    (by rw [List.append_assoc]; exact h3) hr3
  -- S1: long long sn = smin_v[k]
  obtain ⟨r1, h1, hr1, hp1, hv1', hc1, hn1, hw1⟩ := seq_decl mv fu P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, mx⟩, ⟨s64, mn⟩]) (VVB b) s64 (aRd (mv.nv + pre.length) 4) sn sn
    (den_rd mv (VVB (b)) _ 4 (by omega) (hty 4 (by omega)) sn (bIx (mv.nv + pre.length)) rfl k (by rw [VVB_get4]; exact hl4) (by rw [VVB_get4]; exact hD4) (by rw [VVB_get4]; exact hv4) (hdn [⟨s64, mx⟩, ⟨s64, mn⟩] (VVB b))) (conv_signed s64 rfl rfl _ hm4) (UNt2 (mv.nv + pre.length)) r2
    (by rw [List.append_assoc]; exact h2) hr2
  -- S0b: long long mn = min_v[k]
  obtain ⟨rb, hb, hrb, hpb, hvb, hcb, hnb, hwb⟩ := seq_decl mv fu P ((pre ++ [cs inf, ci n, ci k, cs x]) ++ [⟨s64, mx⟩]) (VVB b) s64 (aRd (mv.nv + pre.length) 3) mn mn
    (den_rd mv (VVB (b)) _ 3 (by omega) (hty 3 (by omega)) mn (bIx (mv.nv + pre.length)) rfl k (by rw [VVB_get3]; exact hl3) (by rw [VVB_get3]; exact hD3) (by rw [VVB_get3]; exact hv3) (hdn [⟨s64, mx⟩] (VVB b))) (conv_signed s64 rfl rfl _ hm3) (UNt1 (mv.nv + pre.length)) r1
    (by rw [List.append_assoc]; exact h1) hr1
  -- S0a: long long mx = max_v[k]
  obtain ⟨ra, ha, hra, hpa, hva, hca, hna, hwa⟩ := seq_decl mv fu P (pre ++ [cs inf, ci n, ci k, cs x]) (VVB b) s64 (aRd (mv.nv + pre.length) 0) mx mx
    (den_rd mv (VVB (b)) _ 0 (by omega) (hty 0 (by omega)) mx (bIx (mv.nv + pre.length)) rfl k (by rw [VVB_get0]; exact hl0) (by rw [VVB_get0]; exact hD0) (by rw [VVB_get0]; exact hv0) (hdn0 (VVB b))) (conv_signed s64 rfl rfl _ hm0) (.sequence (aDecl (aRd (mv.nv + pre.length) 3)) (UNt1 (mv.nv + pre.length))) rb
    hb hrb
  refine ⟨ra, ha, hra, ?_, ?_, ?_⟩
  · rw [hva, hvb, hv1', hv2', hv3', hv4', hv5, hv6, hv7, hv8', hv9, hv10, hv11]
    try rfl
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at *; omega
  · simp at *; omega

end Proofs.BeatsExec
