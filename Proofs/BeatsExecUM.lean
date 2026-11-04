import Proofs.BeatsExecUN
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

abbrev UMBRA (o : Nat) : Command :=
  .branch (.binary bT .eq (aVar (o + 4)) (aVar (o + 6))) (uAsg o (o + 7))
    (.sequence (.scope (.sequence (.branch (.binary bT .eq (aVar (o + 5)) (aVar (o + 6))) (uAsg o (o + 8)) Sk) Sk)) Sk)
abbrev UMBRB (o : Nat) : Command :=
  .branch (.logical true (.binary bT .ne (aVar (o + 9)) (bInf o)) (.binary bT .lt (aVar (o + 9)) (bX o))) (uAsg o (o + 9)) Sk
abbrev UMt10 (o : Nat) : Command := .sequence (bW 8 (aVar (o + 9)) o) Sk
abbrev UMt9 (o : Nat) : Command := .sequence (UMBRB o) (UMt10 o)
abbrev UMt8 (o : Nat) : Command := .sequence (aDecl (aRd o 8)) (UMt9 o)
abbrev UMt7 (o : Nat) : Command := .sequence (bW 1 (aVar (o + 8)) o) (UMt8 o)
abbrev UMt6 (o : Nat) : Command := .sequence (bW 0 (aVar (o + 7)) o) (UMt7 o)
abbrev UMt5 (o : Nat) : Command := .sequence (bW 3 (bX o) o) (UMt6 o)
abbrev UMt4 (o : Nat) : Command := .sequence (UMBRA o) (UMt5 o)
abbrev UMt3 (o : Nat) : Command := .sequence (aDecl (aVar (o + 5))) (UMt4 o)
abbrev UMt2 (o : Nat) : Command := .sequence (aDecl (aVar (o + 4))) (UMt3 o)
abbrev UMt1 (o : Nat) : Command := .sequence (aDecl (aRd o 3)) (UMt2 o)
abbrev UM (o : Nat) : Command := .sequence (aDecl (aRd o 0)) (.sequence (aDecl (aRd o 1)) (UMt1 o))

def um1 (b : BS) (k : Nat) (x NMX NSX LVP : Int) : BS := { b with mnv := b.mnv.set k x }
def um2 (b : BS) (k : Nat) (x NMX NSX LVP : Int) : BS := { um1 b k x NMX NSX LVP with mxv := b.mxv.set k NMX }
def um3 (b : BS) (k : Nat) (x NMX NSX LVP : Int) : BS := { um2 b k x NMX NSX LVP with smx := b.smx.set k NSX }
def um4 (b : BS) (k : Nat) (x NMX NSX LVP : Int) : BS := { um3 b k x NMX NSX LVP with lval := b.lval.set k LVP }

/-- The result of `update_node_min` on the vectors. -/
def ummB (b : BS) (inf x : Int) (k : Nat) : BS :=
  { b with
    mnv := b.mnv.set k x
    mxv := b.mxv.set k (if b.mxv.getD k 0 = b.mnv.getD k 0 then x else b.mxv.getD k 0)
    smx := b.smx.set k (if ¬ (b.mxv.getD k 0 = b.mnv.getD k 0) ∧ b.smx.getD k 0 = b.mnv.getD k 0 then x else b.smx.getD k 0)
    lval := b.lval.set k (if (b.lval.getD k 0 ≠ inf ∧ b.lval.getD k 0 < x) then x else b.lval.getD k 0) }

-- Keep concrete scalar states and vector maps folded while applying execution lemmas.
attribute [local irreducible] gS VVB

set_option maxHeartbeats 0 in
theorem umm_exec (mv : MV) (hnv : mv.nv = 15) (pre : List Cell) (hty : ∀ v, v < 9 → mv.ty v = s64) (b : BS) (P : List Cell)
    (inf x : Int) (n k : Nat) (hk : k < M31) (hinf : s64.valid inf = true) (hninf : s64.valid (-inf) = true)
    (hx : s64.valid x = true) (hl0 : k < b.mxv.length) (hl1 : k < b.smx.length) (hl3 : k < b.mnv.length)
    (hl8 : k < b.lval.length)
    (hv0 : ∀ w ∈ b.mxv, s64.valid w = true) (hv1 : ∀ w ∈ b.smx, s64.valid w = true)
    (hv3 : ∀ w ∈ b.mnv, s64.valid w = true) (hv8 : ∀ w ∈ b.lval, s64.valid w = true) (fu : Nat) :
    ∃ r : PRM, pexecM mv fu (UM (mv.nv + pre.length)) (gS P (pre ++ [cs inf, ci n, ci k, cs x])) (VVB b) = some r ∧
      r.ret = none ∧ r.vv = VVB (ummB b inf x k) ∧ r.cost ≤ 3000 ∧ r.wk ≤ 4 := by
  classical
  have hm0 := getD_mem_valid b.mxv k hl0 hv0
  have hm1 := getD_mem_valid b.smx k hl1 hv1
  have hm3 := getD_mem_valid b.mnv k hl3 hv3
  have hm8 := getD_mem_valid b.lval k hl8 hv8
  unfold ummB
  generalize hD0 : b.mxv.getD k 0 = mx at *
  generalize hD1 : b.smx.getD k 0 = sx at *
  generalize hD3 : b.mnv.getD k 0 = mn at *
  generalize hD8 : b.lval.getD k 0 = lv at *
  obtain ⟨NMX, hNMX⟩ : ∃ v : Int, v = (if mx = mn then x else mx) := ⟨_, rfl⟩
  obtain ⟨NSX, hNSX⟩ : ∃ v : Int, v = (if ¬ (mx = mn) ∧ sx = mn then x else sx) := ⟨_, rfl⟩
  obtain ⟨LVP, hLVP⟩ : ∃ v : Int, v = (if (lv ≠ inf ∧ lv < x) then x else lv) := ⟨_, rfl⟩
  rw [← hNMX, ← hNSX, ← hLVP]
  have vNMX : s64.valid NMX = true := by
    rw [hNMX]; by_cases h : mx = mn
    · rw [if_pos h]; exact hx
    · rw [if_neg h]; exact hm0
  have vNSX : s64.valid NSX = true := by
    rw [hNSX]; by_cases h : ¬ (mx = mn) ∧ sx = mn
    · rw [if_pos h]; exact hx
    · rw [if_neg h]; exact hm1
  have vLVP : s64.valid LVP = true := by
    rw [hLVP]; by_cases h : (lv ≠ inf ∧ lv < x)
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
  obtain ⟨r11, h11, hr11, hp11, hv11, hc11, hw11⟩ : ∃ r11 : PRM, pexecM mv fu Sk (gS P ((pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) ++ [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩, ⟨s64, LVP⟩])) (VVB (um4 b k x NMX NSX LVP)) = some r11 ∧
      r11.ret = none ∧ r11.ps = gS P ((pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) ++ [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩, ⟨s64, LVP⟩]) ∧ r11.vv = VVB (um4 b k x NMX NSX LVP) ∧ r11.cost ≤ 0 ∧ r11.wk ≤ 0 :=
    ⟨_, pexecM_skip _ _ _ _, rfl, rfl, rfl, Nat.le_refl _, Nat.le_refl _⟩
  -- S10: lval[k] = LVP
  obtain ⟨r10, h10, hr10, hp10, hv10, hc10, hn10, hw10⟩ := seq_write mv fu (gS P ((pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) ++ [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩, ⟨s64, LVP⟩])) (VVB (um3 b k x NMX NSX LVP)) 8 (by omega) s64
    (hty 8 (by omega)) (bIx (mv.nv + pre.length)) (aVar ((mv.nv + pre.length) + 9)) LVP k
    (den_cellvar mv P _ (pre.length + 9) _ (by omega) LVP (cell_at pre [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩, ⟨s64, LVP⟩] inf x 5 _ rfl (pre.length + 9) n k (by omega)) vLVP _)
    ((db [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩, ⟨s64, LVP⟩] _).1) (by rw [VVB_get8]; exact hl8) vLVP Sk r11 (by rw [VVB_get8, VVB_upd8]; exact h11) hr11
    100 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 200)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S9: if (lv != inf && lv < x) lv = x
  have e8 : ((pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) ++ ([⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩, ⟨s64, lv⟩] : List Cell)).set (pre.length + 9) (⟨s64, if (lv ≠ inf ∧ lv < x) then x else lv⟩ : Cell) = ((pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) ++ ([⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩, ⟨s64, LVP⟩] : List Cell)) := by
    rw [hLVP]
    have i9 : pre.length + 9 = (pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)).length + 5 := by simp
    rw [i9, set_app_idx (pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) _ 5 _ (by simp)]
    simp
  obtain ⟨r9, h9, hr9, hp9, hv9, hc9, hn9, hw9⟩ := seq_sbranch2 mv fu P ((pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) ++ [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩, ⟨s64, lv⟩]) (VVB (um3 b k x NMX NSX LVP)) (pre.length + 9) (by simp) s64
    (.logical true (.binary bT .ne (aVar ((mv.nv + pre.length) + 9)) (bInf (mv.nv + pre.length))) (.binary bT .lt (aVar ((mv.nv + pre.length) + 9)) (bX (mv.nv + pre.length)))) (bX (mv.nv + pre.length)) (lv ≠ inf ∧ lv < x) x x ⟨s64, lv⟩
    (den_andc mv _ _ _ _ (lv ≠ inf) (lv < x)
      (by rw [den_cmp mv _ _ .ne _ _ lv inf (den_cellvar mv P _ (pre.length + 9) _ (by omega) lv (cell_at pre [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩, ⟨s64, lv⟩] inf x 5 _ rfl (pre.length + 9) n k (by omega)) hm8 _) ((db [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩, ⟨s64, lv⟩] _).2.2.1) rfl rfl]; exact ne_conv _ _)
      (by rw [den_cmp mv _ _ .lt _ _ lv x (den_cellvar mv P _ (pre.length + 9) _ (by omega) lv (cell_at pre [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩, ⟨s64, lv⟩] inf x 5 _ rfl (pre.length + 9) n k (by omega)) hm8 _) ((db [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩, ⟨s64, lv⟩] _).2.1) rfl rfl]; exact lt_conv _ _) rfl rfl)
    (fun h => (db [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩, ⟨s64, lv⟩] _).2.1) (cell_at pre [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩, ⟨s64, lv⟩] inf x 5 _ rfl (pre.length + 9) n k (by omega)) rfl hm8 (fun h => conv_signed s64 rfl rfl _ hx)
    (UMt10 (mv.nv + pre.length)) r10 (by rw [e8]; exact h10) hr10 200 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes])
    (P.length + 2 * pre.length + 200) (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S8: long long lv = lval[k]
  obtain ⟨r8, h8, hr8, hp8, hv8', hc8, hn8, hw8⟩ := seq_decl mv fu P ((pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) ++ [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩]) (VVB (um3 b k x NMX NSX LVP)) s64 (aRd (mv.nv + pre.length) 8) lv lv
    (den_rd mv (VVB (um3 b k x NMX NSX LVP)) _ 8 (by omega) (hty 8 (by omega)) lv (bIx (mv.nv + pre.length)) rfl k (by rw [VVB_get8]; exact hl8) (by rw [VVB_get8]; exact hD8) (by rw [VVB_get8]; exact hv8) (hdn [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩] (VVB b))) (conv_signed s64 rfl rfl _ hm8) (UMt9 (mv.nv + pre.length)) r9
    (by rw [List.append_assoc]; exact h9) hr9
  -- S7: smax_v[k] = NSX
  obtain ⟨r7, h7, hr7, hp7, hv7, hc7, hn7, hw7⟩ := seq_write mv fu (gS P ((pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) ++ [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩])) (VVB (um2 b k x NMX NSX LVP)) 1 (by omega) s64
    (hty 1 (by omega)) (bIx (mv.nv + pre.length)) (aVar ((mv.nv + pre.length) + 8)) NSX k
    (den_cellvar mv P _ (pre.length + 8) _ (by omega) NSX (cell_at pre [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩] inf x 4 _ rfl (pre.length + 8) n k (by omega)) vNSX _)
    ((db [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩] _).1) (by rw [VVB_get1]; exact hl1) vNSX (UMt8 (mv.nv + pre.length)) r8 (by rw [VVB_get1, VVB_upd1]; exact h8) hr8
    100 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 200)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S6: max_v[k] = NMX
  obtain ⟨r6, h6, hr6, hp6, hv6, hc6, hn6, hw6⟩ := seq_write mv fu (gS P ((pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) ++ [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩])) (VVB (um1 b k x NMX NSX LVP)) 0 (by omega) s64
    (hty 0 (by omega)) (bIx (mv.nv + pre.length)) (aVar ((mv.nv + pre.length) + 7)) NMX k
    (den_cellvar mv P _ (pre.length + 7) _ (by omega) NMX (cell_at pre [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩] inf x 3 _ rfl (pre.length + 7) n k (by omega)) vNMX _)
    ((db [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩] _).1) (by rw [VVB_get0]; exact hl0) vNMX (UMt7 (mv.nv + pre.length)) r7 (by rw [VVB_get0, VVB_upd0]; exact h7) hr7
    100 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 200)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S5: min_v[k] = x
  obtain ⟨r5, h5, hr5, hp5, hv5, hc5, hn5, hw5⟩ := seq_write mv fu (gS P ((pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) ++ [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩])) (VVB b) 3 (by omega) s64
    (hty 3 (by omega)) (bIx (mv.nv + pre.length)) (bX (mv.nv + pre.length)) x k ((db [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩] _).2.1) ((db [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩] _).1) (by rw [VVB_get3]; exact hl3) hx (UMt6 (mv.nv + pre.length)) r6
    (by rw [VVB_get3, VVB_upd3]; exact h6) hr6
    100 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes]) (P.length + 2 * pre.length + 200)
    (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S4: if (mx == mn) nmx = x; else if (sx == mn) nsx = x
  have e6 : ((((pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) ++ ([⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, mx⟩, ⟨s64, sx⟩] : List Cell))).set (pre.length + 7) (⟨s64, if mx = mn then x else mx⟩ : Cell)).set (pre.length + 8)
      (⟨s64, if ¬ (mx = mn) ∧ sx = mn then x else sx⟩ : Cell) = ((pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) ++ ([⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, NMX⟩, ⟨s64, NSX⟩] : List Cell)) := by
    rw [hNMX, hNSX]
    have i7 : pre.length + 7 = (pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)).length + 3 := by simp
    have i8 : pre.length + 8 = (pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)).length + 4 := by simp
    rw [i7, set_app_idx (pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) _ 3 _ (by simp), i8,
      set_app_idx (pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) _ 4 _ (by simp)]
    simp
  obtain ⟨r4, h4, hr4, hp4, hv4', hc4, hn4, hw4⟩ := seq_sbranch_elif mv fu P ((pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) ++ [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, mx⟩, ⟨s64, sx⟩]) (VVB b) (pre.length + 7) (pre.length + 8)
    (by omega) (by simp) (by simp) s64 (.binary bT .eq (aVar ((mv.nv + pre.length) + 4)) (aVar ((mv.nv + pre.length) + 6))) (.binary bT .eq (aVar ((mv.nv + pre.length) + 5)) (aVar ((mv.nv + pre.length) + 6)))
    (bX (mv.nv + pre.length)) (bX (mv.nv + pre.length)) (mx = mn) (sx = mn) x x ⟨s64, mx⟩ ⟨s64, sx⟩
    (by rw [den_cmp mv _ _ .eq _ _ mx mn (den_cellvar mv P _ (pre.length + 4) _ (by omega) mx (cell_at pre [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, mx⟩, ⟨s64, sx⟩] inf x 0 _ rfl (pre.length + 4) n k (by omega)) hm0 _) (den_cellvar mv P _ (pre.length + 6) _ (by omega) mn (cell_at pre [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, mx⟩, ⟨s64, sx⟩] inf x 2 _ rfl (pre.length + 6) n k (by omega)) hm3 _) rfl rfl]; exact Proofs.BellmanFordPExec.eq_convP _ _)
    (fun _ => by rw [den_cmp mv _ _ .eq _ _ sx mn (den_cellvar mv P _ (pre.length + 5) _ (by omega) sx (cell_at pre [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, mx⟩, ⟨s64, sx⟩] inf x 1 _ rfl (pre.length + 5) n k (by omega)) hm1 _) (den_cellvar mv P _ (pre.length + 6) _ (by omega) mn (cell_at pre [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, mx⟩, ⟨s64, sx⟩] inf x 2 _ rfl (pre.length + 6) n k (by omega)) hm3 _) rfl rfl]; exact Proofs.BellmanFordPExec.eq_convP _ _)
    (fun _ => (db [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, mx⟩, ⟨s64, sx⟩] _).2.1) (fun _ _ => (db [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, mx⟩, ⟨s64, sx⟩] _).2.1)
    (cell_at pre [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, mx⟩, ⟨s64, sx⟩] inf x 3 _ rfl (pre.length + 7) n k (by omega)) (cell_at pre [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, mx⟩, ⟨s64, sx⟩] inf x 4 _ rfl (pre.length + 8) n k (by omega))
    rfl rfl hm0 hm1 (fun _ => conv_signed s64 rfl rfl _ hx) (fun _ _ => conv_signed s64 rfl rfl _ hx)
    (UMt5 (mv.nv + pre.length)) r5 (by rw [e6]; exact h5) hr5 300 (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes])
    (P.length + 2 * pre.length + 300) (by simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes, gS_size]; omega)
  -- S3: nsx = sx
  obtain ⟨r3, h3, hr3, hp3, hv3', hc3, hn3, hw3⟩ := seq_decl mv fu P ((pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) ++ [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, mx⟩]) (VVB b) s64 (aVar ((mv.nv + pre.length) + 5)) sx sx
    (den_cellvar mv P _ (pre.length + 5) _ (by omega) sx (cell_at pre [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩, ⟨s64, mx⟩] inf x 1 _ rfl (pre.length + 5) n k (by omega)) hm1 (VVB b)) (conv_signed s64 rfl rfl _ hm1) (UMt4 (mv.nv + pre.length)) r4
    (by rw [List.append_assoc]; exact h4) hr4
  -- S2: nmx = mx
  obtain ⟨r2, h2, hr2, hp2, hv2', hc2, hn2, hw2⟩ := seq_decl mv fu P ((pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) ++ [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩]) (VVB b) s64 (aVar ((mv.nv + pre.length) + 4)) mx mx
    (den_cellvar mv P _ (pre.length + 4) _ (by omega) mx (cell_at pre [⟨s64, mx⟩, ⟨s64, sx⟩, ⟨s64, mn⟩] inf x 0 _ rfl (pre.length + 4) n k (by omega)) hm0 (VVB b)) (conv_signed s64 rfl rfl _ hm0) (UMt3 (mv.nv + pre.length)) r3
    (by rw [List.append_assoc]; exact h3) hr3
  -- S1: long long mn = min_v[k]
  obtain ⟨r1, h1, hr1, hp1, hv1', hc1, hn1, hw1⟩ := seq_decl mv fu P ((pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) ++ [⟨s64, mx⟩, ⟨s64, sx⟩]) (VVB b) s64 (aRd (mv.nv + pre.length) 3) mn mn
    (den_rd mv (VVB (b)) _ 3 (by omega) (hty 3 (by omega)) mn (bIx (mv.nv + pre.length)) rfl k (by rw [VVB_get3]; exact hl3) (by rw [VVB_get3]; exact hD3) (by rw [VVB_get3]; exact hv3) (hdn [⟨s64, mx⟩, ⟨s64, sx⟩] (VVB b))) (conv_signed s64 rfl rfl _ hm3) (UMt2 (mv.nv + pre.length)) r2
    (by rw [List.append_assoc]; exact h2) hr2
  -- S0b: long long sx = smax_v[k]
  obtain ⟨rb, hb, hrb, hpb, hvb, hcb, hnb, hwb⟩ := seq_decl mv fu P ((pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) ++ [⟨s64, mx⟩]) (VVB b) s64 (aRd (mv.nv + pre.length) 1) sx sx
    (den_rd mv (VVB (b)) _ 1 (by omega) (hty 1 (by omega)) sx (bIx (mv.nv + pre.length)) rfl k (by rw [VVB_get1]; exact hl1) (by rw [VVB_get1]; exact hD1) (by rw [VVB_get1]; exact hv1) (hdn [⟨s64, mx⟩] (VVB b))) (conv_signed s64 rfl rfl _ hm1) (UMt1 (mv.nv + pre.length)) r1
    (by rw [List.append_assoc]; exact h1) hr1
  -- S0a: long long mx = max_v[k]
  obtain ⟨ra, ha, hra, hpa, hva, hca, hna, hwa⟩ := seq_decl mv fu P (pre ++ ([cs inf, ci n, ci k, cs x] : List Cell)) (VVB b) s64 (aRd (mv.nv + pre.length) 0) mx mx
    (den_rd mv (VVB (b)) _ 0 (by omega) (hty 0 (by omega)) mx (bIx (mv.nv + pre.length)) rfl k (by rw [VVB_get0]; exact hl0) (by rw [VVB_get0]; exact hD0) (by rw [VVB_get0]; exact hv0) (hdn0 (VVB b))) (conv_signed s64 rfl rfl _ hm0) (.sequence (aDecl (aRd (mv.nv + pre.length) 1)) (UMt1 (mv.nv + pre.length))) rb
    hb hrb
  refine ⟨ra, ha, hra, ?_, ?_, ?_⟩
  · rw [hva, hvb, hv1', hv2', hv3', hv4', hv5, hv6, hv7, hv8', hv9, hv10, hv11]
    try rfl
  · simp [vwp, NExpr.nodes, NExpr.scalarOnly, Container.nodes] at *; omega
  · simp at *; omega

end Proofs.BeatsExec
