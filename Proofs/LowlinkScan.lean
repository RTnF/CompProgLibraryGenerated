import Proofs.LowlinkInv

namespace Proofs.LowlinkScan
open Proofs.PrimMath (Rtc)
open Proofs.LowlinkInv

/-- A scan step at the top `v` of the stack that reads the arc `q = It v`, whose end `w` is already visited. Only `It v`
and `L` change; `Lnew` is either `L` or `L` with `L v` lowered to `O w`. -/
def scanS (st : St) (v : Nat) (Lnew : Nat → Int) : St :=
  { st with L := Lnew, It := upd st.It v (st.It v + 1) }

theorem inv_scan {n : Nat} {hd tg : Nat → Nat} {st : St} (I : MInv n hd tg st) {v w q : Nat} (Lnew : Nat → Int)
    (hv : v ∈ st.Vis) (hfv : st.Fi v < 0) (hq : (q : Int) = st.It v) (hit : (q : Int) < (hd (v + 1) : Int))
    (hw : tg q = w) (hwv : 0 ≤ st.O w)
    (h1 : ∀ u, Lnew u ≤ st.L u) (h2 : ∀ u, u ≠ v → Lnew u = st.L u) (h3 : 0 ≤ Lnew v)
    (h4 : Lnew v = st.L v ∨ (st.P v ≠ (w : Int) ∧ Lnew v = st.O w))
    (h5 : st.P v ≠ (w : Int) → Lnew v ≤ st.O w) : MInv n hd tg (scanS st v Lnew) := by
  have hwvis : w ∈ st.Vis := I.vis_of_nn hwv
  have hrng := I.it_rng v hv
  have hadj : AdjH hd tg v w := ⟨q, by omega, by omega, hw⟩
  refine ⟨I.vis_nd, I.vis_lt, I.vis_ord, I.unv_ord, I.par_none, I.par_ok, I.fin_unv, I.fin_ok, I.sp_le, I.sk_mem, I.sk_par,
    I.sk_root, I.sk_cover, I.interval, I.nbr_fin, I.desc_fin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, I.sep_unv, I.par_neg⟩
  · -- it_rng
    intro x hx
    by_cases hxv : x = v
    · subst hxv
      simp only [scanS, upd_same]
      omega
    · simp only [scanS, upd_ne _ _ _ _ hxv]
      exact I.it_rng x hx
  · -- it_scan
    intro x hx q' hq1 hq2
    by_cases hxv : x = v
    · subst hxv
      simp only [scanS, upd_same] at hq2
      by_cases hlt : (q' : Int) < st.It x
      · exact I.it_scan x hx q' hq1 hlt
      · have : q' = q := by omega
        subst this
        rw [hw]
        exact hwvis
    · simp only [scanS, upd_ne _ _ _ _ hxv] at hq2
      exact I.it_scan x hx q' hq1 hq2
  · -- it_fin
    intro x hx hfx
    have hfx' : 0 ≤ st.Fi x := hfx
    have hxv : x ≠ v := by
      intro e
      subst e
      omega
    simp only [scanS, upd_ne _ _ _ _ hxv]
    exact I.it_fin x hx hfx
  · -- low_le
    intro u hu
    by_cases huv : u = v
    · subst huv
      have := (I.low_le u hu).2
      have := h1 u
      simp only [scanS]
      omega
    · simp only [scanS, h2 u huv]
      exact I.low_le u hu
  · -- low_mem
    intro u hu
    by_cases huv : u = v
    · subst huv
      simp only [scanS]
      rcases h4 with h | ⟨hp, h⟩
      · rw [h]
        exact I.low_mem u hu
      · right
        exact ⟨u, w, Rtc.refl _, hadj, hp, h.symm⟩
    · simp only [scanS, h2 u huv]
      exact I.low_mem u hu
  · -- low_min
    intro u hu x w' q' hset hq1 hq2 hq3 hq4
    have hold : (q' : Int) < st.It x → Lnew u ≤ st.O w' := fun hlt =>
      Int.le_trans (h1 u) (I.low_min u hu x w' q' hset hq1 hlt hq3 hq4)
    by_cases hxv : x = v
    · subst hxv
      simp only [scanS, upd_same] at hq2
      by_cases hlt : (q' : Int) < st.It x
      · exact hold hlt
      · have hqq : q' = q := by omega
        subst hqq
        rw [hw] at hq3
        subst hq3
        have huv : u = x := by
          apply Classical.byContradiction
          intro hne
          have h0 : 0 ≤ st.Fi x := hset.2 x hset.1 (Rtc.refl _) (Ne.symm hne)
          omega
        subst huv
        exact h5 hq4
    · simp only [scanS, upd_ne _ _ _ _ hxv] at hq2
      exact hold hq2
  · -- sep_cnt
    intro p hp
    have := I.sep_cnt p hp
    simp only [scanS]
    rw [this]
    congr 2
    apply List.filter_congr
    intro c _
    by_cases hc : 0 ≤ st.Fi c
    · have hcv : c ≠ v := by
        intro e
        subst e
        omega
      simp [h2 c hcv]
    · simp [hc]

end Proofs.LowlinkScan
