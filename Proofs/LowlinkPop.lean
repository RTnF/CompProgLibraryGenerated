import Proofs.LowlinkInv

namespace Proofs.LowlinkPop
open Proofs.PrimMath (Rtc)
open Proofs.LowlinkInv

theorem length_filter_update {l : List Nat} (hl : l.Nodup) (q q' : Nat → Bool) (c0 : Nat) (h0 : c0 ∈ l)
    (hq : ∀ c ∈ l, c ≠ c0 → q' c = q c) (hq0 : q c0 = false) :
    (l.filter q').length = (l.filter q).length + (if q' c0 = true then 1 else 0) := by
  induction l with
  | nil => simp at h0
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    by_cases hac : a = c0
    · subst hac
      have hft : t.filter q' = t.filter q := by
        apply List.filter_congr
        intro c hc
        exact hq c (List.mem_cons_of_mem _ hc) (fun e => hl.1 (e ▸ hc))
      simp only [List.filter_cons, hq0, hft]
      cases hq' : q' a <;> simp
    · have h0' : c0 ∈ t := by
        rcases List.mem_cons.mp h0 with e | e
        · exact absurd e.symm hac
        · exact e
      have := ih hl.2 h0' (fun c hc hne => hq c (List.mem_cons_of_mem _ hc) hne)
      have hqa : q' a = q a := hq a (by simp) hac
      simp only [List.filter_cons, hqa]
      cases hqa' : q a <;> simp [this] <;> omega

/-- The top `v` of the stack is finished: the finishing time is set, the stack shrinks and (if there is a parent) the
parent's `L` and `Sp` are updated. -/
def popS (st : St) (v : Nat) : St :=
  { st with
    Fi := upd st.Fi v (st.Vis.length : Int)
    sp := st.sp - 1
    L := fun u => if st.P v = (u : Int) then min (st.L u) (st.L v) else st.L u
    Sp := fun u => if st.P v = (u : Int) then st.Sp u + (if st.O u ≤ st.L v then 1 else 0) else st.Sp u }


theorem desc_last_aux {P : Nat → Int} {a x : Nat} (h : Rtc (Pr P) a x) : a = x ∨ ∃ q, Rtc (Pr P) a q ∧ Pr P q x := by
  cases h with
  | refl => exact Or.inl rfl
  | tail hab hbc => exact Or.inr ⟨_, hab, hbc⟩

theorem inv_pop {n : Nat} {hd tg : Nat → Nat} {st : St} (I : MInv n hd tg st) {v : Nat} (hsp : 0 < st.sp)
    (hv : st.Sk (st.sp - 1) = v) (hit : st.It v = (hd (v + 1) : Int)) : MInv n hd tg (popS st v) := by
  have hvm := I.sk_mem (st.sp - 1) (by omega)
  rw [hv] at hvm
  obtain ⟨hvV, hfv⟩ := hvm
  have hOv := I.ord_lt_len hvV
  have hpar : ∀ u : Nat, st.P v = (u : Int) → 2 ≤ st.sp ∧ u = st.Sk (st.sp - 2) := by
    intro u hu
    by_cases h2 : 2 ≤ st.sp
    · refine ⟨h2, ?_⟩
      have := I.sk_par (st.sp - 2) (by omega)
      have e : st.sp - 2 + 1 = st.sp - 1 := by omega
      rw [e, hv] at this
      unfold Pr at this
      omega
    · exfalso
      have h1 : st.sp = 1 := by omega
      have := I.sk_root (by omega)
      have e : st.sp - 1 = 0 := by omega
      rw [e] at hv
      rw [hv] at this
      omega
  have hparS : ∀ u : Nat, st.P v = (u : Int) → u ∈ st.Vis ∧ st.Fi u < 0 ∧ st.O u < st.O v := by
    intro u hu
    obtain ⟨h2, rfl⟩ := hpar u hu
    have := I.sk_mem (st.sp - 2) (by omega)
    exact ⟨this.1, this.2, (I.par_ok _ _ hu).2.2⟩
  have hnotself : st.P v ≠ (v : Int) := by
    intro h
    have := (I.par_ok _ _ h).2.2
    omega
  have hFi' : ∀ x, x ≠ v → (popS st v).Fi x = st.Fi x := fun x hx => upd_ne _ _ _ _ hx
  have hFiv : (popS st v).Fi v = (st.Vis.length : Int) := upd_same _ _ _
  have hfinE : ∀ x ∈ st.Vis, finE (popS st v) x = finE st x := by
    intro x hx
    show (if 0 ≤ (popS st v).Fi x then (popS st v).Fi x else (st.Vis.length : Int)) =
      (if 0 ≤ st.Fi x then st.Fi x else (st.Vis.length : Int))
    by_cases hxv : x = v
    · subst hxv
      have hn : ¬ 0 ≤ st.Fi x := by omega
      rw [hFiv, if_pos (Int.natCast_nonneg _), if_neg hn]
    · rw [hFi' x hxv]
  have hLle : ∀ u, (popS st v).L u ≤ st.L u := by
    intro u
    show (if st.P v = (u : Int) then min (st.L u) (st.L v) else st.L u) ≤ st.L u
    split
    · exact Int.min_le_left _ _
    · exact Int.le_refl _
  refine ⟨I.vis_nd, I.vis_lt, I.vis_ord, I.unv_ord, I.par_none, I.par_ok, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, I.it_rng,
    I.it_scan, ?_, ?_, ?_, ?_, ?_, ?_, I.par_neg⟩
  · -- fin_unv
    intro x hx
    have hxv : x ≠ v := fun e => hx (e ▸ hvV)
    rw [hFi' x hxv]
    exact I.fin_unv x hx
  · -- fin_ok
    intro x hx hfx
    by_cases hxv : x = v
    · subst hxv
      rw [hFiv]
      have := hOv.2
      exact ⟨this, Int.le_refl _⟩
    · rw [hFi' x hxv] at hfx ⊢
      exact I.fin_ok x hx hfx
  · -- sp_le
    show st.sp - 1 ≤ st.Vis.length
    have := I.sp_le
    omega
  · -- sk_mem
    intro i hi
    have hi' : i < st.sp - 1 := hi
    have hm := I.sk_mem i (by omega)
    have hne : st.Sk i ≠ v := by
      intro e
      have := I.stack_ord (i := i) (j := st.sp - 1) hi' (by omega)
      rw [hv, e] at this
      omega
    refine ⟨hm.1, ?_⟩
    show upd st.Fi v (st.Vis.length : Int) (st.Sk i) < 0
    rw [upd_ne _ _ _ _ hne]
    exact hm.2
  · -- sk_par
    intro i hi
    exact I.sk_par i (by have : i + 1 < st.sp - 1 := hi; omega)
  · -- sk_root
    intro h
    exact I.sk_root (by have : 0 < st.sp - 1 := h; omega)
  · -- sk_cover
    intro x hx hfx
    have hxv : x ≠ v := by
      intro e
      subst e
      rw [hFiv] at hfx
      omega
    rw [hFi' x hxv] at hfx
    obtain ⟨i, hi, rfl⟩ := I.sk_cover x hx hfx
    refine ⟨i, ?_, rfl⟩
    show i < st.sp - 1
    apply Classical.byContradiction
    intro hge
    have : i = st.sp - 1 := by omega
    subst this
    exact hxv hv
  · -- interval
    intro x hx y hy
    rw [hfinE x hx]
    exact I.interval x hx y hy
  · -- nbr_fin
    intro x hx hfx w hw
    by_cases hxv : x = v
    · subst hxv
      obtain ⟨q, hq1, hq2, hq3⟩ := hw
      have hwV := I.it_scan x hx q hq1 (by omega)
      rw [hq3] at hwV
      refine ⟨hwV, ?_⟩
      rw [hFiv]
      exact (I.ord_lt_len hwV).2
    · rw [hFi' x hxv] at hfx ⊢
      exact I.nbr_fin x hx hfx w hw
  · -- desc_fin
    intro u hu hfu x hx
    have hxV := I.desc_vis hu hx
    by_cases huv : u = v
    · subst huv
      rw [hFiv]
      by_cases hxv : x = u
      · subst hxv
        rw [hFiv]
        exact ⟨by omega, Int.le_refl _⟩
      · rw [hFi' x hxv]
        have hfx : 0 ≤ st.Fi x := by
          apply Classical.byContradiction
          intro hneg
          have h1 := I.unfin_desc_top hxV (by omega) hsp
          rw [hv] at h1
          have h2 := I.desc_ord hu hx
          have h3 := I.desc_ord hxV h1
          exact hxv (I.ord_inj hxV hu (by omega))
        exact ⟨hfx, (I.fin_ok x hxV hfx).2⟩
    · rw [hFi' u huv] at hfu ⊢
      obtain ⟨h1, h2⟩ := I.desc_fin u hu hfu x hx
      have hxv : x ≠ v := by
        intro e
        subst e
        omega
      rw [hFi' x hxv]
      exact ⟨h1, h2⟩
  · -- it_fin
    intro x hx hfx
    by_cases hxv : x = v
    · subst hxv
      exact hit
    · rw [hFi' x hxv] at hfx
      exact I.it_fin x hx hfx
  · -- low_le
    intro u hu
    obtain ⟨hl0, hl1⟩ := I.low_le u hu
    simp only [popS]
    by_cases h : st.P v = (u : Int)
    · rw [if_pos h]
      have := (I.low_le v hvV).1
      exact ⟨by omega, by omega⟩
    · rw [if_neg h]
      exact ⟨hl0, hl1⟩
  · -- low_mem
    intro u hu
    simp only [popS]
    by_cases h : st.P v = (u : Int)
    · rw [if_pos h]
      obtain ⟨_, _, hou⟩ := hparS u h
      by_cases hlt : st.L u ≤ st.L v
      · rw [Int.min_eq_left hlt]
        exact I.low_mem u hu
      · rw [Int.min_eq_right (by omega)]
        have hlu := (I.low_le u hu).2
        rcases I.low_mem v hvV with heq | ⟨x, w, hx, hxw, hnp, hw⟩
        · omega
        · right
          exact ⟨x, w, Rtc.head h hx, hxw, hnp, hw⟩
    · rw [if_neg h]
      exact I.low_mem u hu
  · -- low_min
    intro u hu x w' q hset hq1 hq2 hq3 hq4
    by_cases hS : Settled st u x
    · exact Int.le_trans (hLle u) (I.low_min u hu x w' q hS hq1 hq2 hq3 hq4)
    · have hex : ∃ y, DescM st.P u y ∧ DescM st.P y x ∧ y ≠ u ∧ st.Fi y < 0 := by
        apply Classical.byContradiction
        intro hnex
        apply hS
        refine ⟨hset.1, ?_⟩
        intro y h1 h2 h3
        apply Classical.byContradiction
        intro hneg
        exact hnex ⟨y, h1, h2, h3, by omega⟩
      obtain ⟨y, hy1, hy2, hy3, hy4⟩ := hex
      have hyv : y = v := by
        apply Classical.byContradiction
        intro hne
        have := hset.2 y hy1 hy2 hy3
        rw [hFi' y hne] at this
        omega
      subst hyv
      have hPu : st.P y = (u : Int) := by
        rcases desc_last_aux hy1 with e | ⟨q', hq', hpq'⟩
        · exact absurd e.symm hy3
        · obtain ⟨hq'V, hq'F, hq'O⟩ := hparS q' hpq'
          have hqu : q' = u := by
            apply Classical.byContradiction
            intro hne
            have hq'v : q' ≠ y := by
              intro e
              subst e
              omega
            have := hset.2 q' hq' (Rtc.head hpq' hy2) hne
            rw [hFi' q' hq'v] at this
            omega
          rw [← hqu]
          exact hpq'
      obtain ⟨huV, huF, huO⟩ := hparS u hPu
      have hSv : Settled st y x := by
        refine ⟨hy2, ?_⟩
        intro y' h1 h2 h3
        have hOy' := I.desc_ord hvV h1
        have hne : y' ≠ u := by
          intro e
          subst e
          omega
        have := hset.2 y' (Rtc.trans hy1 h1) h2 hne
        rw [hFi' y' h3] at this
        exact this
      have hlv := I.low_min y hvV x w' q hSv hq1 hq2 hq3 hq4
      show (if st.P y = (u : Int) then min (st.L u) (st.L y) else st.L u) ≤ st.O w'
      rw [if_pos hPu]
      exact Int.le_trans (Int.min_le_right _ _) hlv
  · -- sep_cnt
    intro p hp
    show (if st.P v = (p : Int) then st.Sp p + (if st.O p ≤ st.L v then 1 else 0) else st.Sp p) =
      ((st.Vis.filter (fun c => decide (Pr st.P p c ∧ 0 ≤ upd st.Fi v (st.Vis.length : Int) c ∧
        st.O p ≤ (if st.P v = (c : Int) then min (st.L c) (st.L v) else st.L c)))).length : Int)
    have hlen := length_filter_update I.vis_nd
      (fun c => decide (Pr st.P p c ∧ 0 ≤ st.Fi c ∧ st.O p ≤ st.L c))
      (fun c => decide (Pr st.P p c ∧ 0 ≤ upd st.Fi v (st.Vis.length : Int) c ∧
        st.O p ≤ (if st.P v = (c : Int) then min (st.L c) (st.L v) else st.L c))) v hvV
      (by
        intro c _ hcv
        apply decide_eq_decide.mpr
        rw [upd_ne _ _ _ _ hcv]
        by_cases hPc : st.P v = (c : Int)
        · have hcF := (hparS c hPc).2.1
          constructor
          · intro h; omega
          · intro h; omega
        · rw [if_neg hPc])
      (by
        simp only [decide_eq_false_iff_not]
        intro h
        omega)
    rw [hlen]
    have hsc := I.sep_cnt p hp
    have hLv : (if st.P v = (v : Int) then min (st.L v) (st.L v) else st.L v) = st.L v := by
      rw [if_neg hnotself]
    by_cases hPp : st.P v = (p : Int)
    · rw [if_pos hPp, hsc]
      simp only [upd_same, hLv]
      by_cases hle : st.O p ≤ st.L v
      · have : decide (Pr st.P p v ∧ 0 ≤ (st.Vis.length : Int) ∧ st.O p ≤ st.L v) = true := by
          simp [Pr, hPp, hle]
        rw [if_pos hle, if_pos this]
        push_cast
        rfl
      · have : decide (Pr st.P p v ∧ 0 ≤ (st.Vis.length : Int) ∧ st.O p ≤ st.L v) = false := by
          simp [Pr, hPp, hle]
        rw [if_neg hle, if_neg (by rw [this]; exact Bool.false_ne_true)]
        simp
    · rw [if_neg hPp, hsc]
      have : decide (Pr st.P p v ∧ 0 ≤ (st.Vis.length : Int) ∧ st.O p ≤ st.L v) = false := by
        rw [decide_eq_false_iff_not]
        intro h
        exact hPp h.1
      simp only [upd_same, hLv]
      rw [if_neg (by rw [this]; exact Bool.false_ne_true)]
      simp
  · -- sep_unv
    intro v' hv'
    show (if st.P v = (v' : Int) then st.Sp v' + (if st.O v' ≤ st.L v then 1 else 0) else st.Sp v') = 0
    rw [if_neg (fun h => hv' (hparS v' h).1)]
    exact I.sep_unv v' hv'

end Proofs.LowlinkPop
