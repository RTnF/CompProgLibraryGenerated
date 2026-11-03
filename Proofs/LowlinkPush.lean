import Proofs.LowlinkPop

namespace Proofs.LowlinkPush
open Proofs.PrimMath (Rtc)
open Proofs.LowlinkInv Proofs.LowlinkPop

/-- Pushing the unvisited `w`, found through the arc `It v` of the top `v`. -/
def pushS (hd : Nat → Nat) (st : St) (v w : Nat) : St :=
  { O := upd st.O w (st.Vis.length : Int)
    L := upd st.L w (st.Vis.length : Int)
    P := upd st.P w (v : Int)
    Sp := st.Sp
    It := upd (upd st.It v (st.It v + 1)) w (hd w : Int)
    Fi := st.Fi
    Sk := upd st.Sk st.sp w
    Vis := st.Vis ++ [w]
    sp := st.sp + 1 }

section
variable {n : Nat} {hd tg : Nat → Nat} {st : St} {v w : Nat}

theorem pushP_ne (x : Nat) (hx : x ≠ w) (p : Nat → Int) (a : Int) : upd p w a x = p x := upd_ne _ _ _ _ hx

/-- Paths between old vertices are unchanged by the push. -/
theorem desc_push_old (I : MInv n hd tg st) (hw : w ∉ st.Vis) (a : Nat) (c : Int) :
    ∀ x, x ∈ st.Vis → (DescM (upd st.P w c) a x ↔ DescM st.P a x) := by
  intro x hx
  constructor
  · intro h
    have key : ∀ x', DescM (upd st.P w c) a x' → x' ≠ w → DescM st.P a x' := by
      intro x' h'
      induction h' with
      | refl => intro _; exact Rtc.refl _
      | @tail b x'' hab hbc ih =>
        intro hx''
        unfold Pr at hbc
        rw [upd_ne _ _ _ _ hx''] at hbc
        have hbV := (I.par_ok _ _ hbc).1
        have hbw : b ≠ w := fun e => hw (e ▸ hbV)
        exact Rtc.tail (ih hbw) hbc
    exact key x h (fun e => hw (e ▸ hx))
  · intro h
    have key : ∀ x', DescM st.P a x' → DescM (upd st.P w c) a x' := by
      intro x' h'
      induction h' with
      | refl => exact Rtc.refl _
      | tail hab hbc ih =>
        have hcV := I.par_vis hbc
        have hcw : _ ≠ w := fun e => hw (e ▸ hcV)
        refine Rtc.tail ih ?_
        unfold Pr at hbc ⊢
        rw [upd_ne _ _ _ _ hcw]
        exact hbc
    exact key x h

theorem desc_push_vis (I : MInv n hd tg st) (_hw : w ∉ st.Vis) (c : Int) {a x : Nat} (ha : a ∈ st.Vis)
    (h : DescM (upd st.P w c) a x) (hx : x ≠ w) : x ∈ st.Vis := by
  induction h with
  | refl => exact ha
  | tail _ hbc _ =>
    unfold Pr at hbc
    rw [upd_ne _ _ _ _ hx] at hbc
    exact I.par_vis hbc

/-- Nothing is a child of the new vertex, and the new vertex has no descendants but itself. -/
theorem desc_from_new (I : MInv n hd tg st) (hw : w ∉ st.Vis) (hv : v ∈ st.Vis) {x : Nat}
    (h : DescM (upd st.P w (v : Int)) w x) : x = w := by
  apply Rtc.eq_of_stuck _ h
  intro c hc
  unfold Pr at hc
  by_cases hcw : c = w
  · subst hcw
    rw [upd_same] at hc
    have : v = c := by omega
    exact hw (this ▸ hv)
  · rw [upd_ne _ _ _ _ hcw] at hc
    have := (I.par_ok _ _ hc).1
    exact hw this

theorem desc_to_new (I : MInv n hd tg st) (hw : w ∉ st.Vis) (hv : v ∈ st.Vis) {a : Nat} (ha : a ∈ st.Vis) :
    DescM (upd st.P w (v : Int)) a w ↔ DescM st.P a v := by
  constructor
  · intro h
    rcases desc_last_aux h with e | ⟨q', hq', hpq'⟩
    · exact absurd (e ▸ ha) hw
    · unfold Pr at hpq'
      rw [upd_same] at hpq'
      have : q' = v := by omega
      subst this
      exact (desc_push_old I hw a _ q' hv).mp hq'
  · intro h
    refine Rtc.tail ((desc_push_old I hw a _ v hv).mpr h) ?_
    unfold Pr
    rw [upd_same]

end


set_option maxHeartbeats 4000000 in
theorem inv_push {n : Nat} {hd tg : Nat → Nat} {st : St} (G : GH n hd tg) (I : MInv n hd tg st) {v w q : Nat}
    (hsp : 0 < st.sp) (hv : st.Sk (st.sp - 1) = v) (hq : (q : Int) = st.It v) (hit : (q : Int) < (hd (v + 1) : Int))
    (hw : tg q = w) (hwU : st.O w < 0) : MInv n hd tg (pushS hd st v w) := by
  have hvm := I.sk_mem (st.sp - 1) (by omega)
  rw [hv] at hvm
  obtain ⟨hvV, hfv⟩ := hvm
  have hwV : w ∉ st.Vis := fun h => by have := (I.ord_lt_len h).1; omega
  have hrng := I.it_rng v hvV
  have hadj : AdjH hd tg v w := ⟨q, by omega, by omega, hw⟩
  have hwn : w < n := (G.adj_lt v w hadj).2
  have hvw : v ≠ w := fun e => hwV (e ▸ hvV)
  have hOv := I.ord_lt_len hvV
  have hFw : st.Fi w = -1 := I.fin_unv w hwV
  have hmemP : ∀ x, x ∈ (pushS hd st v w).Vis ↔ x ∈ st.Vis ∨ x = w := by
    intro x
    simp [pushS]
  have hnw : ∀ x, x ∈ st.Vis → x ≠ w := fun x hx e => hwV (e ▸ hx)
  have hO' : ∀ x, x ≠ w → (pushS hd st v w).O x = st.O x := fun x hx => upd_ne _ _ _ _ hx
  have hOw : (pushS hd st v w).O w = (st.Vis.length : Int) := upd_same _ _ _
  have hL' : ∀ x, x ≠ w → (pushS hd st v w).L x = st.L x := fun x hx => upd_ne _ _ _ _ hx
  have hLw : (pushS hd st v w).L w = (st.Vis.length : Int) := upd_same _ _ _
  have hP' : ∀ x, x ≠ w → (pushS hd st v w).P x = st.P x := fun x hx => upd_ne _ _ _ _ hx
  have hPw : (pushS hd st v w).P w = (v : Int) := upd_same _ _ _
  have hI' : ∀ x, x ≠ w → (pushS hd st v w).It x = (upd st.It v (st.It v + 1)) x := fun x hx => upd_ne _ _ _ _ hx
  have hIw : (pushS hd st v w).It w = (hd w : Int) := upd_same _ _ _
  have hS' : ∀ i, i ≠ st.sp → (pushS hd st v w).Sk i = st.Sk i := fun i hi => upd_ne _ _ _ _ hi
  have hSsp : (pushS hd st v w).Sk st.sp = w := upd_same _ _ _
  have hdesc : ∀ a x, a ∈ st.Vis → x ∈ st.Vis → (DescM (pushS hd st v w).P a x ↔ DescM st.P a x) :=
    fun a x ha hx => desc_push_old I hwV a _ x hx
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun x hx => I.fin_unv x (fun h => hx ((hmemP x).mpr (Or.inl h))), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- vis_nd
    show (st.Vis ++ [w]).Nodup
    rw [List.nodup_append]
    refine ⟨I.vis_nd, by simp, ?_⟩
    intro a ha b hb
    simp at hb
    subst hb
    exact hnw a ha
  · -- vis_lt
    intro x hx
    rcases (hmemP x).mp hx with h | rfl
    · exact I.vis_lt x h
    · exact hwn
  · -- vis_ord
    intro t ht
    have ht' : t < st.Vis.length + 1 := by simpa [pushS] using ht
    by_cases hlt : t < st.Vis.length
    · have : (pushS hd st v w).Vis.getD t 0 = st.Vis.getD t 0 := by
        show (st.Vis ++ [w]).getD t 0 = st.Vis.getD t 0
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [this]
      have hm : st.Vis.getD t 0 ∈ st.Vis := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        exact List.getElem_mem _
      rw [hO' _ (hnw _ hm)]
      exact I.vis_ord t hlt
    · have ht2 : t = st.Vis.length := by omega
      subst ht2
      have : (pushS hd st v w).Vis.getD st.Vis.length 0 = w := by
        show (st.Vis ++ [w]).getD st.Vis.length 0 = w
        simp [List.getD_eq_getElem?_getD]
      rw [this, hOw]
  · -- unv_ord
    intro x hx
    have hx' : x ∉ st.Vis ∧ x ≠ w := by
      constructor
      · intro h; exact hx ((hmemP x).mpr (Or.inl h))
      · intro e; exact hx ((hmemP x).mpr (Or.inr e))
    rw [hO' x hx'.2]
    exact I.unv_ord x hx'.1
  · -- par_none
    intro x hx
    have hx' : x ∉ st.Vis ∧ x ≠ w := by
      constructor
      · intro h; exact hx ((hmemP x).mpr (Or.inl h))
      · intro e; exact hx ((hmemP x).mpr (Or.inr e))
    rw [hP' x hx'.2]
    exact I.par_none x hx'.1
  · -- par_ok
    intro u x hux
    by_cases hxw : x = w
    · subst hxw
      have e : (v : Int) = (u : Int) := by
        have : (pushS hd st v x).P x = (u : Int) := hux
        rw [hPw] at this
        exact this
      have : u = v := by omega
      subst this
      refine ⟨(hmemP _).mpr (Or.inl hvV), hadj, ?_⟩
      show (pushS hd st u x).O u < (pushS hd st u x).O x
      rw [hO' u hvw, hOw]
      exact hOv.2
    · have hux' : st.P x = (u : Int) := by
        have : (pushS hd st v w).P x = (u : Int) := hux
        rwa [hP' x hxw] at this
      obtain ⟨h1, h2, h3⟩ := I.par_ok u x hux'
      have hxV := I.par_vis hux'
      refine ⟨(hmemP u).mpr (Or.inl h1), h2, ?_⟩
      show (pushS hd st v w).O u < (pushS hd st v w).O x
      rw [hO' u (hnw u h1), hO' x hxw]
      exact h3
  · -- fin_ok
    intro x hx hfx
    rcases (hmemP x).mp hx with h | rfl
    · have := I.fin_ok x h hfx
      have hl : (pushS hd st v w).Vis.length = st.Vis.length + 1 := by simp [pushS]
      refine ⟨?_, ?_⟩
      · show (pushS hd st v w).O x < st.Fi x
        rw [hO' x (hnw x h)]
        exact this.1
      · show st.Fi x ≤ (((pushS hd st v w).Vis.length : Nat) : Int)
        rw [hl]
        push_cast
        omega
    · exfalso
      have : 0 ≤ st.Fi x := hfx
      omega
  · -- sp_le
    show st.sp + 1 ≤ (st.Vis ++ [w]).length
    have := I.sp_le
    simp
    omega
  · -- sk_mem
    intro i hi
    have hi' : i < st.sp + 1 := hi
    by_cases his : i = st.sp
    · subst his
      rw [hSsp]
      exact ⟨(hmemP w).mpr (Or.inr rfl), by show st.Fi w < 0; omega⟩
    · have hm := I.sk_mem i (by omega)
      rw [hS' i his]
      exact ⟨(hmemP _).mpr (Or.inl hm.1), hm.2⟩
  · -- sk_par
    intro i hi
    have hi' : i + 1 < st.sp + 1 := hi
    by_cases hlast : i + 1 = st.sp
    · rw [hlast, hSsp, hS' i (by omega)]
      have e : i = st.sp - 1 := by omega
      rw [e, hv]
      exact hPw
    · have hm := I.sk_par i (by omega)
      have hmV := (I.sk_mem (i + 1) (by omega)).1
      rw [hS' i (by omega), hS' (i + 1) hlast]
      unfold Pr at hm ⊢
      rw [hP' _ (hnw _ hmV)]
      exact hm
  · -- sk_root
    intro h0
    have := I.sk_root hsp
    have hmV := (I.sk_mem 0 hsp).1
    rw [hS' 0 (by omega), hP' _ (hnw _ hmV)]
    exact this
  · -- sk_cover
    intro x hx hfx
    rcases (hmemP x).mp hx with h | rfl
    · obtain ⟨i, hi, e⟩ := I.sk_cover x h hfx
      exact ⟨i, show i < st.sp + 1 by omega, by rw [hS' i (by omega)]; exact e⟩
    · exact ⟨st.sp, show st.sp < st.sp + 1 by omega, hSsp⟩
  · -- interval
    intro x hx y hy
    have hlen : (pushS hd st v w).Vis.length = st.Vis.length + 1 := by simp [pushS]
    have hfe : ∀ z, finE (pushS hd st v w) z = if 0 ≤ st.Fi z then st.Fi z else ((st.Vis.length : Int) + 1) := by
      intro z
      show (if 0 ≤ st.Fi z then st.Fi z else (((pushS hd st v w).Vis.length : Nat) : Int)) = _
      rw [hlen]
      push_cast
      rfl
    rcases (hmemP x).mp hx with hx' | rfl <;> rcases (hmemP y).mp hy with hy' | rfl
    · -- old, old
      rw [hdesc x y hx' hy', I.interval x hx' y hy', hO' x (hnw x hx'), hO' y (hnw y hy'), hfe]
      have hy2 := (I.ord_lt_len hy').2
      have hfx := I.fin_ok x hx'
      unfold finE
      by_cases hf : 0 ≤ st.Fi x
      · simp only [if_pos hf]
      · simp only [if_neg hf]
        constructor
        · intro h; exact ⟨h.1, by omega⟩
        · intro h; exact ⟨h.1, hy2⟩
    · -- old, new
      rw [show DescM (pushS hd st v y).P x y ↔ DescM st.P x v from desc_to_new I hwV hvV hx', hO' x (hnw x hx'), hOw, hfe]
      have hx2 := (I.ord_lt_len hx').2
      by_cases hf : 0 ≤ st.Fi x
      · have hnd := I.fin_not_desc_top hx' hf hsp
        rw [hv] at hnd
        have := (I.fin_ok x hx' hf).2
        rw [if_pos hf]
        constructor
        · intro h; exact absurd h hnd
        · intro h; omega
      · have hd1 := I.unfin_desc_top hx' (by omega) hsp
        rw [hv] at hd1
        rw [if_neg hf]
        exact ⟨fun _ => ⟨by omega, by omega⟩, fun _ => hd1⟩
    · -- new, old
      have hy2 := (I.ord_lt_len hy').2
      rw [hO' y (hnw y hy'), hOw]
      constructor
      · intro h
        have := desc_from_new I hwV hvV h
        exact absurd this (hnw y hy')
      · intro h
        omega
    · -- new, new
      rw [hOw, hfe, if_neg (by omega)]
      exact ⟨fun _ => ⟨Int.le_refl _, by omega⟩, fun _ => Rtc.refl _⟩
  · -- nbr_fin
    intro x hx hfx w' hadj'
    rcases (hmemP x).mp hx with h | rfl
    · obtain ⟨hwv, hlt⟩ := I.nbr_fin x h hfx w' hadj'
      refine ⟨(hmemP w').mpr (Or.inl hwv), ?_⟩
      show (pushS hd st v w).O w' < st.Fi x
      rw [hO' w' (hnw w' hwv)]
      exact hlt
    · exfalso
      have : 0 ≤ st.Fi x := hfx
      omega
  · -- desc_fin
    intro u hu hfu x hx
    rcases (hmemP u).mp hu with hu' | rfl
    · by_cases hxw : x = w
      · subst hxw
        exfalso
        have h1 := (desc_to_new I hwV hvV hu').mp hx
        have := (I.desc_fin u hu' hfu v h1).1
        omega
      · have hxV := desc_push_vis I hwV _ hu' hx hxw
        have hx' := (hdesc u x hu' hxV).mp hx
        exact I.desc_fin u hu' hfu x hx'
    · exfalso
      have : 0 ≤ st.Fi u := hfu
      omega
  · -- it_rng
    intro x hx
    rcases (hmemP x).mp hx with h | rfl
    · have hxw := hnw x h
      by_cases hxv : x = v
      · subst hxv
        rw [hI' x hxw, upd_same]
        omega
      · rw [hI' x hxw, upd_ne _ _ _ _ hxv]
        exact I.it_rng x h
    · rw [hIw]
      exact ⟨Int.le_refl _, by exact_mod_cast G.mono x hwn⟩
  · -- it_scan
    intro x hx q' hq1 hq2
    rcases (hmemP x).mp hx with h | rfl
    · have hxw := hnw x h
      by_cases hxv : x = v
      · subst hxv
        rw [hI' x hxw, upd_same] at hq2
        by_cases hlt : (q' : Int) < st.It x
        · exact (hmemP _).mpr (Or.inl (I.it_scan x h q' hq1 hlt))
        · have : q' = q := by omega
          subst this
          rw [hw]
          exact (hmemP w).mpr (Or.inr rfl)
      · rw [hI' x hxw, upd_ne _ _ _ _ hxv] at hq2
        exact (hmemP _).mpr (Or.inl (I.it_scan x h q' hq1 hq2))
    · rw [hIw] at hq2
      omega
  · -- it_fin
    intro x hx hfx
    rcases (hmemP x).mp hx with h | rfl
    · have hxw := hnw x h
      have hxv : x ≠ v := by
        intro e
        subst e
        have : 0 ≤ st.Fi x := hfx
        omega
      rw [hI' x hxw, upd_ne _ _ _ _ hxv]
      exact I.it_fin x h hfx
    · exfalso
      have : 0 ≤ st.Fi x := hfx
      omega
  · -- low_le
    intro x hx
    rcases (hmemP x).mp hx with h | rfl
    · rw [hL' x (hnw x h), hO' x (hnw x h)]
      exact I.low_le x h
    · rw [hLw, hOw]
      exact ⟨Int.natCast_nonneg _, Int.le_refl _⟩
  · -- low_mem
    intro x hx
    rcases (hmemP x).mp hx with h | rfl
    · have hxw := hnw x h
      rw [hL' x hxw, hO' x hxw]
      rcases I.low_mem x h with heq | ⟨a, b, hxa, hab, hnp, hb⟩
      · exact Or.inl heq
      · right
        have haV := I.desc_vis h hxa
        have hbV : b ∈ st.Vis := by
          apply I.vis_of_nn
          have := (I.low_le x h).1
          omega
        refine ⟨a, b, (hdesc x a h haV).mpr hxa, hab, ?_, ?_⟩
        · rw [hP' a (hnw a haV)]
          exact hnp
        · rw [hO' b (hnw b hbV)]
          exact hb
    · left
      rw [hLw, hOw]
  · -- low_min
    intro u hu x w' q' hset hq1 hq2 hq3 hq4
    rcases (hmemP u).mp hu with hu' | rfl
    · have hxw : x ≠ w := by
        intro e
        subst e
        by_cases hux : u = x
        · subst hux
          exact hnw u hu' rfl
        · have := hset.2 x hset.1 (Rtc.refl _) (Ne.symm hux)
          have h' : 0 ≤ st.Fi x := this
          omega
      have hxV := desc_push_vis I hwV _ hu' hset.1 hxw
      have hset' : Settled st u x := by
        refine ⟨(hdesc u x hu' hxV).mp hset.1, ?_⟩
        intro y h1 h2 h3
        have hyV := I.desc_vis hu' h1
        exact hset.2 y ((hdesc u y hu' hyV).mpr h1) ((hdesc y x hyV hxV).mpr h2) h3
      rw [hL' u (hnw u hu')]
      have hP4 : st.P x ≠ (w' : Int) := by
        have : (pushS hd st v w).P x ≠ (w' : Int) := hq4
        rwa [hP' x hxw] at this
      by_cases hxv : x = v
      · subst hxv
        rw [hI' x hxw, upd_same] at hq2
        by_cases hlt : (q' : Int) < st.It x
        · have hw'V := I.it_scan x hxV q' hq1 hlt
          rw [hq3] at hw'V
          rw [hO' w' (hnw w' hw'V)]
          exact I.low_min u hu' x w' q' hset' hq1 hlt hq3 hP4
        · have hqq : q' = q := by omega
          subst hqq
          rw [hw] at hq3
          subst hq3
          have huv : u = x := by
            apply Classical.byContradiction
            intro hne
            have := hset'.2 x hset'.1 (Rtc.refl _) (Ne.symm hne)
            omega
          subst huv
          rw [hOw]
          have := (I.low_le u hu').2
          omega
      · rw [hI' x hxw, upd_ne _ _ _ _ hxv] at hq2
        have hw'V := I.it_scan x hxV q' hq1 hq2
        rw [hq3] at hw'V
        rw [hO' w' (hnw w' hw'V)]
        exact I.low_min u hu' x w' q' hset' hq1 hq2 hq3 hP4
    · -- u is the new vertex
      have hxw := desc_from_new I hwV hvV hset.1
      subst hxw
      rw [hIw] at hq2
      omega
  · -- sep_cnt
    intro p hp
    rcases (hmemP p).mp hp with hp' | rfl
    · show st.Sp p = ((((st.Vis ++ [w]).filter (fun c => decide (Pr (upd st.P w (v : Int)) p c ∧ 0 ≤ st.Fi c ∧
        (upd st.O w (st.Vis.length : Int)) p ≤ (upd st.L w (st.Vis.length : Int)) c))).length : Nat) : Int)
      rw [List.filter_append]
      have h1 : (st.Vis.filter (fun c => decide (Pr (upd st.P w (v : Int)) p c ∧ 0 ≤ st.Fi c ∧
          (upd st.O w (st.Vis.length : Int)) p ≤ (upd st.L w (st.Vis.length : Int)) c))) =
          st.Vis.filter (fun c => decide (Pr st.P p c ∧ 0 ≤ st.Fi c ∧ st.O p ≤ st.L c)) := by
        apply List.filter_congr
        intro c hc
        have hcw := hnw c hc
        unfold Pr
        rw [upd_ne _ _ _ _ hcw, upd_ne _ _ _ _ hcw, upd_ne _ _ _ _ (hnw p hp')]
      have h2 : ([w].filter (fun c => decide (Pr (upd st.P w (v : Int)) p c ∧ 0 ≤ st.Fi c ∧
          (upd st.O w (st.Vis.length : Int)) p ≤ (upd st.L w (st.Vis.length : Int)) c))) = [] := by
        simp only [List.filter_cons, List.filter_nil]
        rw [if_neg]
        intro h
        have := of_decide_eq_true h
        have h3 : 0 ≤ st.Fi w := this.2.1
        omega
      rw [h1, h2, List.append_nil]
      exact I.sep_cnt p hp'
    · show st.Sp p = ((((st.Vis ++ [p]).filter (fun c => decide (Pr (upd st.P p (v : Int)) p c ∧ 0 ≤ st.Fi c ∧
        (upd st.O p (st.Vis.length : Int)) p ≤ (upd st.L p (st.Vis.length : Int)) c))).length : Nat) : Int)
      have hnil : ((st.Vis ++ [p]).filter (fun c => decide (Pr (upd st.P p (v : Int)) p c ∧ 0 ≤ st.Fi c ∧
          (upd st.O p (st.Vis.length : Int)) p ≤ (upd st.L p (st.Vis.length : Int)) c))) = [] := by
        rw [List.filter_eq_nil_iff]
        intro c hc
        simp only [decide_eq_true_eq]
        intro h
        rcases List.mem_append.mp hc with hc' | hc'
        · have hcw := hnw c hc'
          have h0 : (upd st.P p (v : Int)) c = (p : Int) := h.1
          rw [upd_ne _ _ _ _ hcw] at h0
          exact hwV ((I.par_ok _ _ h0).1)
        · have : c = p := by simpa using hc'
          subst this
          have h0 : (upd st.P c (v : Int)) c = (c : Int) := h.1
          rw [upd_same] at h0
          exact hvw (by omega)
      rw [hnil]
      simp
      exact I.sep_unv _ hwV
  · -- sep_unv
    intro x hx
    have hx' : x ∉ st.Vis := fun h => hx ((hmemP x).mpr (Or.inl h))
    exact I.sep_unv x hx'
  · -- par_neg
    intro x hx
    by_cases hxw : x = w
    · subst hxw
      have : (pushS hd st v x).P x = (v : Int) := hPw
      omega
    · rw [hP' x hxw] at hx ⊢
      exact I.par_neg x hx

end Proofs.LowlinkPush
