import Proofs.LowlinkPush

namespace Proofs.LowlinkRoot
open Proofs.PrimMath (Rtc)
open Proofs.LowlinkInv Proofs.LowlinkPop Proofs.LowlinkPush

/-- Start a new DFS tree at the unvisited `r` (the stack is empty). -/
def rootS (hd : Nat → Nat) (st : St) (r : Nat) : St :=
  { O := upd st.O r (st.Vis.length : Int)
    L := upd st.L r (st.Vis.length : Int)
    P := st.P
    Sp := st.Sp
    It := upd st.It r (hd r : Int)
    Fi := st.Fi
    Sk := upd st.Sk 0 r
    Vis := st.Vis ++ [r]
    sp := 1 }

set_option maxHeartbeats 4000000 in
theorem inv_root {n : Nat} {hd tg : Nat → Nat} {st : St} (G : GH n hd tg) (I : MInv n hd tg st) {r : Nat}
    (hsp : st.sp = 0) (hrn : r < n) (hrU : st.O r < 0) : MInv n hd tg (rootS hd st r) := by
  have hrV : r ∉ st.Vis := fun h => by have := (I.ord_lt_len h).1; omega
  have hFr : st.Fi r = -1 := I.fin_unv r hrV
  have hPr : st.P r = -1 := I.par_none r hrV
  have hmemP : ∀ x, x ∈ (rootS hd st r).Vis ↔ x ∈ st.Vis ∨ x = r := by
    intro x
    simp [rootS]
  have hnw : ∀ x, x ∈ st.Vis → x ≠ r := fun x hx e => hrV (e ▸ hx)
  have hO' : ∀ x, x ≠ r → (rootS hd st r).O x = st.O x := fun x hx => upd_ne _ _ _ _ hx
  have hOw : (rootS hd st r).O r = (st.Vis.length : Int) := upd_same _ _ _
  have hL' : ∀ x, x ≠ r → (rootS hd st r).L x = st.L x := fun x hx => upd_ne _ _ _ _ hx
  have hLw : (rootS hd st r).L r = (st.Vis.length : Int) := upd_same _ _ _
  have hI' : ∀ x, x ≠ r → (rootS hd st r).It x = st.It x := fun x hx => upd_ne _ _ _ _ hx
  have hIw : (rootS hd st r).It r = (hd r : Int) := upd_same _ _ _
  have hfinAll : ∀ x ∈ st.Vis, 0 ≤ st.Fi x := by
    intro x hx
    apply Classical.byContradiction
    intro hneg
    obtain ⟨i, hi, _⟩ := I.sk_cover x hx (by omega)
    omega
  have hlen : (rootS hd st r).Vis.length = st.Vis.length + 1 := by simp [rootS]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, fun x hx => I.fin_unv x (fun h => hx ((hmemP x).mpr (Or.inl h))), ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, I.par_neg⟩
  · -- vis_nd
    show (st.Vis ++ [r]).Nodup
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
    · exact hrn
  · -- vis_ord
    intro t ht
    have ht' : t < st.Vis.length + 1 := by simpa [rootS] using ht
    by_cases hlt : t < st.Vis.length
    · have : (rootS hd st r).Vis.getD t 0 = st.Vis.getD t 0 := by
        show (st.Vis ++ [r]).getD t 0 = st.Vis.getD t 0
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [this]
      have hm : st.Vis.getD t 0 ∈ st.Vis := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        exact List.getElem_mem _
      rw [hO' _ (hnw _ hm)]
      exact I.vis_ord t hlt
    · have ht2 : t = st.Vis.length := by omega
      subst ht2
      have : (rootS hd st r).Vis.getD st.Vis.length 0 = r := by
        show (st.Vis ++ [r]).getD st.Vis.length 0 = r
        simp [List.getD_eq_getElem?_getD]
      rw [this, hOw]
  · -- unv_ord
    intro x hx
    have hx' : x ∉ st.Vis ∧ x ≠ r := by
      constructor
      · intro h; exact hx ((hmemP x).mpr (Or.inl h))
      · intro e; exact hx ((hmemP x).mpr (Or.inr e))
    rw [hO' x hx'.2]
    exact I.unv_ord x hx'.1
  · -- par_none
    intro x hx
    exact I.par_none x (fun h => hx ((hmemP x).mpr (Or.inl h)))
  · -- par_ok
    intro u x hux
    obtain ⟨h1, h2, h3⟩ := I.par_ok u x hux
    have hxV := I.par_vis hux
    refine ⟨(hmemP u).mpr (Or.inl h1), h2, ?_⟩
    show (rootS hd st r).O u < (rootS hd st r).O x
    rw [hO' u (hnw u h1), hO' x (hnw x hxV)]
    exact h3
  · -- fin_ok
    intro x hx hfx
    rcases (hmemP x).mp hx with h | rfl
    · have := I.fin_ok x h hfx
      refine ⟨?_, ?_⟩
      · show (rootS hd st r).O x < st.Fi x
        rw [hO' x (hnw x h)]
        exact this.1
      · show st.Fi x ≤ (((rootS hd st r).Vis.length : Nat) : Int)
        rw [hlen]
        push_cast
        omega
    · exfalso
      have : 0 ≤ st.Fi x := hfx
      omega
  · -- sp_le
    show 1 ≤ (st.Vis ++ [r]).length
    simp
  · -- sk_mem
    intro i hi
    have hi0 : i = 0 := by
      have : i < 1 := hi
      omega
    subst hi0
    show (upd st.Sk 0 r) 0 ∈ (rootS hd st r).Vis ∧ (rootS hd st r).Fi ((upd st.Sk 0 r) 0) < 0
    rw [upd_same]
    exact ⟨(hmemP r).mpr (Or.inr rfl), by show st.Fi r < 0; omega⟩
  · -- sk_par
    intro i hi
    have : i + 1 < 1 := hi
    omega
  · -- sk_root
    intro _
    show st.P ((upd st.Sk 0 r) 0) = -1
    rw [upd_same]
    exact hPr
  · -- sk_cover
    intro x hx hfx
    rcases (hmemP x).mp hx with h | rfl
    · exfalso
      have := hfinAll x h
      have : st.Fi x < 0 := hfx
      omega
    · exact ⟨0, show 0 < 1 by omega, show (upd st.Sk 0 x) 0 = x from upd_same _ _ _⟩
  · -- interval
    intro x hx y hy
    have hfe : ∀ z ∈ st.Vis, finE (rootS hd st r) z = finE st z := by
      intro z hz
      have := hfinAll z hz
      show (if 0 ≤ st.Fi z then st.Fi z else (((rootS hd st r).Vis.length : Nat) : Int)) =
        (if 0 ≤ st.Fi z then st.Fi z else (st.Vis.length : Int))
      rw [if_pos this, if_pos this]
    have hfeR : finE (rootS hd st r) r = (st.Vis.length : Int) + 1 := by
      show (if 0 ≤ st.Fi r then st.Fi r else (((rootS hd st r).Vis.length : Nat) : Int)) = _
      rw [if_neg (by omega), hlen]
      push_cast
      rfl
    rcases (hmemP x).mp hx with hx' | rfl <;> rcases (hmemP y).mp hy with hy' | rfl
    · show DescM st.P x y ↔ (rootS hd st r).O x ≤ (rootS hd st r).O y ∧ (rootS hd st r).O y < finE (rootS hd st r) x
      rw [hfe x hx', hO' x (hnw x hx'), hO' y (hnw y hy')]
      exact I.interval x hx' y hy'
    · -- Desc x r is false
      have hnd : ¬ DescM st.P x y := by
        intro h
        rcases desc_last_aux h with e | ⟨q, _, hq⟩
        · exact hnw x hx' e
        · unfold Pr at hq
          rw [hPr] at hq
          omega
      show DescM st.P x y ↔ _
      rw [hO' x (hnw x hx'), hOw, hfe x hx']
      constructor
      · intro h; exact absurd h hnd
      · intro h
        have := (I.fin_ok x hx' (hfinAll x hx')).2
        have h2 := h.2
        unfold finE at h2
        rw [if_pos (hfinAll x hx')] at h2
        omega
    · -- r has no descendants
      have hy2 := (I.ord_lt_len hy').2
      show DescM st.P x y ↔ _
      rw [hO' y (hnw y hy'), hOw]
      constructor
      · intro h
        have : y = x := by
          apply Rtc.eq_of_stuck _ h
          intro c hc
          unfold Pr at hc
          have := (I.par_ok _ _ hc).1
          exact hrV this
        exact absurd this (hnw y hy')
      · intro h
        omega
    · rw [hOw, hfeR]
      exact ⟨fun _ => ⟨Int.le_refl _, by omega⟩, fun _ => Rtc.refl _⟩
  · -- nbr_fin
    intro x hx hfx w' hadj'
    rcases (hmemP x).mp hx with h | rfl
    · obtain ⟨hwv, hlt⟩ := I.nbr_fin x h hfx w' hadj'
      refine ⟨(hmemP w').mpr (Or.inl hwv), ?_⟩
      show (rootS hd st r).O w' < st.Fi x
      rw [hO' w' (hnw w' hwv)]
      exact hlt
    · exfalso
      have : 0 ≤ st.Fi x := hfx
      omega
  · -- desc_fin
    intro u hu hfu x hx
    rcases (hmemP u).mp hu with hu' | rfl
    · exact I.desc_fin u hu' hfu x hx
    · exfalso
      have : 0 ≤ st.Fi u := hfu
      omega
  · -- it_rng
    intro x hx
    rcases (hmemP x).mp hx with h | rfl
    · rw [hI' x (hnw x h)]
      exact I.it_rng x h
    · rw [hIw]
      exact ⟨Int.le_refl _, by exact_mod_cast G.mono x hrn⟩
  · -- it_scan
    intro x hx q' hq1 hq2
    rcases (hmemP x).mp hx with h | rfl
    · rw [hI' x (hnw x h)] at hq2
      exact (hmemP _).mpr (Or.inl (I.it_scan x h q' hq1 hq2))
    · rw [hIw] at hq2
      omega
  · -- it_fin
    intro x hx hfx
    rcases (hmemP x).mp hx with h | rfl
    · rw [hI' x (hnw x h)]
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
        have hbV : b ∈ st.Vis := by
          apply I.vis_of_nn
          have := (I.low_le x h).1
          omega
        refine ⟨a, b, hxa, hab, hnp, ?_⟩
        rw [hO' b (hnw b hbV)]
        exact hb
    · left
      rw [hLw, hOw]
  · -- low_min
    intro u hu x w' q' hset hq1 hq2 hq3 hq4
    rcases (hmemP u).mp hu with hu' | rfl
    · have hxV := I.desc_vis hu' hset.1
      have hxw := hnw x hxV
      rw [hI' x hxw] at hq2
      have hw'V := I.it_scan x hxV q' hq1 hq2
      rw [hq3] at hw'V
      rw [hL' u (hnw u hu'), hO' w' (hnw w' hw'V)]
      exact I.low_min u hu' x w' q' hset hq1 hq2 hq3 hq4
    · have hxw : x = u := by
        apply Rtc.eq_of_stuck _ hset.1
        intro c hc
        unfold Pr at hc
        have := (I.par_ok _ _ hc).1
        exact hrV this
      subst hxw
      rw [hIw] at hq2
      omega
  · -- sep_cnt
    intro p hp
    rcases (hmemP p).mp hp with hp' | rfl
    · show st.Sp p = ((((st.Vis ++ [r]).filter (fun c => decide (Pr st.P p c ∧ 0 ≤ st.Fi c ∧
        (upd st.O r (st.Vis.length : Int)) p ≤ (upd st.L r (st.Vis.length : Int)) c))).length : Nat) : Int)
      rw [List.filter_append]
      have h1 : (st.Vis.filter (fun c => decide (Pr st.P p c ∧ 0 ≤ st.Fi c ∧
          (upd st.O r (st.Vis.length : Int)) p ≤ (upd st.L r (st.Vis.length : Int)) c))) =
          st.Vis.filter (fun c => decide (Pr st.P p c ∧ 0 ≤ st.Fi c ∧ st.O p ≤ st.L c)) := by
        apply List.filter_congr
        intro c hc
        rw [upd_ne _ _ _ _ (hnw c hc), upd_ne _ _ _ _ (hnw p hp')]
      have h2 : ([r].filter (fun c => decide (Pr st.P p c ∧ 0 ≤ st.Fi c ∧
          (upd st.O r (st.Vis.length : Int)) p ≤ (upd st.L r (st.Vis.length : Int)) c))) = [] := by
        simp only [List.filter_cons, List.filter_nil]
        rw [if_neg]
        intro h
        have := of_decide_eq_true h
        have h3 : 0 ≤ st.Fi r := this.2.1
        omega
      rw [h1, h2, List.append_nil]
      exact I.sep_cnt p hp'
    · show st.Sp p = ((((st.Vis ++ [p]).filter (fun c => decide (Pr st.P p c ∧ 0 ≤ st.Fi c ∧
        (upd st.O p (st.Vis.length : Int)) p ≤ (upd st.L p (st.Vis.length : Int)) c))).length : Nat) : Int)
      have hnil : ((st.Vis ++ [p]).filter (fun c => decide (Pr st.P p c ∧ 0 ≤ st.Fi c ∧
          (upd st.O p (st.Vis.length : Int)) p ≤ (upd st.L p (st.Vis.length : Int)) c))) = [] := by
        rw [List.filter_eq_nil_iff]
        intro c hc
        simp only [decide_eq_true_eq]
        intro h
        rcases List.mem_append.mp hc with hc' | hc'
        · exact hrV ((I.par_ok _ _ h.1).1)
        · have : c = p := by simpa using hc'
          subst this
          have h0 : st.P c = (c : Int) := h.1
          omega
      rw [hnil]
      simp
      exact I.sep_unv _ hrV
  · -- sep_unv
    intro x hx
    exact I.sep_unv x (fun h => hx ((hmemP x).mpr (Or.inl h)))

end Proofs.LowlinkRoot
