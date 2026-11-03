import Proofs.LowlinkRoot

namespace Proofs.LowlinkFinal
open Proofs.PrimMath (Rtc)
open Proofs.LowlinkInv Proofs.LowlinkGraph

/-- The initial machine state: nothing visited. `L`, `It`, `Sk` are scratch. -/
def initS (L It : Nat → Int) (Sk : Nat → Nat) : St :=
  { O := fun _ => -1, L := L, P := fun _ => -1, Sp := fun _ => 0, It := It, Fi := fun _ => -1, Sk := Sk, Vis := [], sp := 0 }

theorem inv_init (n : Nat) (hd tg : Nat → Nat) (L It : Nat → Int) (Sk : Nat → Nat) : MInv n hd tg (initS L It Sk) := by
  refine ⟨List.nodup_nil, fun v hv => by simp [initS] at hv, fun t ht => by simp [initS] at ht, fun v _ => rfl,
    fun v _ => rfl, fun u v h => ?_, fun v _ => rfl, fun v hv => by simp [initS] at hv, by simp [initS],
    fun i hi => by simp [initS] at hi, fun i hi => by simp [initS] at hi, fun h => by simp [initS] at h,
    fun v hv => by simp [initS] at hv, fun v hv => by simp [initS] at hv, fun x hx => by simp [initS] at hx,
    fun v hv => by simp [initS] at hv, fun x hx => by simp [initS] at hx, fun x hx => by simp [initS] at hx,
    fun x hx => by simp [initS] at hx, fun v hv => by simp [initS] at hv, fun v hv => by simp [initS] at hv,
    fun v hv => by simp [initS] at hv, fun p hp => by simp [initS] at hp, fun v _ => rfl, fun v _ => rfl⟩
  exact absurd h (by simp [Pr, initS])

section
variable {n : Nat} {hd tg : Nat → Nat} {st : St}

/-- The parent function as an option. -/
def parO (P : Nat → Int) (v : Nat) : Option Nat := if 0 ≤ P v then some (P v).toNat else none

theorem parO_some {P : Nat → Int} {v p : Nat} : parO P v = some p ↔ P v = (p : Int) := by
  unfold parO
  constructor
  · intro h
    split at h
    · have := Option.some.inj h
      omega
    · cases h
  · intro h
    rw [if_pos (by omega)]
    congr 1
    omega

theorem PR_iff {P : Nat → Int} {u v : Nat} : PR (parO P) u v ↔ Pr P u v := parO_some

theorem desc_iff_m {P : Nat → Int} {a x : Nat} : Desc (parO P) a x ↔ DescM P a x := by
  constructor
  · intro h
    exact Rtc.mono (fun _ _ => PR_iff.mp) h
  · intro h
    exact Rtc.mono (fun _ _ => PR_iff.mpr) h

theorem toNat_lt {a b : Int} (_ha : 0 ≤ a) (h : a < b) : a.toNat < b.toNat := by omega
theorem toNat_le {a b : Int} (_ha : 0 ≤ a) (h : a ≤ b) : a.toNat ≤ b.toNat := by omega

theorem fin_all (I : MInv n hd tg st) (hsp : st.sp = 0) : ∀ x ∈ st.Vis, 0 ≤ st.Fi x := by
  intro x hx
  apply Classical.byContradiction
  intro hneg
  obtain ⟨i, hi, _⟩ := I.sk_cover x hx (by omega)
  omega

theorem final_of_inv (G : GH n hd tg) (I : MInv n hd tg st) (hsp : st.sp = 0) (hall : ∀ v, v < n → v ∈ st.Vis) :
    LlFinal n (AdjH hd tg) (parO st.P) (fun v => (st.O v).toNat) (fun v => (st.L v).toNat)
      (fun v => (st.Fi v).toNat) (fun v => (st.Sp v).toNat) := by
  have hF := fin_all I hsp
  have hlt : ∀ v ∈ st.Vis, v < n := I.vis_lt
  have hO0 : ∀ v ∈ st.Vis, 0 ≤ st.O v := fun v hv => (I.ord_lt_len hv).1
  -- a vertex with a descendant (other than itself) is visited
  have hdescV : ∀ a x, DescM st.P a x → a = x ∨ a ∈ st.Vis := by
    intro a x h
    rcases Rtc.cases_head h with e | ⟨b, hb, _⟩
    · exact Or.inl e
    · exact Or.inr (I.par_ok _ _ hb).1
  refine ⟨G.adj_lt, G.sym, G.irrefl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- par_lt
    intro v p hp
    have hp' := parO_some.mp hp
    obtain ⟨h1, h2, h3⟩ := I.par_ok p v hp'
    have hvV := I.par_vis hp'
    exact ⟨hlt v hvV, hlt p h1, h2, toNat_lt (hO0 p h1) h3⟩
  · -- ord_inj
    intro u v hu hv h
    have hu' := hall u hu
    have hv' := hall v hv
    apply I.ord_inj hu' hv'
    have := hO0 u hu'
    have := hO0 v hv'
    have h' : (st.O u).toNat = (st.O v).toNat := h
    omega
  · -- fin_gt
    intro v hv
    have hv' := hall v hv
    have := (I.fin_ok v hv' (hF v hv')).1
    have := hO0 v hv'
    show (st.O v).toNat < (st.Fi v).toNat
    omega
  · -- desc_iff
    intro v y hv hy
    have hv' := hall v hv
    have hy' := hall y hy
    rw [desc_iff_m, I.interval v hv' y hy']
    unfold finE
    rw [if_pos (hF v hv')]
    have := hO0 v hv'
    have := hO0 y hy'
    have := hF v hv'
    show _ ↔ (st.O v).toNat ≤ (st.O y).toNat ∧ (st.O y).toNat < (st.Fi v).toNat
    omega
  · -- fin_le
    intro v x h
    rw [desc_iff_m] at h
    rcases hdescV v x h with rfl | hv
    · exact Nat.le_refl _
    · have hx := I.desc_vis hv h
      have := (I.desc_fin v hv (hF v hv) x h).2
      have := hF x hx
      show (st.Fi x).toNat ≤ (st.Fi v).toNat
      omega
  · -- nbr_lt_fin
    intro x w h
    have hx := hall x (G.adj_lt x w h).1
    have := (I.nbr_fin x hx (hF x hx) w h).2
    have hw := (I.nbr_fin x hx (hF x hx) w h).1
    have := hO0 w hw
    show (st.O w).toNat < (st.Fi x).toNat
    omega
  · -- low_le
    intro v hv
    have hv' := hall v hv
    have := I.low_le v hv'
    show (st.L v).toNat ≤ (st.O v).toNat
    omega
  · -- low_mem
    intro v hv
    have hv' := hall v hv
    have hl := (I.low_le v hv').1
    rcases I.low_mem v hv' with h | ⟨x, w, hx, hxw, hnp, hw⟩
    · left
      show (st.L v).toNat = (st.O v).toNat
      omega
    · right
      refine ⟨x, w, desc_iff_m.mpr hx, hxw, ?_, ?_⟩
      · intro h
        exact hnp (parO_some.mp h)
      · show (st.O w).toNat = (st.L v).toNat
        omega
  · -- low_min
    intro v x w hx hxw hnp
    have hx' := desc_iff_m.mp hx
    have hxn := (G.adj_lt x w hxw).1
    have hv' : v ∈ st.Vis := by
      rcases hdescV v x hx' with rfl | h
      · exact hall _ hxn
      · exact h
    have hxV := hall x hxn
    obtain ⟨q, hq1, hq2, hq3⟩ := hxw
    have hit := I.it_fin x hxV (hF x hxV)
    have hl := (I.low_le v hv').1
    have hset : Settled st v x := ⟨hx', fun y _ _ _ => hF y (I.desc_vis hv' (by assumption))⟩
    have := I.low_min v hv' x w q hset hq1 (by omega) hq3 (fun h => hnp (parO_some.mpr h))
    have hwV : w ∈ st.Vis := hall w (G.adj_lt x w ⟨q, hq1, hq2, hq3⟩).2
    have := hO0 w hwV
    show (st.L v).toNat ≤ (st.O w).toNat
    omega
  · -- sep_eq
    intro p hp
    have hp' := hall p hp
    have hs := I.sep_cnt p hp'
    have hperm : st.Vis.Perm (List.range n) := by
      rw [List.perm_ext_iff_of_nodup I.vis_nd List.nodup_range]
      intro a
      rw [List.mem_range]
      constructor
      · exact fun h => hlt a h
      · exact fun h => hall a h
    let f : Nat → Bool := fun c => decide (Pr st.P p c ∧ 0 ≤ st.Fi c ∧ st.O p ≤ st.L c)
    let g : Nat → Bool := fun c => decide (parO st.P c = some p ∧ (st.O p).toNat ≤ (st.L c).toNat)
    have hfg : ∀ c ∈ List.range n, f c = g c := by
      intro c hc
      have hc' := hall c (List.mem_range.mp hc)
      have h1 := hF c hc'
      have h2 := (I.low_le c hc').1
      have h3 := hO0 p hp'
      apply decide_eq_decide.mpr
      rw [parO_some]
      unfold Pr
      constructor
      · intro h; exact ⟨h.1, by omega⟩
      · intro h; exact ⟨h.1, h1, by omega⟩
    have hlen : (st.Vis.filter f).length = ((List.range n).filter g).length := by
      rw [(hperm.filter f).length_eq]
      rw [List.filter_congr hfg]
    show (st.Sp p).toNat = ((List.range n).filter g).length
    rw [hs, ← hlen]
    exact Int.toNat_natCast _

end

end Proofs.LowlinkFinal
