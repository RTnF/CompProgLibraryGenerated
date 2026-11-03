import Proofs.PrimMath

namespace Proofs.LowlinkGraph
open Proofs.PrimMath (Rtc)

/-- `u` is the DFS parent of `v`. -/
def PR (par : Nat → Option Nat) (u v : Nat) : Prop := par v = some u

/-- `a` is an ancestor of `x` (or `a = x`) in the DFS forest. -/
abbrev Desc (par : Nat → Option Nat) (a x : Nat) : Prop := Rtc (PR par) a x

/-- Head induction on `Rtc`. -/
theorem rtc_head_ind {R : Nat → Nat → Prop} {a c : Nat} (h : Rtc R a c) (P : Nat → Prop) (hc : P c)
    (step : ∀ b d, R b d → Rtc R d c → P d → P b) : P a := by
  induction h generalizing P with
  | refl => exact hc
  | @tail b c' hab hbc ih =>
    have hb : P b := step b c' hbc (Rtc.refl _) hc
    exact ih P hb (fun x y hxy hyb hPy => step x y hxy (Rtc.tail hyb hbc) hPy)

/-- Walking down a chain `c → ... → a`, every step `(u, y)` (with `c →* u` and `y →* a`) is an `E`-edge. -/
theorem chain_path {R E : Nat → Nat → Prop} {c a : Nat} (h : Rtc R c a)
    (hE : ∀ u y, R u y → Rtc R c u → Rtc R y a → E u y) : Rtc E c a := by
  have key := rtc_head_ind h (fun x => Rtc R c x → Rtc E x a) (fun _ => Rtc.refl _) (by
    intro b d hbd hda ih hcb
    exact Rtc.head (hE b d hbd hcb hda) (ih (Rtc.tail hcb hbd)))
  exact key (Rtc.refl _)

theorem desc_last {par : Nat → Option Nat} {a x : Nat} (h : Desc par a x) :
    a = x ∨ ∃ q, Desc par a q ∧ par x = some q := by
  cases h with
  | refl => exact Or.inl rfl
  | tail hab hbc => exact Or.inr ⟨_, hab, hbc⟩

/-- Two ancestors of the same vertex are comparable. -/
theorem desc_comparable {par : Nat → Option Nat} {a b x : Nat} (ha : Desc par a x) (hb : Desc par b x) :
    Desc par a b ∨ Desc par b a := by
  induction ha generalizing b with
  | refl => exact Or.inr hb
  | @tail m x' hax hmx ih =>
    rcases desc_last hb with rfl | ⟨q, hbq, hq⟩
    · exact Or.inl (Rtc.tail hax hmx)
    · have : q = m := by
        have h1 : par x' = some m := hmx
        rw [h1] at hq
        exact (Option.some.inj hq).symm
      subst this
      exact ih hbq

theorem desc_ord {par : Nat → Option Nat} {ord : Nat → Nat} (hp : ∀ v p, par v = some p → ord p < ord v)
    {a x : Nat} (h : Desc par a x) : ord a ≤ ord x := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail _ hbc ih =>
    have := hp _ _ hbc
    omega

structure LlFinal (n : Nat) (Adj : Nat → Nat → Prop) (par : Nat → Option Nat) (ord low fin sep : Nat → Nat) : Prop where
  adj_lt : ∀ x w, Adj x w → x < n ∧ w < n
  adj_sym : ∀ x w, Adj x w → Adj w x
  adj_irrefl : ∀ x, ¬ Adj x x
  par_lt : ∀ v p, par v = some p → v < n ∧ p < n ∧ Adj p v ∧ ord p < ord v
  ord_inj : ∀ u v, u < n → v < n → ord u = ord v → u = v
  fin_gt : ∀ v, v < n → ord v < fin v
  desc_iff : ∀ v y, v < n → y < n → (Desc par v y ↔ ord v ≤ ord y ∧ ord y < fin v)
  fin_le : ∀ v x, Desc par v x → fin x ≤ fin v
  nbr_lt_fin : ∀ x w, Adj x w → ord w < fin x
  low_le : ∀ v, v < n → low v ≤ ord v
  low_mem : ∀ v, v < n → low v = ord v ∨
    ∃ x w, Desc par v x ∧ Adj x w ∧ par x ≠ some w ∧ ord w = low v
  low_min : ∀ v x w, Desc par v x → Adj x w → par x ≠ some w → low v ≤ ord w
  sep_eq : ∀ p, p < n → sep p =
    ((List.range n).filter (fun c => decide (par c = some p ∧ ord p ≤ low c))).length

namespace LlFinal
variable {n : Nat} {Adj : Nat → Nat → Prop} {par : Nat → Option Nat} {ord low fin sep : Nat → Nat}

theorem ord_par (L : LlFinal n Adj par ord low fin sep) : ∀ v p, par v = some p → ord p < ord v :=
  fun v p h => (L.par_lt v p h).2.2.2

theorem desc_ord_ll (L : LlFinal n Adj par ord low fin sep) {a x : Nat} (h : Desc par a x) : ord a ≤ ord x :=
  desc_ord L.ord_par h

/-- An earlier neighbour is an ancestor. -/
theorem anc_of_adj (L : LlFinal n Adj par ord low fin sep) {x w : Nat} (h : Adj x w) (hlt : ord w < ord x) :
    Desc par w x := by
  have hn := L.adj_lt x w h
  have h2 := L.nbr_lt_fin w x (L.adj_sym x w h)
  exact (L.desc_iff w x hn.2 hn.1).mpr ⟨by omega, h2⟩

end LlFinal


namespace LlFinal
variable {n : Nat} {Adj : Nat → Nat → Prop} {par : Nat → Option Nat} {ord low fin sep : Nat → Nat}

/-- The graph without the edge `{p, v}`. -/
def EB (Adj : Nat → Nat → Prop) (p v : Nat) (a b : Nat) : Prop :=
  Adj a b ∧ ¬ ((a = p ∧ b = v) ∨ (a = v ∧ b = p))

theorem EB_symm (L : LlFinal n Adj par ord low fin sep) (p v : Nat) : ∀ a b, EB Adj p v a b → EB Adj p v b a := by
  intro a b ⟨h1, h2⟩
  refine ⟨L.adj_sym a b h1, ?_⟩
  intro h
  apply h2
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

/-- `low v = ord v` iff the tree edge `{par v, v}` is a bridge. -/
theorem bridge_iff (L : LlFinal n Adj par ord low fin sep) (v p : Nat) (hp : par v = some p) :
    low v = ord v ↔ ¬ Rtc (EB Adj p v) p v := by
  have hvn := (L.par_lt v p hp).1
  have hpv := (L.par_lt v p hp).2.2.2
  constructor
  · intro hl hpath
    have hpath' : Rtc (EB Adj p v) v p := Rtc.symm (L.EB_symm p v) hpath
    have closure : ∀ y z, Desc par v y → EB Adj p v y z → Desc par v z := by
      intro y z hy ⟨hadj, hne⟩
      have hn := L.adj_lt y z hadj
      have h1 := L.nbr_lt_fin y z hadj
      have h2 := L.fin_le v y hy
      by_cases hz : ord v ≤ ord z
      · exact (L.desc_iff v z hvn hn.2).mpr ⟨hz, by omega⟩
      · exfalso
        by_cases hpy : par y = some z
        · rcases desc_last hy with rfl | ⟨q, hq, hq2⟩
          · rw [hp] at hpy
            have := Option.some.inj hpy
            subst this
            exact hne (Or.inr ⟨rfl, rfl⟩)
          · rw [hpy] at hq2
            have := Option.some.inj hq2
            subst this
            have := L.desc_ord_ll hq
            omega
        · have := L.low_min v y z hy hadj hpy
          omega
    have hall : ∀ b, Rtc (EB Adj p v) v b → Desc par v b := by
      intro b hb
      induction hb with
      | refl => exact Rtc.refl _
      | tail _ hbc ih => exact closure _ _ ih hbc
    have := L.desc_ord_ll (hall p hpath')
    omega
  · intro hnot
    apply Classical.byContradiction
    intro hne
    have hlt : low v < ord v := Nat.lt_of_le_of_ne (L.low_le v hvn) hne
    rcases L.low_mem v hvn with heq | ⟨x, w, hx, hxw, hnp, hw⟩
    · exact hne heq
    · apply hnot
      have hordx := L.desc_ord_ll hx
      have hwx : Desc par w x := L.anc_of_adj hxw (by omega)
      -- the path from `v` down to `x`
      have pvx : Rtc (EB Adj p v) v x := by
        apply chain_path hx
        intro u y huy hvu _
        have hu := L.desc_ord_ll hvu
        have hyo := L.ord_par y u huy
        refine ⟨(L.par_lt y u huy).2.2.1, ?_⟩
        intro h
        rcases h with ⟨rfl, _⟩ | ⟨_, rfl⟩
        · omega
        · omega
      have exw : EB Adj p v x w := by
        refine ⟨hxw, ?_⟩
        intro h
        rcases h with ⟨rfl, _⟩ | ⟨rfl, rfl⟩
        · omega
        · exact hnp hp
      have hwv : Desc par w v := by
        rcases desc_comparable hwx hx with h | h
        · exact h
        · have := L.desc_ord_ll h
          omega
      have hwp : Desc par w p := by
        rcases desc_last hwv with rfl | ⟨q, hq, hq2⟩
        · omega
        · rw [hp] at hq2
          have := Option.some.inj hq2
          subst this
          exact hq
      have pwp : Rtc (EB Adj p v) w p := by
        apply chain_path hwp
        intro u y huy _ hyp
        have hyo := L.ord_par y u huy
        have hyp' := L.desc_ord_ll hyp
        refine ⟨(L.par_lt y u huy).2.2.1, ?_⟩
        intro h
        rcases h with ⟨_, rfl⟩ | ⟨rfl, rfl⟩
        · omega
        · omega
      exact Rtc.trans (Rtc.symm (L.EB_symm p v) pwp)
        (Rtc.trans (Rtc.single (L.EB_symm p v _ _ exw)) (Rtc.symm (L.EB_symm p v) pvx))

end LlFinal


theorem two_mem_nodup {l : List Nat} (hl : l.Nodup) (h2 : 2 ≤ l.length) : ∃ a b, a ∈ l ∧ b ∈ l ∧ a ≠ b := by
  match l, hl, h2 with
  | a :: b :: t, hl, _ =>
    refine ⟨a, b, by simp, by simp, ?_⟩
    intro h
    rw [List.nodup_cons] at hl
    exact hl.1 (by simp [h])

theorem length_two_of_mem {l : List Nat} (_hl : l.Nodup) {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hne : a ≠ b) :
    2 ≤ l.length := by
  have hsub : [a, b] ⊆ l := by
    intro x hx
    simp at hx
    rcases hx with rfl | rfl <;> assumption
  have hnd : [a, b].Nodup := by simp [hne]
  have := List.Nodup.length_le_of_subset hnd hsub
  simpa using this

namespace LlFinal
variable {n : Nat} {Adj : Nat → Nat → Prop} {par : Nat → Option Nat} {ord low fin sep : Nat → Nat}

/-- Counted children of `p`. -/
def Cnt (par : Nat → Option Nat) (ord low : Nat → Nat) (p c : Nat) : Prop := par c = some p ∧ ord p ≤ low c

theorem mem_cntL (n : Nat) (par : Nat → Option Nat) (ord low : Nat → Nat) (p c : Nat) :
    c ∈ (List.range n).filter (fun c => decide (par c = some p ∧ ord p ≤ low c)) ↔ c < n ∧ Cnt par ord low p c := by
  rw [List.mem_filter, decide_eq_true_iff, List.mem_range]
  rfl

theorem nodup_cntL (n : Nat) (par : Nat → Option Nat) (ord low : Nat → Nat) (p : Nat) :
    ((List.range n).filter (fun c => decide (par c = some p ∧ ord p ≤ low c))).Nodup :=
  List.Nodup.sublist List.filter_sublist List.nodup_range

theorem sep_pos (L : LlFinal n Adj par ord low fin sep) {v : Nat} (hv : v < n) (h : 1 ≤ sep v) :
    ∃ c, Cnt par ord low v c := by
  rw [L.sep_eq v hv] at h
  obtain ⟨c, hc⟩ := List.exists_mem_of_length_pos h
  exact ⟨c, ((mem_cntL n par ord low v c).mp hc).2⟩

theorem sep_two (L : LlFinal n Adj par ord low fin sep) {v : Nat} (hv : v < n) (h : 2 ≤ sep v) :
    ∃ c1 c2, c1 ≠ c2 ∧ Cnt par ord low v c1 ∧ Cnt par ord low v c2 := by
  rw [L.sep_eq v hv] at h
  obtain ⟨a, b, ha, hb, hne⟩ := two_mem_nodup (nodup_cntL n par ord low v) h
  exact ⟨a, b, hne, ((mem_cntL n par ord low v a).mp ha).2, ((mem_cntL n par ord low v b).mp hb).2⟩

theorem sep_zero (L : LlFinal n Adj par ord low fin sep) {v : Nat} (hv : v < n) (h : sep v = 0) :
    ∀ c, par c = some v → low c < ord v := by
  intro c hc
  apply Classical.byContradiction
  intro hlt
  have hcn := (L.par_lt c v hc).1
  have hmem := (mem_cntL n par ord low v c).mpr ⟨hcn, hc, by omega⟩
  have hpos : 0 < sep v := by
    rw [L.sep_eq v hv]
    exact List.length_pos_of_mem hmem
  omega

theorem sep_ge_two (L : LlFinal n Adj par ord low fin sep) {v : Nat} (hv : v < n) {c1 c2 : Nat} (hne : c1 ≠ c2)
    (h1 : Cnt par ord low v c1) (h2 : Cnt par ord low v c2) : 2 ≤ sep v := by
  have hc1 := (L.par_lt c1 v h1.1).1
  have hc2 := (L.par_lt c2 v h2.1).1
  rw [L.sep_eq v hv]
  exact length_two_of_mem (nodup_cntL n par ord low v) ((mem_cntL n par ord low v c1).mpr ⟨hc1, h1⟩)
    ((mem_cntL n par ord low v c2).mpr ⟨hc2, h2⟩) hne

/-- An ancestor of a vertex other than the vertex itself is an ancestor of its parent. -/
theorem desc_up (hp : par v = some p) (h : Desc par w v) (hne : w ≠ v) : Desc par w p := by
  rcases desc_last h with rfl | ⟨q, hq, hq2⟩
  · exact absurd rfl hne
  · rw [hp] at hq2
    have := Option.some.inj hq2
    subst this
    exact hq

/-- The far end of a back edge from the subtree of a child `c` of `v` that reaches before `c` is an ancestor of `v`. -/
theorem wit_anc (L : LlFinal n Adj par ord low fin sep) {c v x w : Nat} (hc : par c = some v) (hx : Desc par c x)
    (hxw : Adj x w) (hlt : ord w < ord c) : Desc par w v := by
  have hcx := L.desc_ord_ll hx
  have hwx : Desc par w x := L.anc_of_adj hxw (by omega)
  have hwc : Desc par w c := by
    rcases desc_comparable hwx hx with h | h
    · exact h
    · have := L.desc_ord_ll h
      omega
  rcases desc_last hwc with rfl | ⟨q, hq, hq2⟩
  · omega
  · rw [hc] at hq2
    have := Option.some.inj hq2
    subst this
    exact hq

theorem child_of_desc {a : Nat} (h : Desc par v a) (hne : v ≠ a) : ∃ c, par c = some v ∧ Desc par c a := by
  rcases Rtc.cases_head h with h1 | ⟨b, hb, hrest⟩
  · exact absurd h1 hne
  · exact ⟨b, hb, hrest⟩

/-- Without `v`. -/
def EV (Adj : Nat → Nat → Prop) (v : Nat) (a b : Nat) : Prop := Adj a b ∧ a ≠ v ∧ b ≠ v

theorem EV_symm (L : LlFinal n Adj par ord low fin sep) (v : Nat) : ∀ a b, EV Adj v a b → EV Adj v b a := by
  intro a b ⟨h1, h2, h3⟩
  exact ⟨L.adj_sym a b h1, h3, h2⟩

/-- The subtree of a child `c` of `v` is closed in the graph without `v`, if no ancestor of `v` is reached below `low c`. -/
theorem sub_closed (L : LlFinal n Adj par ord low fin sep) {c v : Nat} (hc : par c = some v)
    (hout : ∀ z, Desc par z v → z ≠ v → ord z < low c) :
    ∀ y z, Desc par c y → EV Adj v y z → Desc par c z := by
  intro y z hy ⟨hadj, hyv, hzv⟩
  have hn := L.adj_lt y z hadj
  have hcn := (L.par_lt c v hc).1
  have h1 := L.nbr_lt_fin y z hadj
  have h2 := L.fin_le c y hy
  by_cases hz : ord c ≤ ord z
  · exact (L.desc_iff c z hcn hn.2).mpr ⟨hz, by omega⟩
  · exfalso
    have hzc : ord z < ord c := by omega
    have hzv' := L.wit_anc hc hy hadj hzc
    have hzo := L.desc_ord_ll hzv'
    have hzlt : ord z < ord v := by
      have : ord z ≠ ord v := fun h => hzv (L.ord_inj z v hn.2 (L.par_lt c v hc).2.1 h)
      omega
    have hnp : par y ≠ some z := by
      intro hpy
      rcases desc_last hy with rfl | ⟨q, hq, hq2⟩
      · rw [hc] at hpy
        exact hzv (Option.some.inj hpy).symm
      · rw [hpy] at hq2
        have := Option.some.inj hq2
        subst this
        have := L.desc_ord_ll hq
        omega
    have := L.low_min c y z hy hadj hnp
    have := hout z hzv' hzv
    omega

end LlFinal


theorem no_reach_of_closed {E : Nat → Nat → Prop} {S : Nat → Prop} (hcl : ∀ y z, S y → E y z → S z) {a b : Nat}
    (ha : S a) (hb : ¬ S b) : ¬ Rtc E a b := by
  intro h
  have key : ∀ b', Rtc E a b' → S b' := by
    intro b' h'
    induction h' with
    | refl => exact ha
    | tail _ hbc ih => exact hcl _ _ ih hbc
  exact hb (key b h)

/-- Articulation point, in terms of the counters of the algorithm. -/
def Art (par : Nat → Option Nat) (sep : Nat → Nat) (v : Nat) : Prop :=
  (par v = none ∧ 2 ≤ sep v) ∨ (par v ≠ none ∧ 1 ≤ sep v)

namespace LlFinal
variable {n : Nat} {Adj : Nat → Nat → Prop} {par : Nat → Option Nat} {ord low fin sep : Nat → Nat}

theorem desc_lt (L : LlFinal n Adj par ord low fin sep) {a x : Nat} (h : Desc par a x) (hx : x < n) : a < n := by
  induction h with
  | refl => exact hx
  | tail _ hbc ih => exact ih (L.par_lt _ _ hbc).2.1

theorem sub_path (L : LlFinal n Adj par ord low fin sep) {c v a : Nat} (hc : par c = some v) (h : Desc par c a) :
    Rtc (EV Adj v) c a := by
  have hcv := (L.par_lt c v hc).2.2.2
  apply chain_path h
  intro u y huy hcu _
  have h1 := L.desc_ord_ll hcu
  have h2 := L.ord_par y u huy
  refine ⟨(L.par_lt y u huy).2.2.1, ?_, ?_⟩
  · intro e; subst e; omega
  · intro e; subst e; omega

theorem up_path (L : LlFinal n Adj par ord low fin sep) {v p w : Nat} (hp : par v = some p) (h : Desc par w p) :
    Rtc (EV Adj v) w p := by
  have hpv := (L.par_lt v p hp).2.2.2
  apply chain_path h
  intro u y huy _ hyp
  have h1 := L.desc_ord_ll hyp
  have h2 := L.ord_par y u huy
  refine ⟨(L.par_lt y u huy).2.2.1, ?_, ?_⟩
  · intro e; subst e; omega
  · intro e; subst e; omega

theorem root_child_low (L : LlFinal n Adj par ord low fin sep) {v c : Nat} (hp : par v = none) (hc : par c = some v) :
    ord v ≤ low c := by
  have hcv := (L.par_lt c v hc).2.2.2
  have hcn := (L.par_lt c v hc).1
  rcases L.low_mem c hcn with heq | ⟨x, w, hx, hxw, _, hw⟩
  · omega
  · apply Classical.byContradiction
    intro hlt
    have hwv := L.wit_anc hc hx hxw (by omega)
    rcases desc_last hwv with rfl | ⟨q, _, hq2⟩
    · omega
    · rw [hp] at hq2
      cases hq2

theorem nbr_child (L : LlFinal n Adj par ord low fin sep) {v a : Nat} (hp : par v = none) (h : Adj v a) :
    ∃ c, par c = some v ∧ Desc par c a := by
  have hn := L.adj_lt v a h
  have hne : v ≠ a := fun e => L.adj_irrefl v (e ▸ h)
  have hord : ord v ≠ ord a := fun e => hne (L.ord_inj v a hn.1 hn.2 e)
  by_cases hlt : ord a < ord v
  · exfalso
    have hd := L.anc_of_adj h hlt
    rcases desc_last hd with e | ⟨q, _, hq2⟩
    · exact hne e.symm
    · rw [hp] at hq2
      cases hq2
  · have hd : Desc par v a := (L.desc_iff v a hn.1 hn.2).mpr ⟨by omega, L.nbr_lt_fin v a h⟩
    exact child_of_desc hd hne

theorem art_sound (L : LlFinal n Adj par ord low fin sep) {v : Nat} (hv : v < n) (h : Art par sep v) :
    ∃ a b, Adj v a ∧ Adj v b ∧ ¬ Rtc (EV Adj v) a b := by
  rcases h with ⟨hp, h2⟩ | ⟨hp, h1⟩
  · obtain ⟨c1, c2, hne, h1, h2'⟩ := L.sep_two hv h2
    refine ⟨c1, c2, (L.par_lt c1 v h1.1).2.2.1, (L.par_lt c2 v h2'.1).2.2.1, ?_⟩
    have hout : ∀ z, Desc par z v → z ≠ v → ord z < low c1 := by
      intro z hz hzv
      exfalso
      rcases desc_last hz with e | ⟨q, _, hq2⟩
      · exact hzv e
      · rw [hp] at hq2
        cases hq2
    apply no_reach_of_closed (S := fun y => Desc par c1 y) (L.sub_closed h1.1 hout) (Rtc.refl _)
    intro hd
    rcases desc_last hd with e | ⟨q, hq, hq2⟩
    · exact hne e
    · rw [h2'.1] at hq2
      have hqv : q = v := (Option.some.inj hq2).symm
      rw [hqv] at hq
      have := L.desc_ord_ll hq
      have := (L.par_lt c1 v h1.1).2.2.2
      omega
  · obtain ⟨p, hpp⟩ : ∃ p, par v = some p := by
      cases hh : par v with
      | none => exact absurd hh hp
      | some p => exact ⟨p, rfl⟩
    obtain ⟨c, hc⟩ := L.sep_pos hv h1
    have hcv := (L.par_lt c v hc.1).2.2.2
    have hpv := (L.par_lt v p hpp).2.2.2
    refine ⟨c, p, (L.par_lt c v hc.1).2.2.1, L.adj_sym p v (L.par_lt v p hpp).2.2.1, ?_⟩
    have hout : ∀ z, Desc par z v → z ≠ v → ord z < low c := by
      intro z hz hzv
      have h1 := L.desc_ord_ll hz
      have hne : ord z ≠ ord v := fun e => hzv (L.ord_inj z v (L.desc_lt hz hv) hv e)
      have := hc.2
      omega
    apply no_reach_of_closed (S := fun y => Desc par c y) (L.sub_closed hc.1 hout) (Rtc.refl _)
    intro hd
    have := L.desc_ord_ll hd
    omega

end LlFinal


namespace LlFinal
variable {n : Nat} {Adj : Nat → Nat → Prop} {par : Nat → Option Nat} {ord low fin sep : Nat → Nat}

theorem reach_p (L : LlFinal n Adj par ord low fin sep) {v p : Nat} (hp : par v = some p) (hsep : sep v = 0)
    {a : Nat} (ha : Adj v a) : Rtc (EV Adj v) a p := by
  have hvn := (L.par_lt v p hp).1
  have hpv := (L.par_lt v p hp).2.2.2
  have hn := L.adj_lt v a ha
  have hne : v ≠ a := fun e => L.adj_irrefl v (e ▸ ha)
  have hord : ord v ≠ ord a := fun e => hne (L.ord_inj v a hn.1 hn.2 e)
  by_cases hlt : ord a < ord v
  · have hd := L.anc_of_adj ha hlt
    have hav : a ≠ v := fun e => hne e.symm
    exact L.up_path hp (desc_up hp hd hav)
  · have hd : Desc par v a := (L.desc_iff v a hn.1 hn.2).mpr ⟨by omega, L.nbr_lt_fin v a ha⟩
    obtain ⟨c, hc, hca⟩ := child_of_desc hd hne
    have hlow := L.sep_zero hvn hsep c hc
    have hcv := (L.par_lt c v hc).2.2.2
    have hcn := (L.par_lt c v hc).1
    rcases L.low_mem c hcn with heq | ⟨x, w, hx, hxw, _, hw⟩
    · omega
    · have hwc : ord w < ord c := by omega
      have hwv := L.wit_anc hc hx hxw hwc
      have hwne : w ≠ v := by
        intro e
        subst e
        omega
      have hwp := desc_up hp hwv hwne
      have hcx := L.desc_ord_ll hx
      have exw : EV Adj v x w := by
        refine ⟨hxw, ?_, hwne⟩
        intro e
        subst e
        omega
      exact Rtc.trans (Rtc.symm (L.EV_symm v) (L.sub_path hc hca))
        (Rtc.trans (L.sub_path hc hx) (Rtc.trans (Rtc.single exw) (L.up_path hp hwp)))

theorem reach_root (L : LlFinal n Adj par ord low fin sep) {v : Nat} (hv : v < n) (hp : par v = none)
    (hsep : sep v ≤ 1) {a b : Nat} (ha : Adj v a) (hb : Adj v b) : Rtc (EV Adj v) a b := by
  obtain ⟨c1, hc1, hd1⟩ := L.nbr_child hp ha
  obtain ⟨c2, hc2, hd2⟩ := L.nbr_child hp hb
  by_cases heq : c1 = c2
  · subst heq
    exact Rtc.trans (Rtc.symm (L.EV_symm v) (L.sub_path hc1 hd1)) (L.sub_path hc1 hd2)
  · exfalso
    have := L.sep_ge_two hv heq ⟨hc1, L.root_child_low hp hc1⟩ ⟨hc2, L.root_child_low hp hc2⟩
    omega

theorem art_complete (L : LlFinal n Adj par ord low fin sep) {v : Nat} (hv : v < n)
    (h : ∃ a b, Adj v a ∧ Adj v b ∧ ¬ Rtc (EV Adj v) a b) : Art par sep v := by
  obtain ⟨a, b, ha, hb, hnot⟩ := h
  apply Classical.byContradiction
  intro hart
  apply hnot
  cases hpv : par v with
  | none =>
    have hsep : sep v ≤ 1 := by
      apply Classical.byContradiction
      intro h2
      exact hart (Or.inl ⟨hpv, by omega⟩)
    exact L.reach_root hv hpv hsep ha hb
  | some p =>
    have hsep : sep v = 0 := by
      apply Classical.byContradiction
      intro h2
      exact hart (Or.inr ⟨by rw [hpv]; simp, by omega⟩)
    exact Rtc.trans (L.reach_p hpv hsep ha) (Rtc.symm (L.EV_symm v) (L.reach_p hpv hsep hb))

theorem art_iff (L : LlFinal n Adj par ord low fin sep) {v : Nat} (hv : v < n) :
    Art par sep v ↔ ∃ a b, Adj v a ∧ Adj v b ∧ ¬ Rtc (EV Adj v) a b :=
  ⟨L.art_sound hv, L.art_complete hv⟩

end LlFinal

end Proofs.LowlinkGraph
