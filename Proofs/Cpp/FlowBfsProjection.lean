import Proofs.Cpp.FlowBfsProgram

open Proofs.Cpp Proofs.Cpp.Gen Proofs.FlowBfs

namespace Proofs.Cpp.FlowBfs

variable {Cost E : Type} [Inhabited E] [Zero Cost] [LT Cost] [DecidableLT Cost]
  [Field "cap" E Cost] [Field "to" E Int]

def edgesAt (g : cp.FlowGraph Cost E) (v : Nat) : List E := (get g.adj (v : Int)).toList

structure Valid (g : cp.FlowGraph Cost E) : Prop where
  size : g.n_ = (g.adj.size : Int)
  target_range : ∀ v < g.adj.size, ∀ e ∈ edgesAt g v, 0 ≤ target e ∧ target e < g.n_

def residual (g : cp.FlowGraph Cost E) (u v : Nat) : Prop :=
  u < g.adj.size ∧ ∃ e ∈ edgesAt g u, positive (Cost := Cost) e ∧ target e = (v : Int)

def levelsView (lv : Array Int) : Level :=
  fun v => if v < lv.size ∧ 0 ≤ lv[v]! then some lv[v]!.toNat else none

theorem view_some (lv : Array Int) {v d : Nat} (hv : v < lv.size) :
    levelsView lv v = some d ↔ lv[v]! = (d : Int) := by
  unfold levelsView
  by_cases nn : 0 ≤ lv[v]!
  · rw [ite_eq_left ⟨hv, nn⟩, Option.some.injEq]
    omega
  · rw [ite_eq_right (fun h => nn h.2)]
    constructor
    · intro h
      cases h
    · intro h
      exfalso
      omega

theorem view_none (lv : Array Int) {v : Nat} (hv : v < lv.size) (hmark : -1 ≤ lv[v]!) :
    levelsView lv v = none ↔ lv[v]! = -1 := by
  unfold levelsView
  by_cases nn : 0 ≤ lv[v]!
  · rw [ite_eq_left ⟨hv, nn⟩]
    constructor
    · intro h
      cases h
    · intro h
      exfalso
      omega
  · rw [ite_eq_right (fun h => nn h.2)]
    exact ⟨fun _ => by omega, fun _ => rfl⟩

theorem marked_value (lv : Array Int) (v d : Nat) (hv : v < lv.size) (w : Nat) :
    (set lv (v : Int) (d : Int))[w]! = if w = v then (d : Int) else lv[w]! := by
  simpa only [Int.toNat_natCast] using getElemBang_set lv (v : Int) (d : Int) w (by simpa using hv)

theorem view_mark (lv : Array Int) (v d : Nat) (hv : v < lv.size) :
    levelsView (set lv (v : Int) (d : Int)) = mark (levelsView lv) v d := by
  funext w
  unfold levelsView mark
  rw [size_set, marked_value lv v d hv w]
  by_cases hw : w = v
  · subst w
    simp [hv]
  · simp [hw]

def KeepsLevels (before after : Level) : Prop :=
  ∀ v k, before v = some k → after v = some k

theorem keep_mark {lv : Level} {v d : Nat} (fresh : lv v = none) : KeepsLevels lv (mark lv v d) := by
  intro w k h
  by_cases eq : w = v
  · subst w
    rw [fresh] at h
    contradiction
  · simpa [mark, eq] using h

theorem KeepsLevels.trans {a b c : Level} (h₁ : KeepsLevels a b) (h₂ : KeepsLevels b c) : KeepsLevels a c :=
  fun v k h => h₂ v k (h₁ v k h)

theorem KeepsLevels.keeps_bound {a b : Level} (h : KeepsLevels a b) {v d : Nat}
    (hv : lowerAtMost a v d) : lowerAtMost b v d := by
  obtain ⟨j, hj, bound⟩ := hv
  exact ⟨j, h v j hj, bound⟩

structure ScanState (g : cp.FlowGraph Cost E) (source active : Nat) (done : List Nat)
    (b : BfsState) (d : Nat) : Prop where
  size : b.1.size = g.adj.size
  stored : ∀ v < b.1.size, -1 ≤ b.1[v]!
  queueNonnegative : ∀ v ∈ b.2, 0 ≤ v
  scan : Scan (residual g) source active done (b.2.map Int.toNat) (levelsView b.1) d

/-- Each arc either does not alter BFS state or marks its fresh destination and enqueues it. -/
theorem scan_edge (g : cp.FlowGraph Cost E) (valid : Valid g) (source active d : Nat) (done : List Nat)
    (b : BfsState) (st : ScanState g source active done b d) (edge : E)
    (inRow : edge ∈ edgesAt g active) (t : Nat) :
    ∃ (out : BfsState) (t' : Nat),
      (edgeStep (Cost := Cost) (active : Int) edge b).run t = some (.yield out, t') ∧
      ScanState g source active done out d ∧ KeepsLevels (levelsView b.1) (levelsView out.1) ∧
      (positive (Cost := Cost) edge → lowerAtMost (levelsView out.1) (target edge).toNat (d + 1)) ∧ t' ≤ t + 2 := by
  have activeIn : active < g.adj.size := by
    have hf := st.scan.here
    by_contra hh
    have hd : ¬ active < b.1.size := by simpa only [st.size] using hh
    simp [levelsView, hd] at hf
  obtain ⟨hlo, hhi⟩ := valid.target_range active activeIn edge inRow
  let v := (target edge).toNat
  have hvCast : (v : Int) = target edge := by omega
  have hGraph : v < g.adj.size := by rw [valid.size, ← hvCast] at hhi; omega
  have hv : v < b.1.size := by rwa [st.size]
  have ha : active < b.1.size := by rwa [st.size]
  have hActive : get b.1 (active : Int) = (d : Int) := (view_some b.1 ha).mp st.scan.here
  have hValue : get b.1 (target edge) = b.1[v]! := rfl
  by_cases h : positive (Cost := Cost) edge ∧ get b.1 (target edge) = -1
  · obtain ⟨hp, hn⟩ := h
    have hArc : residual g active v := ⟨activeIn, edge, inRow, hp, hvCast.symm⟩
    have hFresh : levelsView b.1 v = none := (view_none b.1 hv (st.stored v hv)).mpr (hValue.symm.trans hn)
    let out : BfsState := (set b.1 (v : Int) ((d + 1 : Nat) : Int), b.2 ++ [(v : Int)])
    have he := edge_discovered (active : Int) edge b t hp hn
    rw [hActive, ← hvCast] at he
    have hev : levelsView out.1 = mark (levelsView b.1) v (d + 1) := view_mark b.1 v (d + 1) hv
    have hq : out.2.map Int.toNat = b.2.map Int.toNat ++ [v] := by simp [out]
    have hs' : out.1.size = b.1.size := size_set _ _ _
    refine ⟨out, t + 2, by simpa only [out, Int.natCast_succ] using he,
      ⟨hs'.trans st.size, ?_, ?_, ?_⟩, ?_, ?_, Nat.le_refl _⟩
    · intro w hw
      rw [hs'] at hw
      change -1 ≤ (set b.1 (v : Int) ((d + 1 : Nat) : Int))[w]!
      rw [marked_value _ _ _ hv]
      split
      · omega
      · exact st.stored w hw
    · intro w hw
      rcases List.mem_append.mp hw with hm | hm
      · exact st.queueNonnegative w hm
      · obtain rfl := List.mem_singleton.mp hm
        exact Int.natCast_nonneg _
    · rw [hev, hq]
      exact st.scan.discover hArc hFresh
    · rw [hev]
      exact keep_mark hFresh
    · intro _
      change lowerAtMost (levelsView out.1) v (d + 1)
      rw [hev]
      exact ⟨d + 1, by simp [mark], Nat.le_refl _⟩
  · refine ⟨b, t + 1, edge_ignored _ _ b t h, st, fun _ _ hx => hx, ?_, by omega⟩
    intro hp
    apply st.scan.level_known
    have hnot : b.1[v]! ≠ -1 := fun q => h ⟨hp, hValue.trans q⟩
    have hbound := st.stored v hv
    exact ⟨(b.1[v]!).toNat, (view_some b.1 hv).mpr (by omega)⟩

end Proofs.Cpp.FlowBfs
