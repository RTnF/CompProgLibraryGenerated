import Proofs.Cpp.Gen.IntervalUnion
import Proofs.Cpp.Lib.Basic

/-! # `interval_union_inclusive` (library/interval/interval_union.hpp)

The union of closed intervals `[l, r]`: the result covers exactly the points of the input (`cov`), its intervals are
valid and separated in increasing order (`Sep`), and `v` is sorted in place; `O(n log n)` steps (the sort and one
pass). -/

open Std.Do Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.IntervalUnion

variable {T : Type} [LinearOrder T] [Inhabited T]

/-- The points covered by a list of closed intervals. -/
def cov (L : List (T × T)) (x : T) : Prop := ∃ p ∈ L, p.1 ≤ x ∧ x ≤ p.2

/-- Adjacent intervals are separated: each ends before the next starts. -/
def Sep : List (T × T) → Prop
  | p :: q :: rest => p.2 < q.1 ∧ Sep (q :: rest)
  | _ => True

/-- Every interval is valid. -/
def Valid (L : List (T × T)) : Prop := ∀ p ∈ L, p.1 ≤ p.2

theorem sep_snoc (L : List (T × T)) (p q : T × T) : Sep ((L ++ [p]) ++ [q]) ↔ Sep (L ++ [p]) ∧ p.2 < q.1 := by
  induction L with
  | nil => simp [Sep]
  | cons a L ih =>
    cases L with
    | nil => simp [Sep]
    | cons b L => simp only [List.cons_append, Sep] at ih ⊢; rw [ih]; tauto

theorem sep_snoc1 (q : T × T) : Sep ([] ++ [q]) := by simp [Sep]

theorem sep_replace_last (L : List (T × T)) (p p' : T × T) (h1 : p'.1 = p.1) (h : Sep (L ++ [p])) :
    Sep (L ++ [p']) := by
  induction L with
  | nil => simp [Sep]
  | cons a L ih =>
    cases L with
    | nil => simp [Sep] at h ⊢; rw [h1]; exact h
    | cons b L => simp only [List.cons_append, Sep] at h ih ⊢; exact ⟨h.1, ih h.2⟩

/-- `!(b < a)` for the lexicographic order on pairs is the lexicographic `≤`. -/
theorem not_lexLt (a b : T × T) : ¬ Prod.lexLt b a ↔ (a.1 < b.1 ∨ (a.1 = b.1 ∧ a.2 ≤ b.2)) := by
  simp only [Prod.lexLt, not_or, not_and, not_lt]
  constructor
  · rintro ⟨h1, h2⟩
    rcases lt_or_eq_of_le h1 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, h2 h.symm⟩
  · rintro (h | ⟨h, h'⟩)
    · exact ⟨le_of_lt h, fun e => absurd e (ne_of_gt h)⟩
    · exact ⟨le_of_eq h, fun _ => h'⟩

theorem sorted_firsts (v : Array (T × T)) :
    List.Pairwise (fun a b => a.1 ≤ b.1) (sortLex v).toList := by
  have hp := List.pairwise_mergeSort (le := fun a b => !decide (Prod.lexLt b a)) ?_ ?_ v.toList
  · simp only [sortLex, List.toList_toArray]
    refine hp.imp fun {a b} h => ?_
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at h
    rcases (not_lexLt a b).mp h with h | ⟨h, _⟩
    · exact le_of_lt h
    · exact le_of_eq h
  · intro a b c hab hbc
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at *
    rw [not_lexLt] at *
    rcases hab with h | ⟨h, h'⟩ <;> rcases hbc with g | ⟨g, g'⟩
    · exact Or.inl (lt_trans h g)
    · exact Or.inl (g ▸ h)
    · exact Or.inl (h ▸ g)
    · exact Or.inr ⟨h.trans g, le_trans h' g'⟩
  · intro a b
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, not_lexLt]
    rcases lt_trichotomy a.1 b.1 with h | h | h
    · exact Or.inl (Or.inl h)
    · rcases le_total a.2 b.2 with g | g
      · exact Or.inl (Or.inr ⟨h, g⟩)
      · exact Or.inr (Or.inr ⟨h.symm, g⟩)
    · exact Or.inr (Or.inl h)

theorem mem_sortLex (v : Array (T × T)) (p : T × T) : p ∈ (sortLex v).toList ↔ p ∈ v.toList := by
  simp only [sortLex, List.toList_toArray]
  exact (List.mergeSort_perm _ _).mem_iff

theorem cov_append (L M : List (T × T)) (x : T) : cov (L ++ M) x ↔ cov L x ∨ cov M x := by
  simp only [cov, List.mem_append]; constructor
  · rintro ⟨p, hp | hp, h⟩ <;> [exact Or.inl ⟨p, hp, h⟩; exact Or.inr ⟨p, hp, h⟩]
  · rintro (⟨p, hp, h⟩ | ⟨p, hp, h⟩) <;> [exact ⟨p, Or.inl hp, h⟩; exact ⟨p, Or.inr hp, h⟩]

theorem cov_single (p : T × T) (x : T) : cov [p] x ↔ p.1 ≤ x ∧ x ≤ p.2 := by simp [cov]

theorem cursor_facts (v : Array (T × T)) (hv : Valid v.toList) {pref suff : List (T × T)} {cur : T × T}
    (h : (sortLex v).toList = pref ++ cur :: suff) : cur.1 ≤ cur.2 ∧ ∀ y ∈ suff, cur.1 ≤ y.1 := by
  have hm : cur ∈ (sortLex v).toList := by rw [h]; simp
  refine ⟨hv cur ((mem_sortLex v cur).mp hm), fun y hy => ?_⟩
  have hs := sorted_firsts v
  rw [h, List.pairwise_append] at hs
  exact (List.pairwise_cons.mp hs.2.1).1 y hy

theorem interval_union_spec (v : Array (T × T)) (hv : Valid v.toList) (t0 : Nat) :
    ⦃fun c => ⌜c = t0⌝⦄ cp.interval_union_inclusive v
    ⦃⇓ r c => ⌜(∀ x, cov r.1.toList x ↔ cov v.toList x) ∧ Valid r.1.toList ∧ Sep r.1.toList ∧
               r.2 = sortLex v ∧ c ≤ t0 + 1 + sortCost v.size + 2 * v.size⌝⦄ := by
  mvcgen [cp.interval_union_inclusive]
  case inv1 =>
    exact ⇓⟨xs, ret⟩ c => ⌜(∀ x, cov ret.toList x ↔ cov xs.prefix x) ∧ Valid ret.toList ∧ Sep ret.toList ∧
      (xs.prefix = [] ↔ ret.toList = []) ∧ (∀ q ∈ ret.toList, ∀ y ∈ xs.suffix, q.1 ≤ y.1) ∧
      c ≤ t0 + 1 + sortCost v.size + 2 * xs.prefix.length⌝
  all_goals simp +zetaDelta at *
  · -- a new interval
    rename_i pref cur suff hcur b c l r ret hinv hcond
    obtain ⟨hcov, hval, hsep, hempty, hleft, hc⟩ := hinv
    obtain ⟨hcv, hcs⟩ := cursor_facts v hv hcur
    refine ⟨fun x => ?_, ?_, ?_, ?_, by omega⟩
    · rw [cov_append, cov_append, hcov]
    · intro p hp; simp at hp; rcases hp with hp | hp; exact hval p (by simpa using hp); subst hp; exact hcv
    · rcases List.eq_nil_or_concat b.toList with hb | ⟨L, p, hb⟩
      · rw [hb]; simp [Sep]
      · rw [List.concat_eq_append] at hb
        rw [hb]
        have hback := back_of_toList b L p hb
        rcases hcond with h | h
        · simp [h] at hb
        · rw [hback] at h; rw [hb] at hsep; exact (sep_snoc L p cur).mpr ⟨hsep, h⟩
    · intro a b' hab y1 y2 hy
      rcases hab with hab | hab
      · exact (hleft a b' hab).2 y1 y2 hy
      · subst hab; exact hcs (y1, y2) hy
  · -- the last interval is extended to the end of the current one
    rename_i pref cur suff hcur b c l r ret hinv hne hlt
    obtain ⟨hcov, hval, hsep, hempty, hleft, hc⟩ := hinv
    obtain ⟨hcv, hcs⟩ := cursor_facts v hv hcur
    obtain ⟨L, p, hb⟩ : ∃ L p, b.toList = L ++ [p] := by
      rcases List.eq_nil_or_concat b.toList with h | ⟨L, p, h⟩
      · exact absurd (by simpa using h) hne.1
      · exact ⟨L, p, by simpa using h⟩
    have hback := back_of_toList b L p hb
    rw [get_last_of_toList b L p hb]
    have hset := set_last_toList b L p (p.1, cur.2) hb
    rw [hback] at hne hlt
    have hpb : p ∈ b.toList := by rw [hb]; simp
    have hp1 : p.1 ≤ cur.1 := (hleft p.1 p.2 (by simpa using hpb)).1
    have hpv : p.1 ≤ p.2 := hval p hpb
    refine ⟨fun x => ?_, ?_, ?_, ?_, ?_, by omega⟩
    · rw [hset, cov_append, cov_append, ← hcov, hb, cov_append]
      simp only [cov_single]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl (Or.inl h)
        · rcases le_or_gt x p.2 with h3 | h3
          · exact Or.inl (Or.inr ⟨h1, h3⟩)
          · exact Or.inr ⟨le_trans hne.2 (le_of_lt h3), h2⟩
      · rintro ((h | ⟨h1, h2⟩) | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨h1, le_trans h2 (le_of_lt hlt)⟩
        · exact Or.inr ⟨le_trans hp1 h1, h2⟩
    · rw [hset]; intro q hq
      simp only [List.mem_append, List.mem_singleton] at hq
      rcases hq with hq | hq
      · exact hval q (by rw [hb]; simp [hq])
      · subst hq; exact le_trans hpv (le_of_lt hlt)
    · rw [hset]; rw [hb] at hsep; exact sep_replace_last L p _ rfl hsep
    · intro h; have := congrArg Array.toList h; rw [hset] at this; simp at this
    · intro a b' hab y1 y2 hy
      have hab' : (a, b') ∈ L ++ [(p.1, cur.2)] := by rw [← hset]; simpa using hab
      simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hab'
      rcases hab' with hab' | ⟨ha, _⟩
      · exact (hleft a b' (by rw [← Array.mem_toList_iff, hb]; simp [hab'])).2 y1 y2 hy
      · subst ha; exact (hleft p.1 p.2 (by simpa using hpb)).2 y1 y2 hy
  · -- the current interval lies inside the last one
    rename_i pref cur suff hcur b c l r hinv hne hle
    obtain ⟨hcov, hval, hsep, hempty, hleft, hc⟩ := hinv
    obtain ⟨L, p, hb⟩ : ∃ L p, b.toList = L ++ [p] := by
      rcases List.eq_nil_or_concat b.toList with h | ⟨L, p, h⟩
      · exact absurd (by simpa using h) hne.1
      · exact ⟨L, p, by simpa using h⟩
    have hback := back_of_toList b L p hb
    rw [hback] at hne hle
    have hpb : p ∈ b.toList := by rw [hb]; simp
    have hp1 : p.1 ≤ cur.1 := (hleft p.1 p.2 (by simpa using hpb)).1
    refine ⟨fun x => ?_, hval, hsep, hne.1, fun a b' hab y1 y2 hy => (hleft a b' hab).2 y1 y2 hy, by omega⟩
    rw [cov_append, ← hcov]
    simp only [cov_single]
    constructor
    · exact Or.inl
    · rintro (h | ⟨h1, h2⟩)
      · exact h
      · exact ⟨p, hpb, le_trans hp1 h1, le_trans h2 hle⟩
  · exact ⟨by simp [Valid], by simp [Sep], by omega⟩
  · obtain ⟨hcov, hval, hsep, _, hc⟩ := ‹(∀ x, _) ∧ _ ∧ _ ∧ _ ∧ _›
    have hsz : (sortLex v).size = v.size := by
      simp only [sortLex, List.size_toArray]; exact (List.mergeSort_perm _ _).length_eq.trans (by simp)
    refine ⟨fun x => ?_, hval, hsep, by rw [hsz] at hc; exact hc⟩
    rw [hcov]
    simp only [cov, mem_sortLex]

end Proofs.Cpp.IntervalUnion
