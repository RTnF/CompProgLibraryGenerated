import Proofs.UfFindCall

namespace Proofs.UfCompression
open Proofs.UfRootCall Proofs.UfFindCall

-- The complete observable array update of a path-compressing root operation.
structure Compressed (ps vec : List Int) (a r : Nat) : Prop where
  length : vec.length = ps.length
  reach : Reach ps a r
  root : ∃ w, ps[r]? = some w ∧ w < 0
  entries : ∀ v, (PathSet ps a r v → vec[v]? = some (r : Int)) ∧
    (¬ PathSet ps a r v → vec[v]? = ps[v]?)

theorem path_reaches_root {ps vec : List Int} {a r : Nat} (c : Compressed ps vec a r)
    {v : Nat} (path : PathSet ps a r v) : Reach ps v r := by
  rcases reach_det ps a v r path.1 c.reach with yes | no
  · exact yes
  · exact absurd (root_reach ps r c.root v no) path.2

theorem root_unique {ps : List Int} {b r z : Nat} (br : Reach ps b r) (bz : Reach ps b z)
    (rr : ∃ w, ps[r]? = some w ∧ w < 0) (rz : ∃ w, ps[z]? = some w ∧ w < 0) : r = z := by
  rcases reach_det ps b r z br bz with h | h
  · exact (root_reach ps r rr z h).symm
  · exact root_reach ps z rz r h

-- Root entries, hence component sizes stored there, are exactly preserved.
theorem negative_entry {ps vec : List Int} {a r v : Nat} (c : Compressed ps vec a r)
    (x : Int) (negative : x < 0) : vec[v]? = some x ↔ ps[v]? = some x := by
  constructor
  · intro found
    by_cases path : PathSet ps a r v
    · rw [(c.entries v).1 path] at found
      have := Option.some.inj found
      omega
    · rw [(c.entries v).2 path] at found
      exact found
  · intro found
    have outside : ¬ PathSet ps a r v := by
      intro path
      have := root_reach ps v ⟨x,found,negative⟩ r (path_reaches_root c path)
      exact path.2 this.symm
    rw [(c.entries v).2 outside]
    exact found

-- Each new parent edge is either an old edge or a shortcut along the old tree.
theorem reach_backward {ps vec : List Int} {a r b z : Nat} (c : Compressed ps vec a r)
    (reach : Reach vec b z) : Reach ps b z := by
  induction reach with
  | refl b => exact Reach.refl b
  | step b p z parent rest ih =>
    by_cases path : PathSet ps a r b
    · have same : p = r := by
        have hp : vec[b]? = some (p : Int) := parent
        rw [(c.entries b).1 path] at hp
        have := Option.some.inj hp
        omega
      subst p
      exact reach_trans ps b r z (path_reaches_root c path) ih
    · have hp : ps[b]? = some (p : Int) := by
        have hp : vec[b]? = some (p : Int) := parent
        rw [(c.entries b).2 path] at hp
        exact hp
      exact Reach.step b p z hp ih

-- Paths to roots survive compression even when intermediate nodes are bypassed.
theorem root_forward {ps vec : List Int} {a r b z : Nat} (c : Compressed ps vec a r)
    (reach : Reach ps b z) (root : ∃ w, ps[z]? = some w ∧ w < 0) : Reach vec b z := by
  induction reach with
  | refl b => exact Reach.refl b
  | step b p z parent rest ih =>
    by_cases path : PathSet ps a r b
    · have same : r = z := root_unique (path_reaches_root c path) (Reach.step b p z parent rest) c.root root
      subst z
      exact Reach.step b r r ((c.entries b).1 path) (Reach.refl r)
    · have hp : vec[b]? = some (p : Int) := by
        rw [(c.entries b).2 path]
        exact parent
      exact Reach.step b p z hp (ih root)

theorem same_root {ps vec : List Int} {a r b z : Nat} (c : Compressed ps vec a r)
    (root : ∃ w, ps[z]? = some w ∧ w < 0) : Reach vec b z ↔ Reach ps b z :=
  ⟨reach_backward c,fun reach => root_forward c reach root⟩

-- This is the relation needed to compose two root calls in same/unite/size:
-- every node keeps its root and that root's negative size, including other trees.
theorem component_preserved {ps vec : List Int} {a r b z : Nat} (c : Compressed ps vec a r)
    (x : Int) (negative : x < 0) :
    (Reach vec b z ∧ vec[z]? = some x) ↔ (Reach ps b z ∧ ps[z]? = some x) := by
  constructor
  · rintro ⟨reach,found⟩
    exact ⟨reach_backward c reach,(negative_entry c x negative).mp found⟩
  · rintro ⟨reach,found⟩
    exact ⟨root_forward c reach ⟨x,found,negative⟩,(negative_entry c x negative).mpr found⟩

-- Connect the preservation relation to the already-proved two-pass executable body.
-- The candidate's additional field/argument slots still need their own call proof.
theorem body_preserves_components (P : List Proofs.CppState.Cell) (ps : List Int)
    (rank : Nat → Nat) (forest : Forest ps rank) (length : ps.length < 2147483648)
    (a : Nat) (inside : a < ps.length) (fuel : Nat) (enough : rank a+2 ≤ fuel) :
    ∃ (res : Proofs.VecWrite.PRW) (r : Nat),
      Proofs.VecWrite.pexecW Proofs.DoublingNested.i32 fuel bodyF (Proofs.PrefixSumsCall.stI P a) ps = some res ∧
      res.ret = some (r : Int) ∧ Compressed ps res.vec a r ∧ Forest res.vec rank ∧
      (∀ b z x, x < 0 → ((Reach res.vec b z ∧ res.vec[z]? = some x) ↔ (Reach ps b z ∧ ps[z]? = some x))) ∧
      res.cost ≤ 90 * rank a+60 ∧ res.need ≤ P.length+60 ∧ res.wk ≤ rank a := by
  obtain ⟨res,r,run,ret,reach,rl,root,inv,cost,need,work,_⟩ :=
    body_exec_find P ps rank forest length a inside fuel enough
  obtain ⟨sameLength,entries⟩ := inv2_final ps res.vec a r root inv
  have compressed : Compressed ps res.vec a r := ⟨sameLength,reach,root,entries⟩
  have newForest : Forest res.vec rank := find_forest ps res.vec rank forest a r reach rl root sameLength entries
    (Proofs.VectorSumCall.i32_valid r (by omega) (by omega))
  exact ⟨res,r,run,ret,compressed,newForest,fun _ _ x negative => component_preserved compressed x negative,cost,need,work⟩

-- A direct pure description of the original recursive `ps[a] = root(ps[a])`.
def recursive : Nat → List Int → Nat → Option (List Int × Nat)
  | 0, _, _ => none
  | fuel+1, ps, a => do
      let p ← ps[a]?
      if p < 0 then some (ps,a) else do
        let (vec,r) ← recursive fuel ps p.toNat
        some (vec.set a (r : Int),r)

theorem reach_parent {ps : List Int} {a p v : Nat} (parent : Parent ps a p) :
    Reach ps a v ↔ v = a ∨ Reach ps p v := by
  constructor
  · intro reach
    cases reach with
    | refl => exact Or.inl rfl
    | step _ b _ other tail =>
      have same : b = p := by
        have one : ps[a]? = some (p : Int) := parent
        have two : ps[a]? = some (b : Int) := other
        rw [one] at two
        have := Option.some.inj two
        omega
      subst b
      exact Or.inr tail
  · rintro (same | tail)
    · subst v; exact Reach.refl a
    · exact Reach.step a p v parent tail

theorem extend {ps vec : List Int} {a p r : Nat} (parent : Parent ps a p)
    (c : Compressed ps vec p r) : Compressed ps (vec.set a (r : Int)) a r := by
  have different : a ≠ r := by
    intro same
    obtain ⟨w,found,negative⟩ := c.root
    have hp : ps[a]? = some (p : Int) := parent
    rw [same,found] at hp
    have := Option.some.inj hp
    omega
  have inside : a < vec.length := by
    have hp : ps[a]? = some (p : Int) := parent
    rw [c.length]
    exact (List.getElem?_eq_some_iff.mp hp).1
  refine ⟨by simpa using c.length,Reach.step a p r parent c.reach,c.root,?_⟩
  intro v
  by_cases same : v = a
  · subst v
    have path : PathSet ps a r a := ⟨Reach.refl a,different⟩
    exact ⟨fun _ => List.getElem?_set_self inside,fun outside => False.elim (outside path)⟩
  · rw [List.getElem?_set_ne (Ne.symm same)]
    have paths : PathSet ps a r v ↔ PathSet ps p r v := by
      simp only [PathSet,reach_parent parent,or_iff_right same]
    exact ⟨fun h => (c.entries v).1 (paths.mp h),fun h => (c.entries v).2 (fun hp => h (paths.mpr hp))⟩

theorem recursive_correct (ps : List Int) (rank : Nat → Nat) (forest : Forest ps rank) :
    ∀ fuel a, a < ps.length → rank a < fuel →
      ∃ vec r, recursive fuel ps a = some (vec,r) ∧ Compressed ps vec a r := by
  intro fuel
  induction fuel with
  | zero => intro a inside enough; omega
  | succ fuel ih =>
    intro a inside enough
    let p := ps[a]
    have found : ps[a]? = some p := List.getElem?_eq_some_iff.mpr ⟨inside,rfl⟩
    by_cases negative : p < 0
    · refine ⟨ps,a,?_,⟨rfl,Reach.refl a,⟨p,found,negative⟩,?_⟩⟩
      · simp [recursive,found,negative]
      · intro v
        have outside : ¬ PathSet ps a a v := by
          intro path
          exact path.2 (root_reach ps a ⟨p,found,negative⟩ v path.1)
        exact ⟨fun path => False.elim (outside path),fun _ => rfl⟩
    · have nonneg : 0 ≤ p := by omega
      have child : p.toNat < ps.length := by have := forest.inside a p found nonneg; omega
      have smaller : rank p.toNat < rank a := forest.decrease a p found nonneg
      obtain ⟨vec,r,run,compressed⟩ := ih p.toNat child (by omega)
      have parent : Parent ps a p.toNat := by simpa [Parent,Int.toNat_of_nonneg nonneg] using found
      exact ⟨vec.set a (r : Int),r,by simp [recursive,found,negative,run],extend parent compressed⟩

theorem unique {ps one two : List Int} {a r z : Nat}
    (first : Compressed ps one a r) (second : Compressed ps two a z) : r = z ∧ one = two := by
  have same : r = z := root_unique first.reach second.reach first.root second.root
  subst z
  refine ⟨rfl,List.ext_getElem? (fun v => ?_)⟩
  by_cases path : PathSet ps a r v
  · rw [(first.entries v).1 path,(second.entries v).1 path]
  · rw [(first.entries v).2 path,(second.entries v).2 path]

theorem recursive_equals_two_pass (P : List Proofs.CppState.Cell) (ps : List Int)
    (rank : Nat → Nat) (forest : Forest ps rank) (length : ps.length < 2147483648)
    (a : Nat) (inside : a < ps.length) (fuel : Nat) (enough : rank a+2 ≤ fuel) :
    ∃ (res : Proofs.VecWrite.PRW) (r : Nat),
      Proofs.VecWrite.pexecW Proofs.DoublingNested.i32 fuel bodyF (Proofs.PrefixSumsCall.stI P a) ps = some res ∧
      res.ret = some (r : Int) ∧ recursive (rank a+1) ps a = some (res.vec,r) := by
  obtain ⟨res,r,run,ret,compressed,_⟩ := body_preserves_components P ps rank forest length a inside fuel enough
  obtain ⟨vec,z,original,other⟩ := recursive_correct ps rank forest (rank a+1) a inside (by omega)
  obtain ⟨rootSame,arraySame⟩ := unique other compressed
  rw [rootSame,arraySame] at original
  exact ⟨res,r,run,ret,original⟩

end Proofs.UfCompression
