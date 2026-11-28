import Proofs.Cpp.Gen.DisjointSet
import Proofs.Cpp.DisjointSet.Contracts

open Proofs.Cpp Proofs.Cpp.Gen
open Proofs.Cpp.UnionFind

namespace Proofs.Cpp.DisjointSet

open Classical in
noncomputable def belongs (parents : Array Int) (root vertex : Nat) : Nat :=
  if RootOf parents vertex root then 1 else 0

noncomputable def componentSize (parents : Array Int) (root : Nat) : Nat :=
  weightSum (belongs parents root) parents.size

def ExactSizes (parents : Array Int) : Prop :=
  ∀ root, IsRoot parents root → rootWeight parents root = componentSize parents root

theorem weightSum_add (f g : Nat → Nat) (n : Nat) :
    weightSum (fun i => f i + g i) n = weightSum f n + weightSum g n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [weightSum, ih]; omega

theorem singleMember (state : cp.DisjointSet)
    (singletons : ∀ i, i < state._ps.size → IsRoot state._ps i)
    {root : Nat} (hroot : IsRoot state._ps root) :
    componentSize state._ps root = 1 := by
  classical
  have zeroSum (n : Nat) : weightSum (fun _ => 0) n = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => simp [weightSum, ih]
  have member (i : Nat) (within : i < state._ps.size) :
      RootOf state._ps i root ↔ i = root := by
    constructor
    · intro path
      exact rootOf_unique state._ps i i root ⟨Reach.refl _, singletons i within⟩ path
    · rintro rfl
      exact ⟨Reach.refl _, hroot⟩
  unfold componentSize
  rw [weightSum_equal (right := replaceWeight (fun _ => 0) root 1)
    (fun i hi => by simp [belongs, replaceWeight, member i hi])]
  have single := weightSum_replace (weight := fun _ => 0) hroot.1 1
  simpa [zeroSum] using single

theorem exactSizes_compress {state after : cp.DisjointSet} {sizes : Nat → Nat}
    (valid : Valid after sizes) (compressed : Comp state._ps after._ps)
    (exactSizes : ExactSizes state._ps) :
    ExactSizes after._ps := by
  classical
  intro root laterRoot
  have originalRoot := (compressed.root_iff root).mp laterRoot
  unfold rootWeight
  rw [compressed.root_val root originalRoot]
  change rootWeight state._ps root = componentSize after._ps root
  rw [exactSizes root originalRoot]
  unfold componentSize
  rw [compressed.size]
  apply weightSum_equal
  intro i within
  have iff : RootOf state._ps i root ↔ RootOf after._ps i root :=
    ⟨rootOf_preserved valid compressed within, rootOf_comp _ _ compressed i root⟩
  simp [belongs, iff]

theorem vertex_has_root (state : cp.DisjointSet) (sizes : Nat → Nat) (valid : Valid state sizes) (vertex : Nat)
    (inside : vertex < state._ps.size) : ∃ root, RootOf state._ps vertex root := by
  obtain ⟨root, _, _, _, _, represents, _, _, _, _⟩ :=
    root_contract state sizes valid (vertex : Int) (by omega) (by rw [valid.vertices]; omega) 0
  exact ⟨root.toNat, by simpa using represents⟩

theorem exactSizes_link (state : cp.DisjointSet) (sizes : Nat → Nat) (valid : Valid state sizes)
    (original : ExactSizes state._ps) (large small : Int)
    (largeNonnegative : 0 ≤ large) (smallNonnegative : 0 ≤ small)
    (largeRoot : IsRoot state._ps large.toNat) (smallRoot : IsRoot state._ps small.toNat)
    (distinct : large ≠ small) :
    ExactSizes (UnionFind.link state._ps large small) := by
  classical
  let joined := UnionFind.link state._ps large small
  have distinctIndices : large.toNat ≠ small.toNat := by omega
  have extent : joined.size = state._ps.size := by simp [joined, UnionFind.link]
  have data := link_get state._ps large small largeNonnegative smallNonnegative largeRoot.1 smallRoot.1 distinct
  intro r resultingRoot
  have notSmall : r ≠ small.toNat := by
    intro equal
    have sign := resultingRoot.2
    change (UnionFind.link state._ps large small)[r]! < 0 at sign
    rw [data, ite_eq_left equal] at sign
    omega
  have asOldRoot : IsRoot state._ps r := by
    by_cases atLarge : r = large.toNat
    · rwa [atLarge]
    have sign := resultingRoot.2
    change (UnionFind.link state._ps large small)[r]! < 0 at sign
    rw [data, ite_eq_right notSmall, ite_eq_right atLarge] at sign
    exact ⟨by rw [← extent]; exact resultingRoot.1, sign⟩
  have project (i : Nat) (inside : i < state._ps.size) :
      RootOf joined i r ↔
        (RootOf state._ps i r ∨ r = large.toNat ∧ RootOf state._ps i small.toNat) := by
    constructor
    · intro afterRoute
      obtain ⟨beforeRoot, beforeRoute⟩ := vertex_has_root state sizes valid i inside
      have afterFromBefore := link_root largeNonnegative smallNonnegative largeRoot smallRoot distinct beforeRoute
      have computed := rootOf_unique joined i _ r afterFromBefore afterRoute
      by_cases moved : beforeRoot = small.toNat
      · rw [ite_eq_left moved] at computed
        exact Or.inr ⟨computed.symm, moved ▸ beforeRoute⟩
      · rw [ite_eq_right moved] at computed
        exact Or.inl (computed ▸ beforeRoute)
    · rintro (same | ⟨atLarge, beforeSmall⟩)
      · simpa only [ite_eq_right notSmall] using
          link_root largeNonnegative smallNonnegative largeRoot smallRoot distinct same
      · simpa only [ite_eq_left rfl, atLarge, ite_true] using
          link_root largeNonnegative smallNonnegative largeRoot smallRoot distinct beforeSmall
  by_cases atLarge : r = large.toNat
  · subst r
    have disjoint (i : Nat) : ¬ (RootOf state._ps i large.toNat ∧ RootOf state._ps i small.toNat) := by
      intro both
      exact distinctIndices (rootOf_unique state._ps i _ _ both.1 both.2)
    have sum : componentSize joined large.toNat =
        componentSize state._ps large.toNat + componentSize state._ps small.toNat := by
      unfold componentSize
      rw [extent, ← weightSum_add]
      apply weightSum_equal
      intro i inside
      have membership := project i inside
      simp only [true_and] at membership
      by_cases left : RootOf state._ps i large.toNat
      · have right : ¬ RootOf state._ps i small.toNat := fun present => disjoint i ⟨left, present⟩
        simp [belongs, membership, left, right]
      · simp [belongs, membership, left]
    change rootWeight joined large.toNat = componentSize joined large.toNat
    rw [sum, ← original _ largeRoot, ← original _ smallRoot]
    unfold rootWeight
    change (-(UnionFind.link state._ps large small)[large.toNat]!).toNat = _
    rw [data, ite_eq_right distinctIndices, ite_eq_left rfl]
    have firstNegative := largeRoot.2
    have secondNegative := smallRoot.2
    omega
  · have sum : componentSize joined r = componentSize state._ps r := by
      unfold componentSize
      rw [extent]
      apply weightSum_equal
      intro i inside
      simp [belongs, project i inside, atLarge]
    change rootWeight joined r = componentSize joined r
    rw [sum, ← original r asOldRoot]
    unfold rootWeight
    change (-(UnionFind.link state._ps large small)[r]!).toNat = _
    rw [data, ite_eq_right notSmall, ite_eq_right atLarge]

theorem unionTrace_sizes {before after : cp.DisjointSet} {sizes : Nat → Nat}
    (original : ExactSizes before._ps) (steps : UnionTrace before sizes after) : ExactSizes after._ps := by
  cases steps with
  | same after valid compressed => exact exactSizes_compress valid compressed original
  | join after large small valid compressed hl hs rLarge rSmall diff =>
    exact exactSizes_link after sizes valid (exactSizes_compress valid compressed original) large small
      hl hs rLarge rSmall diff

theorem construct_cardinal (n : Int) (nonnegative : 0 ≤ n) (fits : n < 2 ^ 31) (start : Nat) :
    ∃ state, (cp.DisjointSet.init n).run start = some (state, start + 1 + n.toNat) ∧
      Valid state (fun _ => 1) ∧ ExactSizes state._ps ∧ state._n = n ∧ state._num_groups = n := by
  obtain ⟨state, ran, valid, vertices, groups, singleton⟩ := construct n nonnegative fits start
  refine ⟨state, ran, valid, ?_, vertices, groups⟩
  intro root rootAt
  have assigned : rootWeight state._ps root = 1 := (valid.weights.rootSize root rootAt).symm
  exact assigned.trans (singleMember state singleton rootAt).symm

theorem size_cardinal (state : cp.DisjointSet) (sizes : Nat → Nat) (valid : Valid state sizes)
    (exactSizes : ExactSizes state._ps) (a : Int) (nonnegative : 0 ≤ a) (inside : a < state._n) (start : Nat) :
    ∃ (r : Int) (after : cp.DisjointSet) (stop : Nat), (cp.DisjointSet.size_ state a).run start =
        some (((componentSize state._ps r.toNat : Int), after), stop) ∧
      RootOf state._ps a.toNat r.toNat ∧ Valid after sizes ∧ ExactSizes after._ps ∧
      stop ≤ start + 2 + state._ps.size.log2 := by
  obtain ⟨r, after, stop, ran, located, validAfter, compressed, _, work⟩ :=
    size_contract state sizes valid a nonnegative inside start
  have count := exactSizes r.toNat located.2
  have sign := located.2.2
  unfold rootWeight at count
  have val : -state._ps[r.toNat]! = (componentSize state._ps r.toNat : Int) := by omega
  rw [val] at ran
  exact ⟨r, after, stop, ran, located, validAfter, exactSizes_compress validAfter compressed exactSizes, work⟩

theorem root_cardinal (state : cp.DisjointSet) (sizes : Nat → Nat) (valid : Valid state sizes)
    (exactSizes : ExactSizes state._ps) (a : Int) (nonnegative : 0 ≤ a) (inside : a < state._n) (start : Nat) :
    ∃ (r : Int) (after : cp.DisjointSet) (stop : Nat), (cp.DisjointSet.root state a).run start =
        some ((r, after), stop) ∧
      0 ≤ r ∧ RootOf state._ps a.toNat r.toNat ∧ Valid after sizes ∧ ExactSizes after._ps ∧
      Comp state._ps after._ps ∧
      (∀ i, Reach state._ps a.toNat i → i ≠ r.toNat → after._ps[i]! = r) ∧
      stop ≤ start + 1 + state._ps.size.log2 := by
  obtain ⟨r, after, stop, ran, nonnegativeRoot, located, validAfter, compressed, _, work⟩ :=
    root_contract state sizes valid a nonnegative inside start
  have allCompressed := (root_rec_compresses fuel state valid.vertices a start r after stop ran).2
  exact ⟨r, after, stop, ran, nonnegativeRoot, located, validAfter,
    exactSizes_compress validAfter compressed exactSizes, compressed, allCompressed, work⟩

theorem same_cardinal (state : cp.DisjointSet) (sizes : Nat → Nat) (valid : Valid state sizes)
    (exactSizes : ExactSizes state._ps) (a b : Int)
    (aValid : 0 ≤ a ∧ a < state._n) (bValid : 0 ≤ b ∧ b < state._n) (start : Nat) :
    ∃ (x y : Int) (after : cp.DisjointSet) (stop : Nat), (cp.DisjointSet.same state a b).run start =
        some ((decide (x = y), after), stop) ∧
      RootOf state._ps a.toNat x.toNat ∧ RootOf state._ps b.toNat y.toNat ∧
      0 ≤ x ∧ 0 ≤ y ∧ Valid after sizes ∧ ExactSizes after._ps ∧ Comp state._ps after._ps ∧
      stop ≤ start + 3 + 2 * state._ps.size.log2 := by
  obtain ⟨x, y, after, stop, ran, rootA, rootB, hx, hy, validAfter, compressed, _, work⟩ :=
    same_contract state sizes valid a b aValid bValid start
  exact ⟨x, y, after, stop, ran, rootA, rootB, hx, hy, validAfter,
    exactSizes_compress validAfter compressed exactSizes, compressed, work⟩

theorem get_num (state : cp.DisjointSet) (sizes : Nat → Nat) (valid : Valid state sizes) (start : Nat) :
    (cp.DisjointSet.getNum state).run start = some (((rootCount state._ps : Int), state), start + 1) :=
  getNum_contract state sizes valid start

theorem unite_cardinal (state : cp.DisjointSet) (sizes : Nat → Nat) (valid : Valid state sizes)
    (exactSizes : ExactSizes state._ps) (a b : Int)
    (aValid : 0 ≤ a ∧ a < state._n) (bValid : 0 ≤ b ∧ b < state._n) (start : Nat) :
    ∃ (x y : Int) (after : cp.DisjointSet) (afterSizes : Nat → Nat) (stop : Nat),
      (cp.DisjointSet.unite state a b).run start = some ((unionRoot state._ps x y, after), stop) ∧
      RootOf state._ps a.toNat x.toNat ∧ RootOf state._ps b.toNat y.toNat ∧
      Valid after afterSizes ∧ ExactSizes after._ps ∧ after._n = state._n ∧
      after._num_groups = state._num_groups - (if x = y then 0 else 1) ∧
      (∀ v z, v < state._ps.size → RootOf state._ps v z →
        RootOf after._ps v (if x = y then z
          else if z = (if unionRoot state._ps x y = x then y else x).toNat
            then (unionRoot state._ps x y).toNat else z)) ∧
      stop ≤ start + 3 + 2 * state._ps.size.log2 := by
  obtain ⟨x, y, after, sizesAfter, stop, ran, rootA, rootB, validAfter, vertices, groups, allRoots, trace, work⟩ :=
    unite_contract state sizes valid a b aValid bValid start
  exact ⟨x, y, after, sizesAfter, stop, ran, rootA, rootB, validAfter, unionTrace_sizes exactSizes trace,
    vertices, groups, allRoots, work⟩

end Proofs.Cpp.DisjointSet
