import Proofs.Cpp.DisjointSet.RootCount

open Proofs.Cpp Proofs.Cpp.Gen
open Proofs.Cpp.UnionFind

namespace Proofs.Cpp.DisjointSet

structure Valid (state : cp.DisjointSet) (sizes : Nat → Nat) : Prop where
  weights : SizeCertificate state._ps sizes
  total : rootMass state._ps = state._ps.size
  vertices : state._n = state._ps.size
  groups : state._num_groups = rootCount state._ps
  fits : state._ps.size < 2 ^ 31

theorem construct (n : Int) (nonnegative : 0 ≤ n) (fits : n < 2 ^ 31) (start : Nat) :
    ∃ state, (cp.DisjointSet.init n).run start = some (state, start + 1 + n.toNat) ∧
      Valid state (fun _ => 1) ∧ state._n = n ∧ state._num_groups = n ∧
      (∀ i, i < state._ps.size → IsRoot state._ps i) := by
  obtain ⟨state, stop, ran, length, vertices, groups, weights, total, singleton, elapsed⟩ :=
    generated_init_mass n nonnegative fits start
  have rootNumber : rootCount state._ps = state._ps.size := by
    unfold rootCount
    rw [weightSum_equal (right := fun _ => 1)
      (fun i hi => by simp [isRootCount, (singleton i hi).2]), weightSum_ones]
  exact ⟨state, elapsed ▸ ran, ⟨weights, total, by omega, by omega, by omega⟩,
    vertices, groups, singleton⟩

theorem root_contract (state : cp.DisjointSet) (sizes : Nat → Nat) (valid : Valid state sizes)
    (a : Int) (nonnegative : 0 ≤ a) (inside : a < state._n) (start : Nat) :
    ∃ (r : Int) (after : cp.DisjointSet) (stop : Nat), (cp.DisjointSet.root state a).run start = some ((r, after), stop) ∧
      0 ≤ r ∧ RootOf state._ps a.toNat r.toNat ∧ Valid after sizes ∧
      Comp state._ps after._ps ∧ after._n = state._n ∧ stop ≤ start + 1 + state._ps.size.log2 := by
  obtain ⟨r, after, stop, ran, hr, represents, weights, compressed, length, vertices, groups, work⟩ :=
    generated_root_height state sizes valid.weights valid.vertices valid.fits a nonnegative inside start
  refine ⟨r, after, stop, ran, hr, represents, ⟨weights, ?_, ?_, ?_, ?_⟩, compressed, vertices, work⟩
  · rw [rootMass_compress compressed, valid.total, length]
  · rw [vertices, valid.vertices, length]
  · rw [groups, valid.groups, rootCount_compress compressed]
  · rw [length]
    exact valid.fits

theorem size_contract (state : cp.DisjointSet) (sizes : Nat → Nat) (valid : Valid state sizes)
    (a : Int) (nonnegative : 0 ≤ a) (inside : a < state._n) (start : Nat) :
    ∃ (r : Int) (after : cp.DisjointSet) (stop : Nat), (cp.DisjointSet.size_ state a).run start =
        some ((-state._ps[r.toNat]!, after), stop) ∧
      RootOf state._ps a.toNat r.toNat ∧ Valid after sizes ∧
      Comp state._ps after._ps ∧ after._n = state._n ∧ stop ≤ start + 2 + state._ps.size.log2 := by
  obtain ⟨r, after, stop, ran, hr, represents, validAfter, compressed, vertices, work⟩ :=
    root_contract state sizes valid a nonnegative inside (start + 1)
  have size := generated_size_after_root state after a r start stop ⟨nonnegative, inside⟩ ran
  rw [show get after._ps r = after._ps[r.toNat]! from rfl, compressed.root_val r.toNat represents.2] at size
  exact ⟨r, after, stop, size, represents, validAfter, compressed, vertices, by omega⟩

theorem same_contract (state : cp.DisjointSet) (sizes : Nat → Nat) (valid : Valid state sizes)
    (a b : Int) (aValid : 0 ≤ a ∧ a < state._n) (bValid : 0 ≤ b ∧ b < state._n) (start : Nat) :
    ∃ (x y : Int) (after : cp.DisjointSet) (stop : Nat), (cp.DisjointSet.same state a b).run start =
        some ((decide (x = y), after), stop) ∧
      RootOf state._ps a.toNat x.toNat ∧ RootOf state._ps b.toNat y.toNat ∧
      0 ≤ x ∧ 0 ≤ y ∧ Valid after sizes ∧ Comp state._ps after._ps ∧
      after._n = state._n ∧ stop ≤ start + 3 + 2 * state._ps.size.log2 := by
  obtain ⟨x, first, mid, ranA, hx, rootA, va, ca, na, wa⟩ :=
    root_contract state sizes valid a aValid.1 aValid.2 (start + 1)
  obtain ⟨y, after, stop, ranB, hy, rootB, vb, cb, nb, wb⟩ :=
    root_contract first sizes va b bValid.1 (by rw [na]; exact bValid.2) mid
  have ran := generated_same_after_roots state first after a b x y start mid stop aValid bValid ranA ranB
  rw [ca.size] at wb
  exact ⟨x, y, after, stop, ran, rootA, rootOf_comp _ _ ca _ _ rootB, hx, hy, vb,
    comp_trans _ _ _ ca cb, nb.trans na, by omega⟩

theorem getNum_contract (state : cp.DisjointSet) (sizes : Nat → Nat) (valid : Valid state sizes) (start : Nat) :
    (cp.DisjointSet.getNum state).run start = some (((rootCount state._ps : Int), state), start + 1) := by
  rw [← valid.groups]
  cases state
  rfl

def mergeInto (state : cp.DisjointSet) (large small : Int) : cp.DisjointSet :=
  ⟨UnionFind.link state._ps large small, state._num_groups - 1, state._n⟩

theorem Valid.link (state : cp.DisjointSet) (sizes : Nat → Nat) (valid : Valid state sizes)
    (large small : Int) (largeIndex : 0 ≤ large) (smallIndex : 0 ≤ small)
    (largeRoot : IsRoot state._ps large.toNat) (smallRoot : IsRoot state._ps small.toNat)
    (distinct : large ≠ small)
    (order : -(get state._ps small) ≤ -(get state._ps large)) :
    Valid (mergeInto state large small) (joinedSize sizes large.toNat small.toNat) := by
  have cap := rootMass_pair_bound valid.weights valid.total largeRoot smallRoot (by omega : large.toNat ≠ small.toNat)
  have sizesOrder : sizes small.toNat ≤ sizes large.toNat := by
    rw [valid.weights.rootSize small.toNat smallRoot, valid.weights.rootSize large.toNat largeRoot]
    exact Int.toNat_le_toNat order
  have extent := (link_forest state._ps (heightRank state._ps.size sizes) valid.weights.forest
    large small largeIndex smallIndex largeRoot smallRoot distinct).2
  have total := rootMass_link valid.weights large small largeIndex smallIndex largeRoot smallRoot distinct
  have groups := rootCount_link valid.weights large small largeIndex smallIndex largeRoot smallRoot distinct
  constructor
  · exact valid.weights.link large small largeIndex smallIndex largeRoot smallRoot distinct sizesOrder cap
  · change rootMass (UnionFind.link state._ps large small) = (UnionFind.link state._ps large small).size
    rw [total, extent, valid.total]
  · change state._n = (UnionFind.link state._ps large small).size
    rw [extent, valid.vertices]
  · change state._num_groups - 1 = (rootCount (UnionFind.link state._ps large small) : Int)
    have original := valid.groups
    omega
  · change (UnionFind.link state._ps large small).size < _
    rw [extent]
    exact valid.fits

theorem reach_append {parents : Array Int} {a b : Nat} (initial : Reach parents a b)
    {c : Nat} (suffix : Reach parents b c) : Reach parents a c := by
  induction initial with
  | refl _ => exact suffix
  | step i j k first _ ih => exact Reach.step _ _ _ first (ih suffix)

theorem link_root {parents : Array Int} {large small : Int}
    (largeIndex : 0 ≤ large) (smallIndex : 0 ≤ small)
    (largeRoot : IsRoot parents large.toNat) (smallRoot : IsRoot parents small.toNat)
    (different : large ≠ small) {a r : Nat} (original : RootOf parents a r) :
    RootOf (UnionFind.link parents large small) a (if r = small.toNat then large.toNat else r) := by
  let joined := UnionFind.link parents large small
  have distinct : large.toNat ≠ small.toNat := by omega
  have extent : joined.size = parents.size := by simp [joined, UnionFind.link, size_set]
  have data := link_get parents large small largeIndex smallIndex largeRoot.1 smallRoot.1 different
  have oldPaths {i j : Nat} (route : Reach parents i j) : Reach joined i j := by
    induction route with
    | refl i => exact Reach.refl i
    | step i j k step rest follow =>
      have awayLarge : i ≠ large.toNat := by
        intro equal
        have sign := step.2.1
        rw [equal] at sign
        have negative := largeRoot.2
        omega
      have awaySmall : i ≠ small.toNat := by
        intro equal
        have sign := step.2.1
        rw [equal] at sign
        have negative := smallRoot.2
        omega
      have unchanged : joined[i]! = parents[i]! := by
        change (UnionFind.link parents large small)[i]! = _
        simp [data i, awaySmall, awayLarge]
      exact Reach.step _ _ _
        ⟨by rw [extent]; exact step.1, by rw [unchanged]; exact step.2.1,
          by rw [unchanged]; exact step.2.2⟩ follow
  have joinedLarge : IsRoot joined large.toNat := by
    constructor
    · rw [extent]
      exact largeRoot.1
    · change (UnionFind.link parents large small)[large.toNat]! < 0
      have left := largeRoot.2
      have right := smallRoot.2
      rw [data, ite_eq_right distinct, ite_eq_left rfl]
      omega
  by_cases isSmall : r = small.toNat
  · rw [ite_eq_left isSmall]
    have connection : Parent joined small.toNat large.toNat := by
      have value : joined[small.toNat]! = large := by
        exact (data small.toNat).trans (ite_eq_left rfl)
      exact ⟨by rw [extent]; exact smallRoot.1, by rw [value]; exact largeIndex, by rw [value]⟩
    have route : Reach joined a small.toNat := by rw [← isSmall]; exact oldPaths original.1
    exact ⟨reach_append route (Reach.step _ _ _ connection (Reach.refl _)), joinedLarge⟩
  · rw [ite_eq_right isSmall]
    refine ⟨oldPaths original.1, ?_⟩
    by_cases isLarge : r = large.toNat
    · rwa [isLarge]
    · constructor
      · rw [extent]
        exact original.2.1
      · change (UnionFind.link parents large small)[r]! < 0
        rw [data, ite_eq_right isSmall, ite_eq_right isLarge]
        exact original.2.2

theorem rootOf_preserved {state after : cp.DisjointSet} {sizes : Nat → Nat}
    (valid : Valid after sizes) (compressed : Comp state._ps after._ps)
    {vertex root : Nat} (member : vertex < state._ps.size)
    (original : RootOf state._ps vertex root) : RootOf after._ps vertex root := by
  have inside : (vertex : Int) < after._n := by rw [valid.vertices, compressed.size]; omega
  obtain ⟨later, _, _, _, _, actual, _, _, _, _⟩ :=
    root_contract after sizes valid (vertex : Int) (by omega) inside 0
  simp only [Int.toNat_natCast] at actual
  have originalLater := rootOf_comp _ _ compressed vertex later.toNat actual
  simpa only [rootOf_unique state._ps vertex later.toNat root originalLater original] using actual

def unionRoot (parents : Array Int) (x y : Int) : Int :=
  if -(get parents x) < -(get parents y) then y else x

inductive UnionTrace (before : cp.DisjointSet) (sizes : Nat → Nat) : cp.DisjointSet → Prop
  | same (after : cp.DisjointSet) (valid : Valid after sizes) (compress : Comp before._ps after._ps) :
      UnionTrace before sizes after
  | join (compressed : cp.DisjointSet) (large small : Int) (valid : Valid compressed sizes)
      (compress : Comp before._ps compressed._ps) (largeIndex : 0 ≤ large) (smallIndex : 0 ≤ small)
      (largeRoot : IsRoot compressed._ps large.toNat) (smallRoot : IsRoot compressed._ps small.toNat)
      (distinct : large ≠ small) : UnionTrace before sizes (mergeInto compressed large small)

theorem unite_contract (state : cp.DisjointSet) (sizes : Nat → Nat) (valid : Valid state sizes)
    (a b : Int) (aValid : 0 ≤ a ∧ a < state._n) (bValid : 0 ≤ b ∧ b < state._n) (start : Nat) :
    ∃ (x y : Int) (after : cp.DisjointSet) (afterSizes : Nat → Nat) (stop : Nat),
      (cp.DisjointSet.unite state a b).run start = some ((unionRoot state._ps x y, after), stop) ∧
      RootOf state._ps a.toNat x.toNat ∧ RootOf state._ps b.toNat y.toNat ∧
      Valid after afterSizes ∧ after._n = state._n ∧
      after._num_groups = state._num_groups - (if x = y then 0 else 1) ∧
      (∀ v z, v < state._ps.size → RootOf state._ps v z →
        RootOf after._ps v (if x = y then z
          else if z = (if unionRoot state._ps x y = x then y else x).toNat
            then (unionRoot state._ps x y).toNat else z)) ∧
      UnionTrace state sizes after ∧ stop ≤ start + 3 + 2 * state._ps.size.log2 := by
  obtain ⟨x, first, mid, ranA, hx, rootA, va, ca, na, wa⟩ :=
    root_contract state sizes valid a aValid.1 aValid.2 (start + 1)
  obtain ⟨y, compressed, stop, ranB, hy, rootB, vb, cb, nb, wb⟩ :=
    root_contract first sizes va b bValid.1 (by rw [na]; exact bValid.2) mid
  have phase := generated_unite_after_roots state first compressed a b x y start mid stop aValid bValid ranA ranB
  have frame := comp_trans _ _ _ ca cb
  have oldB := rootOf_comp _ _ ca b.toNat y.toNat rootB
  have xRoot : IsRoot compressed._ps x.toNat := (frame.root_iff _).mpr rootA.2
  have yRoot : IsRoot compressed._ps y.toNat := (frame.root_iff _).mpr oldB.2
  have groups : compressed._num_groups = state._num_groups := by
    rw [vb.groups, valid.groups, rootCount_compress frame]
  have vertices : compressed._n = state._n := nb.trans na
  have elapsed : stop ≤ start + 3 + 2 * state._ps.size.log2 := by
    rw [ca.size] at wb
    omega
  have copyRoots (v z : Nat) (inside : v < state._ps.size) (root : RootOf state._ps v z) :
      RootOf compressed._ps v z := rootOf_preserved vb frame inside root
  have sourceValueX : get compressed._ps x = get state._ps x := frame.root_val _ rootA.2
  have sourceValueY : get compressed._ps y = get state._ps y := frame.root_val _ oldB.2
  by_cases equal : x = y
  · refine ⟨x, y, compressed, sizes, stop, ?_, rootA, oldB, vb, vertices, ?_, ?_, .same compressed vb frame, elapsed⟩
    · simpa [unionRoot, equal] using phase
    · simpa [equal] using groups
    · intro v z inside root
      simpa [equal] using copyRoots v z inside root
  · by_cases swap : -(get compressed._ps x) < -(get compressed._ps y)
    · have chosen : unionRoot state._ps x y = y := by
        simpa [unionRoot, ← sourceValueX, ← sourceValueY, swap]
      refine ⟨x, y, mergeInto compressed y x, joinedSize sizes y.toNat x.toNat, stop,
        ?_, rootA, oldB, vb.link compressed sizes y x hy hx yRoot xRoot (Ne.symm equal) (by omega),
        vertices, ?_, ?_, .join compressed y x vb frame hy hx yRoot xRoot (Ne.symm equal), elapsed⟩
      · simpa [equal, swap, chosen, mergeInto] using phase
      · simp [mergeInto, equal, groups]
      · intro v z inside root
        simpa [equal, (Ne.symm equal), chosen, mergeInto] using
          link_root hy hx yRoot xRoot (Ne.symm equal) (copyRoots v z inside root)
    · have chosen : unionRoot state._ps x y = x := by
        simpa [unionRoot, ← sourceValueX, ← sourceValueY, swap]
      refine ⟨x, y, mergeInto compressed x y, joinedSize sizes x.toNat y.toNat, stop,
        ?_, rootA, oldB, vb.link compressed sizes x y hx hy xRoot yRoot equal (by omega),
        vertices, ?_, ?_, .join compressed x y vb frame hx hy xRoot yRoot equal, elapsed⟩
      · simpa [equal, swap, chosen, mergeInto] using phase
      · simp [mergeInto, equal, groups]
      · intro v z inside root
        simpa [equal, chosen, mergeInto] using
          link_root hx hy xRoot yRoot equal (copyRoots v z inside root)

end Proofs.Cpp.DisjointSet
