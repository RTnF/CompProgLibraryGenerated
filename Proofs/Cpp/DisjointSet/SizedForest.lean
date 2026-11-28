import Proofs.Cpp.DisjointSet.Bridge

open Std.Do Proofs.Cpp Proofs.Cpp.Gen
open Proofs.Cpp.UnionFind

namespace Proofs.Cpp.DisjointSet

/-- A non-root retains the component size it had when it last was a root. -/
structure SizeCertificate (parents : Array Int) (sizeAtLink : Nat → Nat) : Prop where
  inside : ∀ i j, Parent parents i j → j < parents.size
  positive : ∀ i, i < parents.size → 0 < sizeAtLink i
  bounded : ∀ i, i < parents.size → sizeAtLink i ≤ parents.size
  doubles : ∀ i j, Parent parents i j → 2 * sizeAtLink i ≤ sizeAtLink j
  rootSize : ∀ i, IsRoot parents i → sizeAtLink i = (-parents[i]!).toNat

def heightRank (vertices : Nat) (sizeAtLink : Nat → Nat) (i : Nat) : Nat :=
  vertices.log2 - (sizeAtLink i).log2

private theorem log2_le_log2 {a b : Nat} (apos : 0 < a) (ab : a ≤ b) :
    a.log2 ≤ b.log2 :=
  (Nat.le_log2 (by omega)).mpr (le_trans (Nat.log2_self_le (by omega)) ab)

theorem heightRank_bounds (vertices : Nat) (sizeAtLink : Nat → Nat) (i : Nat) :
    heightRank vertices sizeAtLink i ≤ vertices.log2 := Nat.sub_le _ _

theorem SizeCertificate.forest {parents : Array Int} {sizeAtLink : Nat → Nat}
    (certificate : SizeCertificate parents sizeAtLink) :
    Forest parents (heightRank parents.size sizeAtLink) := by
  constructor
  · intro i hi sign
    exact certificate.inside i parents[i]!.toNat ⟨hi, sign, rfl⟩
  · intro i hi sign
    let j := parents[i]!.toNat
    have edge : Parent parents i j := ⟨hi, sign, rfl⟩
    have hj := certificate.inside i j edge
    have strictly : (sizeAtLink i).log2 < (sizeAtLink j).log2 := by
      have positive := certificate.positive i hi
      have grows := log2_le_log2 (show 0 < 2 * sizeAtLink i by omega) (certificate.doubles i j edge)
      rw [Nat.log2_two_mul (by omega : sizeAtLink i ≠ 0)] at grows
      omega
    have bound := log2_le_log2 (certificate.positive j hj) (certificate.bounded j hj)
    change parents.size.log2 - (sizeAtLink j).log2 < parents.size.log2 - (sizeAtLink i).log2
    omega

theorem SizeCertificate.reach_grows {parents : Array Int} {sizeAtLink : Nat → Nat}
    (certificate : SizeCertificate parents sizeAtLink) {i j : Nat} (path : Reach parents i j) :
    sizeAtLink i ≤ sizeAtLink j := by
  induction path with
  | refl => rfl
  | step i j k edge _ later =>
    have grows := certificate.doubles i j edge
    omega

theorem SizeCertificate.reach_doubles {parents : Array Int} {sizeAtLink : Nat → Nat}
    (certificate : SizeCertificate parents sizeAtLink) {i j : Nat} (path : Reach parents i j)
    (strict : i ≠ j) : 2 * sizeAtLink i ≤ sizeAtLink j := by
  cases path with
  | refl => exact (strict rfl).elim
  | step i middle j edge rest =>
    exact le_trans (certificate.doubles i middle edge) (certificate.reach_grows rest)

theorem SizeCertificate.reach_inside {parents : Array Int} {sizeAtLink : Nat → Nat}
    (certificate : SizeCertificate parents sizeAtLink) {i j : Nat} (path : Reach parents i j)
    (startInside : i < parents.size) : j < parents.size := by
  induction path with
  | refl => exact startInside
  | step start middle finish first _ later => exact later (certificate.inside start middle first)

theorem SizeCertificate.compress {parents after : Array Int} {sizeAtLink : Nat → Nat}
    (certificate : SizeCertificate parents sizeAtLink) (sameRoots : Comp parents after)
    (paths : ∀ i j, Parent after i j → Reach parents i j ∧ i ≠ j) :
    SizeCertificate after sizeAtLink := by
  constructor
  · intro i j edge
    rw [sameRoots.size]
    exact certificate.reach_inside (paths i j edge).1 (by rw [← sameRoots.size]; exact edge.1)
  · intro i hi
    exact certificate.positive i (by rwa [sameRoots.size] at hi)
  · intro i hi
    rw [sameRoots.size] at hi ⊢
    exact certificate.bounded i hi
  · intro i j edge
    exact certificate.reach_doubles (paths i j edge).1 (paths i j edge).2
  · intro i root
    have beforeRoot := (sameRoots.root_iff i).mp root
    rw [sameRoots.root_val i beforeRoot]
    exact certificate.rootSize i beforeRoot

theorem compression_paths {before after : Array Int} {rank : Nat → Nat}
    (forest : Forest before rank) (sizes : after.size = before.size) (sourceVertex root : Nat)
    (reaches : Reach before sourceVertex root) (negative : before[root]! < 0)
    (r : Int) (rootIndex : r.toNat = root)
    (frame : ∀ i, after[i]! = before[i]! ∨
      (Reach before sourceVertex i ∧ i ≠ root ∧ after[i]! = r)) :
    ∀ i j, Parent after i j → Reach before i j ∧ i ≠ j := by
  intro i j edge
  rcases frame i with unchanged | ⟨visited, different, newParent⟩
  · have original : Parent before i j :=
      ⟨by rw [← sizes]; exact edge.1, by rw [← unchanged]; exact edge.2.1,
        by rw [← unchanged]; exact edge.2.2⟩
    have lower := forest.decrease i original.1 original.2.1
    rw [original.2.2] at lower
    refine ⟨Reach.step _ _ _ original (Reach.refl _), ?_⟩
    intro equal
    rw [equal] at lower
    exact (Nat.lt_irrefl _ lower)
  · have jroot : j = root := by rw [← edge.2.2, newParent, rootIndex]
    rw [jroot]
    exact ⟨reach_to_root before sourceVertex i root visited reaches negative, different⟩

theorem generated_root_height (forest : cp.DisjointSet) (sizes : Nat → Nat)
    (valid : SizeCertificate forest._ps sizes) (representation : forest._n = forest._ps.size)
    (fits : forest._ps.size < 2 ^ 31) (a : Int) (nonnegative : 0 ≤ a)
    (inside : a < forest._n) (start : Nat) :
    ∃ r after stop, (cp.DisjointSet.root forest a).run start = some ((r, after), stop) ∧
      0 ≤ r ∧ RootOf forest._ps a.toNat r.toNat ∧ SizeCertificate after._ps sizes ∧
      Comp forest._ps after._ps ∧ after._ps.size = forest._ps.size ∧ after._n = forest._n ∧
      after._num_groups = forest._num_groups ∧ stop ≤ start + 1 + forest._ps.size.log2 := by
  let rank := heightRank forest._ps.size sizes
  let state := modern forest
  have hsize : state._ps.size = forest._ps.size := rfl
  have hin : a.toNat < state._ps.size := by omega
  have enough := nrank_le rank state._ps.size a.toNat
  have budget : nrank rank state._ps.size a.toNat < fuel := by
    unfold fuel
    omega
  have model := root_rec_spec fuel state rank a valid.forest representation nonnegative hin budget start
  obtain ⟨⟨r, after⟩, stop, ran, positive, reached, found, sameSize, sameN, sameCount, _, frame, work⟩ :=
    run_of_triple model
  change (cp.UnionFind.root state a).run start = some ((r, after), stop) at ran
  have transfer := root_transfer state a start
  rw [legacy_modern, ran] at transfer
  have values := compress_comp state._ps after._ps a.toNat r positive reached found sameSize frame
  have preserve := valid.compress values
    (compression_paths valid.forest sameSize a.toNat r.toNat reached found.2 r rfl frame)
  have bound := heightRank_bounds forest._ps.size sizes a.toNat
  exact ⟨r, legacy after, stop, transfer, positive, ⟨reached, found⟩, preserve, values, sameSize,
    sameN, sameCount, by change stop ≤ start + 1 + heightRank _ _ _ at work; omega⟩

def joinedSize (sizeAtLink : Nat → Nat) (larger smaller i : Nat) : Nat :=
  if i = larger then sizeAtLink larger + sizeAtLink smaller else sizeAtLink i

theorem SizeCertificate.link {parents : Array Int} {sizeAtLink : Nat → Nat}
    (certificate : SizeCertificate parents sizeAtLink) (larger smaller : Int)
    (largeIndex : 0 ≤ larger) (smallIndex : 0 ≤ smaller)
    (largeRoot : IsRoot parents larger.toNat) (smallRoot : IsRoot parents smaller.toNat)
    (distinct : larger ≠ smaller) (ordered : sizeAtLink smaller.toNat ≤ sizeAtLink larger.toNat)
    (fits : sizeAtLink larger.toNat + sizeAtLink smaller.toNat ≤ parents.size) :
    SizeCertificate (UnionFind.link parents larger smaller) (joinedSize sizeAtLink larger.toNat smaller.toNat) := by
  have different : larger.toNat ≠ smaller.toNat := by
    intro equal
    exact distinct (by omega)
  have data := link_get parents larger smaller largeIndex smallIndex largeRoot.1 smallRoot.1 distinct
  have sameSize := (link_forest parents (heightRank parents.size sizeAtLink) certificate.forest
    larger smaller largeIndex smallIndex largeRoot smallRoot distinct).2
  have updateBounds (i : Nat) : sizeAtLink i ≤ joinedSize sizeAtLink larger.toNat smaller.toNat i := by
    unfold joinedSize
    split
    · rename_i h
      rw [h]
      omega
    · rfl
  have edgeShape (i j : Nat) (edge : Parent (UnionFind.link parents larger smaller) i j) :
      (i = smaller.toNat ∧ j = larger.toNat) ∨
        (i ≠ larger.toNat ∧ Parent parents i j) := by
    obtain ⟨within, nonnegative, parent⟩ := edge
    rw [sameSize] at within
    rw [data] at nonnegative parent
    by_cases isSmall : i = smaller.toNat
    · rw [ite_eq_left isSmall] at parent
      exact Or.inl ⟨isSmall, parent.symm⟩
    · rw [ite_eq_right isSmall] at nonnegative parent
      by_cases isLarge : i = larger.toNat
      · rw [ite_eq_left isLarge] at nonnegative
        have left := largeRoot.2
        have right := smallRoot.2
        omega
      · rw [ite_eq_right isLarge] at nonnegative parent
        exact Or.inr ⟨isLarge, within, nonnegative, parent⟩
  constructor
  · intro i j edge
    rw [sameSize]
    rcases edgeShape i j edge with ⟨_, rfl⟩ | ⟨_, old⟩
    · exact largeRoot.1
    · exact certificate.inside i j old
  · intro i hi
    rw [sameSize] at hi
    exact lt_of_lt_of_le (certificate.positive i hi) (updateBounds i)
  · intro i hi
    rw [sameSize] at hi ⊢
    unfold joinedSize
    split
    · exact fits
    · exact certificate.bounded i hi
  · intro i j edge
    rcases edgeShape i j edge with ⟨rfl, rfl⟩ | ⟨notLarge, old⟩
    · simp [joinedSize, different.symm]
      omega
    · rw [show joinedSize sizeAtLink larger.toNat smaller.toNat i = sizeAtLink i by simp [joinedSize, notLarge]]
      exact le_trans (certificate.doubles i j old) (updateBounds j)
  · intro i root
    obtain ⟨within, negative⟩ := root
    rw [sameSize] at within
    rw [data] at negative ⊢
    by_cases isSmall : i = smaller.toNat
    · rw [ite_eq_left isSmall] at negative
      omega
    · rw [ite_eq_right isSmall] at negative ⊢
      by_cases isLarge : i = larger.toNat
      · rw [ite_eq_left isLarge]
        have left := certificate.rootSize larger.toNat largeRoot
        have right := certificate.rootSize smaller.toNat smallRoot
        have negLeft := largeRoot.2
        have negRight := smallRoot.2
        simp only [joinedSize, isLarge, ite_true]
        omega
      · rw [ite_eq_right isLarge] at negative ⊢
        simpa [joinedSize, isLarge] using certificate.rootSize i ⟨within, negative⟩

end Proofs.Cpp.DisjointSet
