import Proofs.Cpp.DisjointSet.SizedForest

open Std.Do Proofs.Cpp Proofs.Cpp.Gen
open Proofs.Cpp.UnionFind

namespace Proofs.Cpp.DisjointSet

def weightSum (weight : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => weightSum weight k + weight k

theorem weightSum_equal {left right : Nat → Nat} {n : Nat} (same : ∀ i, i < n → left i = right i) :
    weightSum left n = weightSum right n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [weightSum, weightSum, ih (fun i hi => same i (by omega)), same n (by omega)]

theorem weightSum_bound {weight : Nat → Nat} {i n : Nat} (inside : i < n) :
    weight i ≤ weightSum weight n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [weightSum]
    by_cases last : i = n
    · subst i
      omega
    · exact le_trans (ih (by omega)) (Nat.le_add_right _ _)

theorem weightSum_pair_bound {weight : Nat → Nat} {i j n : Nat} (insideI : i < n) (insideJ : j < n)
    (different : i ≠ j) : weight i + weight j ≤ weightSum weight n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [weightSum]
    by_cases lastI : i = n
    · subst i
      have h := weightSum_bound (weight := weight) (i := j) (n := n) (by omega)
      omega
    by_cases lastJ : j = n
    · subst j
      have h := weightSum_bound (weight := weight) (i := i) (n := n) (by omega)
      omega
    exact le_trans (ih (by omega) (by omega)) (Nat.le_add_right _ _)

def replaceWeight (weight : Nat → Nat) (index value i : Nat) : Nat :=
  if i = index then value else weight i

theorem weightSum_replace {weight : Nat → Nat} {index n : Nat} (inside : index < n) (value : Nat) :
    weightSum (replaceWeight weight index value) n + weight index =
      weightSum weight n + value := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [weightSum, replaceWeight]
    by_cases last : index = n
    · subst index
      rw [ite_eq_left rfl, weightSum_equal (left := replaceWeight weight n value) (right := weight)
        (fun i hi => ite_eq_right (by omega : i ≠ n))]
      omega
    · rw [ite_eq_right (Ne.symm last)]
      have balanced := ih (by omega)
      omega

def rootWeight (parents : Array Int) (i : Nat) : Nat := (-parents[i]!).toNat

def rootMass (parents : Array Int) : Nat := weightSum (rootWeight parents) parents.size

theorem rootMass_compress {parents after : Array Int} (sameRoots : Comp parents after) :
    rootMass after = rootMass parents := by
  unfold rootMass
  rw [sameRoots.size]
  apply weightSum_equal
  intro i within
  by_cases originalRoot : IsRoot parents i
  · simp [rootWeight, sameRoots.root_val i originalRoot]
  · have before : 0 ≤ parents[i]! := by
      by_contra! negative
      exact originalRoot ⟨within, negative⟩
    have after' : 0 ≤ after[i]! := by
      by_contra! negative
      exact originalRoot ((sameRoots.root_iff i).mp ⟨by rwa [sameRoots.size], negative⟩)
    simp [rootWeight, Int.toNat_eq_zero.mpr (by omega : -after[i]! ≤ 0),
      Int.toNat_eq_zero.mpr (by omega : -parents[i]! ≤ 0)]

theorem rootMass_pair_bound {parents : Array Int} {sizeAtLink : Nat → Nat}
    (certificate : SizeCertificate parents sizeAtLink) (mass : rootMass parents = parents.size)
    {first second : Nat} (rootFirst : IsRoot parents first) (rootSecond : IsRoot parents second)
    (distinct : first ≠ second) : sizeAtLink first + sizeAtLink second ≤ parents.size := by
  rw [certificate.rootSize first rootFirst, certificate.rootSize second rootSecond, ← mass]
  exact weightSum_pair_bound (weight := rootWeight parents) rootFirst.1 rootSecond.1 distinct

theorem rootMass_link {parents : Array Int} {sizeAtLink : Nat → Nat}
    (certificate : SizeCertificate parents sizeAtLink) (first second : Int)
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second)
    (firstRoot : IsRoot parents first.toNat) (secondRoot : IsRoot parents second.toNat)
    (distinct : first ≠ second) :
    rootMass (UnionFind.link parents first second) = rootMass parents := by
  let combined := rootWeight parents first.toNat + rootWeight parents second.toNat
  let raised := replaceWeight (rootWeight parents) first.toNat combined
  let removed := replaceWeight raised second.toNat 0
  have different : first.toNat ≠ second.toNat := by omega
  have data := link_get parents first second firstNonnegative secondNonnegative firstRoot.1 secondRoot.1 distinct
  have sameSize := (link_forest parents (heightRank parents.size sizeAtLink) certificate.forest
    first second firstNonnegative secondNonnegative firstRoot secondRoot distinct).2
  have equals (i : Nat) : rootWeight (UnionFind.link parents first second) i = removed i := by
    unfold rootWeight
    rw [data]
    by_cases atSecond : i = second.toNat
    · rw [ite_eq_left atSecond]
      simp only [removed, replaceWeight, atSecond, ite_eq_left rfl]
      exact Int.toNat_eq_zero.mpr (by omega)
    · rw [ite_eq_right atSecond]
      simp only [removed, raised, replaceWeight, ite_eq_right atSecond]
      by_cases atFirst : i = first.toNat
      · rw [ite_eq_left atFirst]
        simp only [ite_eq_left atFirst, combined, rootWeight]
        have left := firstRoot.2
        have right := secondRoot.2
        omega
      · simp only [ite_eq_right atFirst, rootWeight]
  unfold rootMass
  rw [sameSize, weightSum_equal (left := rootWeight (UnionFind.link parents first second))
    (right := removed) (fun i _ => equals i)]
  have increase := weightSum_replace (weight := rootWeight parents) firstRoot.1 combined
  have decrease := weightSum_replace (weight := raised) secondRoot.1 0
  have beforeSecond : raised second.toNat = rootWeight parents second.toNat := by
    simp [raised, replaceWeight, different.symm]
  change weightSum raised parents.size + rootWeight parents first.toNat =
    weightSum (rootWeight parents) parents.size + combined at increase
  change weightSum removed parents.size + raised second.toNat =
    weightSum raised parents.size + 0 at decrease
  rw [beforeSecond] at decrease
  dsimp [combined] at increase
  omega

theorem weightSum_ones (n : Nat) : weightSum (fun _ => 1) n = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [weightSum, ih]

theorem generated_init_mass (n : Int) (nonnegative : 0 ≤ n) (fits : n < 2 ^ 31) (start : Nat) :
    ∃ state stop, (cp.DisjointSet.init n).run start = some (state, stop) ∧
      state._ps.size = n.toNat ∧ state._n = n ∧ state._num_groups = n ∧
      SizeCertificate state._ps (fun _ => 1) ∧ rootMass state._ps = state._ps.size ∧
      (∀ i, i < state._ps.size → IsRoot state._ps i) ∧ stop = start + 1 + n.toNat := by
  obtain ⟨state, stop, ran, len, single, vertices, groups, inv, elapsed⟩ :=
    run_of_triple (init_int_spec n nonnegative fits start)
  have transfer := init_transfer n start
  rw [ran] at transfer
  have parents (i : Nat) (inside : i < state._ps.size) : state._ps[i]! = -1 :=
    (single i (by omega)).2
  have noEdge (i j : Nat) (edge : Parent state._ps i j) : False := by
    have sign := edge.2.1
    rw [parents i edge.1] at sign
    omega
  have cert : SizeCertificate state._ps (fun _ => 1) :=
    ⟨fun i j edge => (noEdge i j edge).elim, fun _ _ => by decide, fun _ hi => by omega,
      fun i j edge => (noEdge i j edge).elim,
      fun i root => by simp [parents i root.1]⟩
  have mass : rootMass state._ps = state._ps.size := by
    unfold rootMass
    rw [weightSum_equal (right := fun _ => 1) (fun i hi => by simp [rootWeight, parents i hi]),
      weightSum_ones]
  exact ⟨legacy state, stop, transfer, len, vertices, groups, cert, mass,
    fun i hi => (single i (by change i < state._ps.size at hi; omega)).1, elapsed⟩

end Proofs.Cpp.DisjointSet
