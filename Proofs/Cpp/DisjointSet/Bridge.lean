import Proofs.Cpp.Gen.DisjointSet
import Proofs.Cpp.UnionFind

open Proofs.Cpp Proofs.Cpp.Gen
open Proofs.Cpp.UnionFind

namespace Proofs.Cpp.DisjointSet

def legacy (forest : cp.UnionFind) : cp.DisjointSet :=
  ⟨forest._ps, forest._num_groups, forest._n⟩

def modern (forest : cp.DisjointSet) : cp.UnionFind :=
  ⟨forest._ps, forest._num_groups, forest._n⟩

theorem legacy_modern (forest : cp.DisjointSet) : legacy (modern forest) = forest := by
  cases forest
  rfl

theorem modern_legacy (forest : cp.UnionFind) : modern (legacy forest) = forest := by
  cases forest
  rfl

def result (output : Option ((α × cp.UnionFind) × Nat)) :
    Option ((α × cp.DisjointSet) × Nat) :=
  output.map fun ((value, forest), stop) => ((value, legacy forest), stop)

theorem init_transfer (n : Int) (start : Nat) :
    (cp.DisjointSet.init n).run start =
      ((cp.UnionFind.init_int n).run start).map fun (forest, stop) => (legacy forest, stop) := by
  simp [cp.DisjointSet.init, cp.UnionFind.init_int, legacy, tick, tickN, check, StateT.run]
  split <;> rfl

private theorem run_tick (start : Nat) : tick.run start = some ((), start + 1) := rfl

private theorem run_check (condition : Bool) (clock : Nat) :
    (check condition).run clock = if condition then some ((), clock) else none := by
  cases condition <;> rfl

private theorem run_return (value : α) (start : Nat) :
    (pure value : M α).run start = some (value, start) := rfl

private theorem bind_some (value : α) (next : α → Option β) :
    (some value >>= next) = next value := rfl

private theorem bind_none (next : α → Option β) : (none >>= next) = none := rfl

theorem root_rec_transfer (fuel : Nat) (forest : cp.UnionFind) (a : Int) (start : Nat) :
    (cp.DisjointSet.root_rec fuel (legacy forest) a).run start =
      result ((cp.UnionFind.root_rec fuel forest a).run start) := by
  induction fuel generalizing forest a start with
  | zero => rfl
  | succ fuel ih =>
    cases forest with
    | mk parents groups vertices =>
      simp only [cp.DisjointSet.root_rec, cp.UnionFind.root_rec, legacy, StateT.run_bind,
        run_tick, bind_some, run_check]
      have invocation := ih ⟨parents, groups, vertices⟩ (get parents a) (start + 1)
      have compareBranch :
          (do
            let r ← (cp.DisjointSet.root_rec fuel ⟨parents, groups, vertices⟩ (get parents a)).run
              (start + 1)
            some ((get (set r.1.2._ps a r.1.1) a,
              (⟨set r.1.2._ps a r.1.1, r.1.2._num_groups, r.1.2._n⟩ : cp.DisjointSet)), r.2)) =
          result (do
            let r ← (cp.UnionFind.root_rec fuel ⟨parents, groups, vertices⟩ (get parents a)).run
              (start + 1)
            some ((get (set r.1.2._ps a r.1.1) a,
              (⟨set r.1.2._ps a r.1.1, r.1.2._num_groups, r.1.2._n⟩ : cp.UnionFind)), r.2)) := by
        rw [show (cp.DisjointSet.root_rec fuel ⟨parents, groups, vertices⟩ (get parents a)).run
          (start + 1) = _ from invocation]
        cases (cp.UnionFind.root_rec fuel ⟨parents, groups, vertices⟩ (get parents a)).run (start + 1) with
        | none => rfl
        | some output => rcases output with ⟨⟨r, ps, groups, vertices⟩, stop⟩; rfl
      let valid := decide (0 ≤ a) && decide (a < vertices)
      let atRoot := decide (get parents a < 0)
      let checkInput : Option (Unit × Nat) := if valid then some ((), start + 1) else none
      change
        (checkInput >>= fun p =>
          (if atRoot then pure (a, (⟨parents, groups, vertices⟩ : cp.DisjointSet)) else do
            let r ← cp.DisjointSet.root_rec fuel ⟨parents, groups, vertices⟩ (get parents a)
            pure (get (set r.2._ps a r.1) a, ⟨set r.2._ps a r.1, r.2._num_groups, r.2._n⟩)).run p.2) =
        result (checkInput >>= fun p =>
          (if atRoot then pure (a, (⟨parents, groups, vertices⟩ : cp.UnionFind)) else do
            let r ← cp.UnionFind.root_rec fuel ⟨parents, groups, vertices⟩ (get parents a)
            pure (get (set r.2._ps a r.1) a, ⟨set r.2._ps a r.1, r.2._num_groups, r.2._n⟩)).run p.2)
      by_cases good : valid = true
      · have checked : checkInput = some ((), start + 1) := by simp [checkInput, good]
        rw [checked]
        simp only [bind_some]
        by_cases root : atRoot = true
        · simp only [root, ite_true, run_return]
          rfl
        · simp only [ite_eq_right root, StateT.run_bind, run_return]
          exact compareBranch
      · have rejected : checkInput = none := by simp [checkInput, good]
        rw [rejected]
        rfl

theorem root_transfer (forest : cp.UnionFind) (a : Int) (start : Nat) :
    (cp.DisjointSet.root (legacy forest) a).run start =
      result ((cp.UnionFind.root forest a).run start) :=
  root_rec_transfer fuel forest a start

theorem groups_transfer (forest : cp.UnionFind) (start : Nat) :
    (cp.DisjointSet.getNum (legacy forest)).run start =
      result ((cp.UnionFind.num_groups forest).run start) := by
  cases forest
  rfl

private def validVertex (n a : Int) : Bool := decide (0 ≤ a) && decide (a < n)

private def withRoots (limit : S → Int) (root : S → Int → M (Int × S))
    (done : Int → Int → S → M (R × S)) (forest : S) (a b : Int) : M (R × S) := do
  tick
  check (validVertex (limit forest) a)
  check (validVertex (limit forest) b)
  let first ← root forest a
  let second ← root first.2 b
  done first.1 second.1 second.2

private theorem withRoots_transfer
    (findLegacy : cp.DisjointSet → Int → M (Int × cp.DisjointSet))
    (findModern : cp.UnionFind → Int → M (Int × cp.UnionFind))
    (related : ∀ forest a start,
      (findLegacy (legacy forest) a).run start = result ((findModern forest a).run start))
    (fromLegacy : Int → Int → cp.DisjointSet → M (R × cp.DisjointSet))
    (fromModern : Int → Int → cp.UnionFind → M (R × cp.UnionFind))
    (finish : ∀ x y forest start, (fromLegacy x y (legacy forest)).run start =
      result ((fromModern x y forest).run start))
    (forest : cp.UnionFind) (a b : Int) (start : Nat) :
      (withRoots cp.DisjointSet._n findLegacy fromLegacy (legacy forest) a b).run start =
        result ((withRoots cp.UnionFind._n findModern fromModern forest a b).run start) := by
  let checkedA := (check (validVertex forest._n a)).run (start + 1)
  change
    (checkedA >>= fun firstCheck =>
      (check (validVertex forest._n b)).run firstCheck.2 >>= fun secondCheck =>
      (findLegacy (legacy forest) a).run secondCheck.2 >>= fun first =>
      (findLegacy first.1.2 b).run first.2 >>= fun second =>
      (fromLegacy first.1.1 second.1.1 second.1.2).run second.2) =
    result (checkedA >>= fun firstCheck =>
      (check (validVertex forest._n b)).run firstCheck.2 >>= fun secondCheck =>
      (findModern forest a).run secondCheck.2 >>= fun first =>
      (findModern first.1.2 b).run first.2 >>= fun second =>
      (fromModern first.1.1 second.1.1 second.1.2).run second.2)
  cases checkedA with
  | none => rfl
  | some firstCheck =>
    simp only [bind_some]
    cases (check (validVertex forest._n b)).run firstCheck.2 with
    | none => rfl
    | some secondCheck =>
      simp only [bind_some]
      rw [related]
      cases (findModern forest a).run secondCheck.2 with
      | none => rfl
      | some first =>
        rcases first with ⟨⟨x, firstForest⟩, firstStop⟩
        simp only [result, Option.map_some, bind_some]
        rw [related]
        cases (findModern firstForest b).run firstStop with
        | none => rfl
        | some second =>
          rcases second with ⟨⟨y, secondForest⟩, secondStop⟩
          simpa only [result, Option.map_some, bind_some] using finish x y secondForest secondStop

theorem same_transfer (forest : cp.UnionFind) (a b : Int) (start : Nat) :
    (cp.DisjointSet.same (legacy forest) a b).run start =
      result ((cp.UnionFind.same forest a b).run start) := by
  exact withRoots_transfer cp.DisjointSet.root cp.UnionFind.root root_transfer (fun x y f => pure (decide (x = y), f))
    (fun x y f => pure (decide (x = y), f)) (by intros; rfl) forest a b start

private def linkRoots (parents : S → Array Int) (groupCount vertices : S → Int)
    (pack : Array Int → Int → Int → S) (x y : Int) (forest : S) : M (Int × S) := do
  if decide (x = y) then return (x, forest)
  let mut first := x
  let mut second := y
  let mut ps := parents forest
  if decide (-(get ps first) < -(get ps second)) then
    let saved := first
    first := second
    second := saved
  ps := set ps first (get ps first + get ps second)
  ps := set ps second first
  return (first, pack ps (groupCount forest - 1) (vertices forest))

theorem unite_transfer (forest : cp.UnionFind) (a b : Int) (start : Nat) :
    (cp.DisjointSet.unite (legacy forest) a b).run start =
      result ((cp.UnionFind.unite forest a b).run start) := by
  refine withRoots_transfer cp.DisjointSet.root cp.UnionFind.root root_transfer
    (linkRoots cp.DisjointSet._ps cp.DisjointSet._num_groups cp.DisjointSet._n cp.DisjointSet.mk)
    (linkRoots cp.UnionFind._ps cp.UnionFind._num_groups cp.UnionFind._n cp.UnionFind.mk) ?_ forest a b start
  intro x y state clock
  cases state with
  | mk parents groups vertices =>
    by_cases sameRoot : x = y
    · simp [linkRoots, legacy, sameRoot, result, run_return]
    · by_cases swap : -(get parents x) < -(get parents y)
      · simp [linkRoots, legacy, sameRoot, swap, result, run_return]
      · simp [linkRoots, legacy, sameRoot, swap, result, run_return]

private def withRoot (limit : S → Int) (root : S → Int → M (Int × S))
    (done : Int → S → M (R × S)) (forest : S) (a : Int) : M (R × S) := do
  tick
  check (validVertex (limit forest) a)
  let first ← root forest a
  done first.1 first.2

private theorem withRoot_transfer
    (findLegacy : cp.DisjointSet → Int → M (Int × cp.DisjointSet))
    (findModern : cp.UnionFind → Int → M (Int × cp.UnionFind))
    (related : ∀ forest a start,
      (findLegacy (legacy forest) a).run start = result ((findModern forest a).run start))
    (fromLegacy : Int → cp.DisjointSet → M (R × cp.DisjointSet))
    (fromModern : Int → cp.UnionFind → M (R × cp.UnionFind))
    (finish : ∀ x forest start, (fromLegacy x (legacy forest)).run start =
      result ((fromModern x forest).run start))
    (forest : cp.UnionFind) (a : Int) (start : Nat) :
      (withRoot cp.DisjointSet._n findLegacy fromLegacy (legacy forest) a).run start =
        result ((withRoot cp.UnionFind._n findModern fromModern forest a).run start) := by
  let checked := (check (validVertex forest._n a)).run (start + 1)
  change
    (checked >>= fun condition =>
      (findLegacy (legacy forest) a).run condition.2 >>= fun first =>
      (fromLegacy first.1.1 first.1.2).run first.2) =
    result (checked >>= fun condition =>
      (findModern forest a).run condition.2 >>= fun first =>
      (fromModern first.1.1 first.1.2).run first.2)
  cases checked with
  | none => rfl
  | some condition =>
    simp only [bind_some]
    rw [related]
    cases (findModern forest a).run condition.2 with
    | none => rfl
    | some first =>
      rcases first with ⟨⟨root, after⟩, stop⟩
      simpa only [result, Option.map_some, bind_some] using finish root after stop

theorem size_transfer (forest : cp.UnionFind) (a : Int) (start : Nat) :
    (cp.DisjointSet.size_ (legacy forest) a).run start =
      result ((cp.UnionFind.size_ forest a).run start) := by
  exact withRoot_transfer cp.DisjointSet.root cp.UnionFind.root root_transfer
    (fun x f => pure (-(get f._ps x), f))
    (fun x f => pure (-(get f._ps x), f)) (by intros; rfl) forest a start

private theorem withRoots_run {limit : S → Int} {root : S → Int → M (Int × S)}
    (done : Int → Int → S → M (R × S)) (forest firstState secondState : S)
    (a b firstRoot secondRoot : Int) (start middle stop : Nat)
    (ha : 0 ≤ a ∧ a < limit forest) (hb : 0 ≤ b ∧ b < limit forest)
    (first : (root forest a).run (start + 1) = some ((firstRoot, firstState), middle))
    (second : (root firstState b).run middle = some ((secondRoot, secondState), stop)) :
    (withRoots limit root done forest a b).run start = (done firstRoot secondRoot secondState).run stop := by
  have validA : validVertex (limit forest) a = true := by simp [validVertex, ha.1, ha.2]
  have validB : validVertex (limit forest) b = true := by simp [validVertex, hb.1, hb.2]
  simp only [withRoots, StateT.run_bind, run_tick, bind_some, run_check, validA, validB,
    ite_true, first, second]

theorem generated_same_after_roots (forest firstState secondState : cp.DisjointSet)
    (a b firstRoot secondRoot : Int) (start middle stop : Nat)
    (ha : 0 ≤ a ∧ a < forest._n) (hb : 0 ≤ b ∧ b < forest._n)
    (first : (cp.DisjointSet.root forest a).run (start + 1) = some ((firstRoot, firstState), middle))
    (second : (cp.DisjointSet.root firstState b).run middle = some ((secondRoot, secondState), stop)) :
    (cp.DisjointSet.same forest a b).run start =
      some ((decide (firstRoot = secondRoot), secondState), stop) :=
  withRoots_run (fun x y f => pure (decide (x = y), f)) forest firstState secondState
    a b firstRoot secondRoot start middle stop ha hb first second

theorem generated_size_after_root (forest after : cp.DisjointSet) (a root : Int)
    (start stop : Nat) (ha : 0 ≤ a ∧ a < forest._n)
    (found : (cp.DisjointSet.root forest a).run (start + 1) = some ((root, after), stop)) :
    (cp.DisjointSet.size_ forest a).run start = some ((-(get after._ps root), after), stop) := by
  have valid : validVertex forest._n a = true := by simp [validVertex, ha.1, ha.2]
  change (withRoot cp.DisjointSet._n cp.DisjointSet.root (fun x f => pure (-(get f._ps x), f)) forest a).run
    start = _
  simp only [withRoot, StateT.run_bind, run_tick, bind_some, run_check, valid, ite_true, found, run_return]

theorem generated_unite_after_roots (forest firstState secondState : cp.DisjointSet)
    (a b firstRoot secondRoot : Int) (start middle stop : Nat)
    (ha : 0 ≤ a ∧ a < forest._n) (hb : 0 ≤ b ∧ b < forest._n)
    (first : (cp.DisjointSet.root forest a).run (start + 1) = some ((firstRoot, firstState), middle))
    (second : (cp.DisjointSet.root firstState b).run middle = some ((secondRoot, secondState), stop)) :
    (cp.DisjointSet.unite forest a b).run start =
      some (if firstRoot = secondRoot then ((firstRoot, secondState), stop)
        else if -(get secondState._ps firstRoot) < -(get secondState._ps secondRoot) then
          ((secondRoot, ⟨UnionFind.link secondState._ps secondRoot firstRoot,
            secondState._num_groups - 1, secondState._n⟩), stop)
        else ((firstRoot, ⟨UnionFind.link secondState._ps firstRoot secondRoot,
          secondState._num_groups - 1, secondState._n⟩), stop)) := by
  let done := linkRoots cp.DisjointSet._ps cp.DisjointSet._num_groups cp.DisjointSet._n cp.DisjointSet.mk
  change (withRoots cp.DisjointSet._n cp.DisjointSet.root done forest a b).run start = _
  rw [withRoots_run done forest firstState secondState a b firstRoot secondRoot start middle stop ha hb first second]
  by_cases equal : firstRoot = secondRoot
  · simp [done, linkRoots, equal, run_return]
  · by_cases chooseSecond : -(get secondState._ps firstRoot) < -(get secondState._ps secondRoot)
    · simp [done, linkRoots, equal, chooseSecond, UnionFind.link, run_return]
    · simp [done, linkRoots, equal, chooseSecond, UnionFind.link, run_return]

/-- A successful root search makes every non-root vertex on its path point to the representative. -/
theorem root_rec_compresses (budget : Nat) (before : cp.DisjointSet)
    (vertices : before._n = before._ps.size)
    (a : Int) (start : Nat) (r : Int) (after : cp.DisjointSet) (stop : Nat)
    (run : (cp.DisjointSet.root_rec budget before a).run start = some ((r, after), stop)) :
    after._ps.size = before._ps.size ∧
      ∀ i, Reach before._ps a.toNat i → i ≠ r.toNat → after._ps[i]! = r := by
  induction budget generalizing a start r after stop with
  | zero =>
    change none = _ at run
    contradiction
  | succ budget ih =>
    obtain ⟨parents, groups, n⟩ := before
    simp only at vertices
    simp only [cp.DisjointSet.root_rec, StateT.run_bind, run_tick, bind_some, run_check] at run
    by_cases valid : 0 ≤ a ∧ a < n
    · have index : a.toNat < parents.size := by omega
      have checked : (decide (0 ≤ a) && decide (a < n)) = true := by simp [valid.1, valid.2]
      simp only [checked, ite_true, bind_some] at run
      by_cases atRoot : get parents a < 0
      · simp only [atRoot, decide_true, ite_true, run_return, Option.some.injEq, Prod.mk.injEq] at run
        obtain ⟨⟨rfl, rfl⟩, rfl⟩ := run
        refine ⟨rfl, fun i path different => ?_⟩
        exact (different (root_reach_eq parents a.toNat i atRoot path)).elim
      · simp only [atRoot, decide_false, Bool.false_eq_true, ite_false, StateT.run_bind,
          run_return] at run
        cases branch : (cp.DisjointSet.root_rec budget ⟨parents, groups, n⟩ (get parents a)).run
            (start + 1) with
        | none => simp only [branch, bind_none, reduceCtorEq] at run
        | some outcome =>
          obtain ⟨⟨representative, compressed⟩, done⟩ := outcome
          simp only [branch, bind_some, Option.some.injEq, Prod.mk.injEq] at run
          obtain ⟨⟨hs, ha⟩, _⟩ := run
          obtain ⟨length, recursive⟩ := ih _ _ _ _ _ branch
          have inside : a.toNat < compressed._ps.size := by
            change compressed._ps.size = parents.size at length
            omega
          have lookup := getElemBang_set compressed._ps a representative a.toNat inside
          change (set compressed._ps a representative)[a.toNat]! = r at hs
          rw [lookup, ite_eq_left rfl] at hs
          subst r after
          refine ⟨(size_set _ _ _).trans length, fun i path different => ?_⟩
          rw [getElemBang_set _ _ _ _ inside]
          by_cases first : i = a.toNat
          · simp only [first, ite_true]
          · rw [ite_eq_right first]
            have edge : Parent parents a.toNat (get parents a).toNat :=
              ⟨index, Int.le_of_not_gt atRoot, rfl⟩
            exact recursive i (reach_next parents a.toNat i _ path (Ne.symm first) edge) different
    · have rejected : (decide (0 ≤ a) && decide (a < n)) = false := by
        cases h : (decide (0 ≤ a) && decide (a < n))
        · rfl
        · exact (valid (by simpa using h)).elim
      simp only [rejected, Bool.false_eq_true, ite_false, bind_none, reduceCtorEq] at run

end Proofs.Cpp.DisjointSet
