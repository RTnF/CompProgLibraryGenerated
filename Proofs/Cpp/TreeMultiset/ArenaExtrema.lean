import Proofs.Cpp.TreeMultiset.ArenaReadCounts

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeMultiset

def extreme {K : Type} (greatest : Bool) : Tree K → Option K
  | .empty => none
  | .node key _ _ left right =>
    (if greatest then extreme greatest right else extreme greatest left).or (some key)

def childCode {K : Type} (greatest : Bool) (row : cp.TreeMultiSet_Slot K) : UInt64 :=
  if greatest then row.right else row.left

def extremeStep {K : Type} [Inhabited K] (greatest : Bool) (arena : cp.TreeMultiSet K)
    (_ : Unit) (index : UInt64) : Cpp.M (ForInStep UInt64) := do
  Cpp.tick
  let sentinel ← cp.TreeMultiSet.none (T := K)
  let child := childCode greatest (modelCell arena index)
  if !(decide (child ≠ sentinel)) then return .done index
  return .yield child

def extremeProgram {K : Type} [Inhabited K] (greatest : Bool) (arena : cp.TreeMultiSet K) : Cpp.M (K × cp.TreeMultiSet K) := do
  Cpp.tick
  let sentinel ← cp.TreeMultiSet.none (T := K)
  Cpp.check (decide (arena.root ≠ sentinel))
  let index ← forIn Cpp.forever arena.root (extremeStep greatest arena)
  let key ← Cpp.optionalValue (modelCell arena index).key
  return (key, arena)

theorem generated_min_program {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) :
    cp.TreeMultiSet.min_ arena = extremeProgram false arena := by
  cases arena
  unfold cp.TreeMultiSet.min_ extremeProgram extremeStep childCode modelCell
  rfl

theorem generated_max_program {K : Type} [Inhabited K] (arena : cp.TreeMultiSet K) :
    cp.TreeMultiSet.max_ arena = extremeProgram true arena := by
  cases arena
  unfold cp.TreeMultiSet.max_ extremeProgram extremeStep childCode modelCell
  rfl

private theorem extreme_step_run {K : Type} [Inhabited K] (greatest : Bool) (arena : cp.TreeMultiSet K)
    (index : UInt64) (start : Nat) :
    let child := childCode greatest (modelCell arena index)
    (extremeStep greatest arena () index).run start =
      some ((if child = endIndex then .done index else .yield child), start + 2) := by
  have tickRun : Cpp.tick.run start = some ((), start + 1) := rfl
  have endRun : (cp.TreeMultiSet.none (T := K)).run (start + 1) = some (endIndex, start + 2) := rfl
  by_cases isEnd : childCode greatest (modelCell arena index) = endIndex <;>
    simp [extremeStep, StateT.run_bind, tickRun, endRun, isEnd]

theorem extreme_nonempty {K : Type} (greatest : Bool) (tree : Tree K) (nonempty : tree ≠ .empty) :
    ∃ key, extreme greatest tree = some key := by
  cases tree with
  | empty => contradiction
  | node key p n left right =>
    simp only [extreme]
    cases greatest <;> simp

theorem Realizes.empty_iff {K : Type} {arena : Array (StoredNode K)} {root : Option Nat}
    {tree : Tree K} {used : List Nat} (layout : Realizes arena root tree used) : root = none ↔ tree = .empty := by
  cases layout <;> simp

private theorem extreme_loop_spec {K : Type} [Inhabited K] (greatest : Bool)
    (arena : cp.TreeMultiSet K) (tree : Tree K) (index : UInt64) (used : List Nat)
    (layout : Realizes (storageView arena) (decode index) tree used)
    (nonempty : tree ≠ .empty) (fits : arena.slots.size ≤ 2 ^ 63)
    (fuel start : Nat) (enough : tree.height < fuel) :
    ∃ final key stop, (Cpp.loopFuel fuel index (extremeStep greatest arena)).run start = some (final, stop) ∧
      stop ≤ start + 2 * tree.height ∧ (modelCell arena final).key = some key ∧ extreme greatest tree = some key := by
  induction tree generalizing index used fuel start with
  | empty => exact (nonempty rfl).elim
  | node key priority count left right ihLeft ihRight =>
    generalize decoded : decode index = root at layout
    cases layout with
    | @node slot _ _ _ _ _ lc rc ls rs reads leftTree rightTree lf rf sep =>
      cases fuel with
      | zero => simp [Tree.height] at enough
      | succ fuel =>
        obtain ⟨_, _, view⟩ := modelCell_view arena index slot _ decoded reads fits
        let row := modelCell arena index
        have keyEq : row.key = some key := congrArg StoredNode.key view
        let child := childCode greatest row
        let subtree := if greatest then right else left
        let footprint := if greatest then rs else ls
        have subLayout : Realizes (storageView arena) (decode child) subtree footprint := by
          cases greatest
          · change Realizes (storageView arena) (decode row.left) left ls
            rw [show decode row.left = lc from congrArg StoredNode.left view]
            exact leftTree
          · change Realizes (storageView arena) (decode row.right) right rs
            rw [show decode row.right = rc from congrArg StoredNode.right view]
            exact rightTree
        have recur : ∀ begin : Nat, subtree ≠ .empty → ∃ final value stop,
            (Cpp.loopFuel fuel child (extremeStep greatest arena)).run begin = some (final, stop) ∧
            stop ≤ begin + 2 * subtree.height ∧
            (modelCell arena final).key = some value ∧ extreme greatest subtree = some value := by
          intro begin notEmpty
          have lHeight : left.height < fuel := by simp only [Tree.height] at enough; omega
          have rHeight : right.height < fuel := by simp only [Tree.height] at enough; omega
          cases greatest
          · exact ihLeft child footprint subLayout notEmpty fuel begin lHeight
          · exact ihRight child footprint subLayout notEmpty fuel begin rHeight
        have sideHeight : subtree.height ≤ max left.height right.height := by
          cases greatest
          · exact Nat.le_max_left _ _
          · exact Nat.le_max_right _ _
        have modelOut : extreme greatest (.node key priority count left right) =
            (extreme greatest subtree).or (some key) := by cases greatest <;> rfl
        have step : (extremeStep greatest arena () index).run start =
            some ((if child = endIndex then ForInStep.done index else ForInStep.yield child), start + 2) :=
          extreme_step_run greatest arena index start
        by_cases childEmpty : child = endIndex
        · have empty : subtree = .empty := subLayout.empty_iff.mp ((decode_none _).mpr childEmpty)
          refine ⟨index, key, start + 2, ?_, ?_, keyEq, ?_⟩
          · have done : (extremeStep greatest arena () index).run start =
                  some (.done index, start + 2) := by
              simpa only [ite_eq_left childEmpty] using step
            simp [Cpp.loopFuel, StateT.run_bind, done]
          · simp only [Tree.height]; omega
          · rw [modelOut, empty]
            rfl
        · have nonemptySub : subtree ≠ .empty :=
            fun same => childEmpty ((decode_none _).mp (subLayout.empty_iff.mpr same))
          obtain ⟨final, value, stop, loop, work, valueEq, result⟩ := recur (start + 2) nonemptySub
          have leading : (extremeStep greatest arena () index).run start =
              some (.yield child, start + 2) := by
            simpa only [ite_eq_right childEmpty] using step
          refine ⟨final, value, stop, ?_, ?_, valueEq, ?_⟩
          · simp [Cpp.loopFuel, StateT.run_bind, leading, loop]
          · simp only [Tree.height]; omega
          · rw [modelOut, result]
            rfl

theorem generated_extreme_entry {K : Type} [Inhabited K] (greatest : Bool)
    (arena : cp.TreeMultiSet K) (tree : Tree K) (used : List Nat)
    (layout : Realizes (storageView arena) (decode arena.root) tree used)
    (nonempty : tree ≠ .empty) (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    ∃ key stop, (extremeProgram greatest arena).run start = some ((key, arena), stop) ∧
      stop ≤ start + 2 + 2 * tree.height ∧ extreme greatest tree = some key := by
  have capacity : tree.slots ≤ arena.slots.size := by simpa [storageView] using layout.capacity
  have height := tree.height_le_slots
  have enough : tree.height < Cpp.fuel := by unfold Cpp.fuel; omega
  have present : arena.root ≠ endIndex := fun same => nonempty (layout.empty_iff.mp ((decode_none _).mpr same))
  obtain ⟨final, key, stop, loop, work, keyEq, expected⟩ :=
    extreme_loop_spec greatest arena tree arena.root used layout nonempty fits Cpp.fuel (start + 2) enough
  have loopRun : (forIn Cpp.forever arena.root (extremeStep greatest arena)).run (start + 2) = some (final, stop) := loop
  have tickRun : Cpp.tick.run start = some ((), start + 1) := rfl
  have endRun : (cp.TreeMultiSet.none (T := K)).run (start + 1) = some (endIndex, start + 2) := rfl
  refine ⟨key, stop, ?_, work, expected⟩
  simp [extremeProgram, StateT.run_bind, tickRun, endRun, Cpp.check, present, loopRun, keyEq, Cpp.optionalValue]

theorem extreme_ordered {K : Type} [LinearOrder K] (greatest : Bool) (tree : Tree K)
    (ordered : tree.Ordered) (value : K) (found : extreme greatest tree = some value) :
    (∃ count, (value, count) ∈ tree.entries) ∧
    ∀ entry ∈ tree.entries, if greatest then entry.1 ≤ value else value ≤ entry.1 := by
  induction tree generalizing value with
  | empty => simp [extreme] at found
  | node key p count left right ihLeft ihRight =>
    obtain ⟨leftOrdered, rightOrdered, less, greater⟩ := Tree.ordered_node ordered
    cases greatest
    · cases chosen : extreme false left with
      | none =>
        have absent : left = .empty := by
          by_contra h
          obtain ⟨_, positive⟩ := extreme_nonempty false left h
          rw [chosen] at positive
          contradiction
        simp [extreme, chosen] at found
        subst value
        refine ⟨⟨count, List.mem_append_right _ (List.mem_cons_self ..)⟩, ?_⟩
        intro entry mem
        simp only [Tree.entries, absent, List.nil_append] at mem
        rcases List.mem_cons.mp mem with rfl | fromRight
        · exact le_rfl
        · exact le_of_lt (greater _ fromRight)
      | some selected =>
        simp [extreme, chosen] at found
        subst value
        obtain ⟨⟨n, member⟩, bound⟩ := ihLeft leftOrdered selected chosen
        refine ⟨⟨n, List.mem_append_left _ member⟩, ?_⟩
        have keyBound := le_of_lt (less _ member)
        intro entry mem
        rcases List.mem_append.mp mem with fromLeft | rest
        · exact bound entry fromLeft
        · rcases List.mem_cons.mp rest with rfl | fromRight
          · exact keyBound
          · exact le_trans keyBound (le_of_lt (greater _ fromRight))
    · cases chosen : extreme true right with
      | none =>
        have absent : right = .empty := by
          by_contra h
          obtain ⟨_, positive⟩ := extreme_nonempty true right h
          rw [chosen] at positive
          contradiction
        simp [extreme, chosen] at found
        subst value
        refine ⟨⟨count, List.mem_append_right _ (List.mem_cons_self ..)⟩, ?_⟩
        intro entry mem
        rcases List.mem_append.mp mem with fromLeft | rest
        · exact le_of_lt (less _ fromLeft)
        · simp only [absent, Tree.entries] at rest
          rcases List.mem_cons.mp rest with rfl | impossible
          · exact le_rfl
          · exact (List.not_mem_nil impossible).elim
      | some selected =>
        simp [extreme, chosen] at found
        subst value
        obtain ⟨⟨n, member⟩, bound⟩ := ihRight rightOrdered selected chosen
        refine ⟨⟨n, List.mem_append_right _ (List.mem_cons_of_mem _ member)⟩, ?_⟩
        have keyBound := le_of_lt (greater _ member)
        intro entry mem
        rcases List.mem_append.mp mem with fromLeft | rest
        · exact le_trans (le_of_lt (less _ fromLeft)) keyBound
        · rcases List.mem_cons.mp rest with rfl | fromRight
          · exact keyBound
          · exact bound entry fromRight

theorem generated_min_spec {K : Type} [Inhabited K] [LinearOrder K] (arena : cp.TreeMultiSet K)
    (tree : Tree K) (used : List Nat)
    (layout : Realizes (storageView arena) (decode arena.root) tree used)
    (nonempty : tree ≠ .empty) (ordered : tree.Ordered)
    (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    ∃ key stop, (cp.TreeMultiSet.min_ arena).run start = some ((key, arena), stop) ∧
      stop ≤ start + 2 + 2 * tree.height ∧ (∃ count, (key, count) ∈ tree.entries) ∧
      ∀ entry ∈ tree.entries, key ≤ entry.1 := by
  rw [generated_min_program]
  obtain ⟨key, stop, run, cost, found⟩ := generated_extreme_entry false arena tree used layout nonempty fits start
  obtain ⟨mem, lower⟩ := extreme_ordered false tree ordered key found
  exact ⟨key, stop, run, cost, mem, lower⟩

theorem generated_max_spec {K : Type} [Inhabited K] [LinearOrder K] (arena : cp.TreeMultiSet K)
    (tree : Tree K) (used : List Nat)
    (layout : Realizes (storageView arena) (decode arena.root) tree used)
    (nonempty : tree ≠ .empty) (ordered : tree.Ordered)
    (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    ∃ key stop, (cp.TreeMultiSet.max_ arena).run start = some ((key, arena), stop) ∧
      stop ≤ start + 2 + 2 * tree.height ∧ (∃ count, (key, count) ∈ tree.entries) ∧
      ∀ entry ∈ tree.entries, entry.1 ≤ key := by
  rw [generated_max_program]
  obtain ⟨key, stop, run, cost, found⟩ := generated_extreme_entry true arena tree used layout nonempty fits start
  obtain ⟨mem, upper⟩ := extreme_ordered true tree ordered key found
  exact ⟨key, stop, run, cost, mem, upper⟩

end Proofs.Cpp.TreeMultiset
