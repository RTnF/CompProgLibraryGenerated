import Proofs.Cpp.TreeSet.Detach

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeSet

def released {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64) : cp.TreeSet K :=
  { putCell arena i { cell arena.slots i with key := none, left := arena.free_head } with free_head := i }

theorem released_layout {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64)
    (left right : Tree K) (key : K) (ls rs free : List Nat)
    (pending : Pending arena i left key right ls rs)
    (chain : FreeChain arena.slots arena.free_head free) (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    let next := released arena i
    (cp.TreeSet.release arena i).run start = some (next, start + 1) ∧
    next.slots.size = arena.slots.size ∧ Retained arena next [i.toNat] ∧
    Layout next.slots (cell arena.slots i).left left ls ∧
    Layout next.slots (cell arena.slots i).right right rs ∧
    FreeChain next.slots next.free_head (i.toNat :: free) := by
  let row : cp.TreeSet_Slot K := { cell arena.slots i with key := none, left := arena.free_head }
  let next := released arena i
  have inside : (slotOffset i).toNat < arena.slots.size := by
    have allocated := pending.allocated
    rwa [slotOffset_nat _ (by omega)]
  have sameSize : next.slots.size = arena.slots.size := putCell_size ..
  have written : cell next.slots i = row := cell_written arena i row inside
  have notFree : i.toNat ∉ free := fun member =>
    pending.disjoint_free chain member (List.mem_cons_self ..)
  have tail := chain.putCell_away i row pending.allocated fits notFree
  refine ⟨generated_release_run arena i inside start, sameSize, ⟨rfl, Nat.le_of_eq sameSize.symm, ?_⟩,
    pending.leftLayout.putCell_away i row pending.allocated fits pending.leftApart,
    pending.rightLayout.putCell_away i row pending.allocated fits pending.rightApart,
    ?_⟩
  · intro j range outside
    exact cell_put_away arena i j row pending.allocated range fits (fun eq => outside (by simp [eq]))
  · change FreeChain next.slots i (i.toNat :: free)
    refine .cons (by rw [sameSize]; exact pending.allocated) pending.nonnull ?_ ?_ notFree
    · rw [written]
    · rw [written]
      exact tail

private theorem tick_run (clock : Nat) : Cpp.tick.run clock = some ((), clock + 1) := rfl
private theorem sentinel_run {K : Type} (clock : Nat) :
    (cp.TreeSet.none (T := K)).run clock = some (endIndex, clock + 1) := rfl
private theorem some_bind {A B : Type} (value : A) (next : A → Option B) :
    (some value >>= next) = next value := rfl
private theorem pure_run {A : Type} (value : A) (clock : Nat) :
    (pure value : Cpp.M A).run clock = some (value, clock) := rfl
private theorem restore_result {K : Type} (source : Option ((UInt64 × cp.TreeSet K) × Nat)) :
    (source >>= fun p => some ((p.1.1, ⟨p.1.2.slots, p.1.2.root, p.1.2.free_head⟩), p.2)) =
      source := by cases source <;> rfl

private theorem generated_erase_empty_run {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (fuel : Nat) (arena : cp.TreeSet K) (key : K) (start : Nat) :
    (cp.TreeSet.erase_rec (fuel + 1) arena endIndex key).run start =
      some ((endIndex, arena), start + 3) := by
  rcases arena with ⟨slots, root, head⟩
  simp only [cp.TreeSet.erase_rec, StateT.run_bind, tick_run, sentinel_run, some_bind, decide_true,
    ite_true, pure_run]

private theorem erase_narrow_run {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (fuel : Nat) (arena : cp.TreeSet K) (i : UInt64) (key current : K) (start : Nat)
    (nonnull : i ≠ endIndex) (value : (cell arena.slots i).key = some current) (descend : key < current ∨ current < key)
    (onlyOne : current < key → ¬ key < current) :
    let row := cell arena.slots i
    (cp.TreeSet.erase_rec (fuel + 1) arena i key).run start =
      if key < current then (do
        let p ← (cp.TreeSet.erase_rec fuel arena row.left key).run (start + 2)
        (cp.TreeSet.rebalance (linkLeft p.1.2 i p.1.1) i).run p.2)
      else (do
        let p ← (cp.TreeSet.erase_rec fuel arena row.right key).run (start + 2)
        (cp.TreeSet.rebalance (linkRight p.1.2 i p.1.1) i).run p.2) := by
  rcases arena with ⟨slots, root, head⟩
  change (Cpp.get slots (slotOffset i)).key = some current at value
  simp only [slotOffset] at value
  rcases descend with goLeft | goRight
  · simp only [cp.TreeSet.erase_rec, StateT.run_bind, tick_run, sentinel_run, some_bind, nonnull,
      decide_false, Bool.false_eq_true, ite_false, Cpp.optionalValue, value, pure_run, goLeft,
      decide_true, ite_true, restore_result, linkLeft, cell, putCell, slotOffset]
  · have notLeft := onlyOne goRight
    simp only [cp.TreeSet.erase_rec, StateT.run_bind, tick_run, sentinel_run, some_bind, nonnull,
      decide_false, Bool.false_eq_true, ite_false, Cpp.optionalValue, value, pure_run, goRight,
      notLeft, decide_true, ite_true, restore_result, linkRight, cell, putCell, slotOffset]

def replaceRootLinks {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i left right : UInt64) :
    cp.TreeSet K := linkRight (linkLeft arena i left) i right

private theorem erase_match_run {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (fuel : Nat) (arena : cp.TreeSet K) (i : UInt64) (key current : K) (start : Nat)
    (nonnull : i ≠ endIndex) (value : (cell arena.slots i).key = some current)
    (notLeft : ¬ key < current) (notRight : ¬ current < key)
    (inside : (slotOffset i).toNat < arena.slots.size) :
    let row := cell arena.slots i
    let next := released arena i
    (cp.TreeSet.erase_rec (fuel + 1) arena i key).run start =
      if row.left = endIndex then some ((row.right, next), start + 4)
      else if row.right = endIndex then some ((row.left, next), start + 5)
      else (do
        let p ← (cp.TreeSet.detach_first next row.right).run (start + 5)
        (cp.TreeSet.rebalance (replaceRootLinks p.1.2 p.1.1.1 row.left p.1.1.2) p.1.1.1).run p.2) := by
  rcases arena with ⟨slots, root, head⟩
  let arena : cp.TreeSet K := ⟨slots, root, head⟩
  have release : (cp.TreeSet.release ⟨slots, root, head⟩ i).run (start + 1 + 1) =
      some (released ⟨slots, root, head⟩ i, start + 3) := generated_release_run arena i inside (start + 2)
  change (Cpp.get slots (slotOffset i)).key = some current at value
  simp only [slotOffset] at value
  by_cases noLeft : (Cpp.get slots (Cpp.toSigned 64 i.toNat)).left = endIndex <;>
    by_cases noRight : (Cpp.get slots (Cpp.toSigned 64 i.toNat)).right = endIndex <;>
    simp only [cp.TreeSet.erase_rec, StateT.run_bind, tick_run, sentinel_run, some_bind, nonnull,
      decide_false, Bool.false_eq_true, ite_false, Cpp.optionalValue, value, pure_run, release,
      notLeft, notRight, noLeft, noRight, decide_true, ite_true, restore_result, replaceRootLinks,
      cell, linkLeft, linkRight, putCell, slotOffset]


private theorem replaceRoot_layout {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i l r : UInt64)
    (left right : Tree K) (key : K) (ls rs : List Nat)
    (inside : i.toNat < arena.slots.size) (nonnull : i ≠ endIndex) (hasKey : (cell arena.slots i).key = some key)
    (ll : Layout arena.slots l left ls) (rr : Layout arena.slots r right rs)
    (xl : i.toNat ∉ ls) (xr : i.toNat ∉ rs) (apart : List.Disjoint ls rs)
    (fits : arena.slots.size ≤ 2 ^ 63) :
    let next := replaceRootLinks arena i l r
    Pending next i left key right ls rs ∧ ChangedWithin arena next [i.toNat] := by
  let one := linkLeft arena i l
  let two := replaceRootLinks arena i l r
  have oneSize := linkLeft_size arena i l
  have twoSize : two.slots.size = arena.slots.size :=
    (linkRight_size one i r).trans oneSize
  have changeFirst : ChangedWithin arena one [i.toNat] :=
    putCell_changedWithin _ _ _ inside fits (by simp)
  have changeSecond : ChangedWithin one two [i.toNat] :=
    putCell_changedWithin _ _ _ (by rwa [oneSize]) (by rwa [oneSize]) (by simp)
  have changes := changeFirst.trans changeSecond (fun _ h => h) (fun _ h => h)
  refine ⟨⟨by rwa [twoSize], nonnull, ?_, ?_, ?_, xl, xr, apart⟩, changes⟩
  · change (cell two.slots i).key = some key
    change (cell (linkRight one i r).slots i).key = _
    rw [linkRight_preserves _ _ _ (by rwa [oneSize]) (by rwa [oneSize]), linkLeft_preserves _ _ _ inside fits]
    exact hasKey
  · change Layout (linkRight one i r).slots (cell (linkRight one i r).slots i).left left ls
    rw [linkRight_preserves _ _ _ (by rwa [oneSize]) (by rwa [oneSize]), linkLeft_preserves _ _ _ inside fits]
    exact changes.layout ll (fun {_} h p => xl ((List.mem_singleton.mp p) ▸ h))
  · change Layout (linkRight one i r).slots (cell (linkRight one i r).slots i).right right rs
    rw [linkRight_preserves _ _ _ (by rwa [oneSize]) (by rwa [oneSize])]
    exact changes.layout rr (fun {_} h p => xr ((List.mem_singleton.mp p) ▸ h))

private theorem generated_erase_matching {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (fuel : Nat) (arena : cp.TreeSet K) (i : UInt64) (left right : Tree K) (key current : K)
    (ls rs free : List Nat) (pending : Pending arena i left current right ls rs)
    (available : FreeChain arena.slots arena.free_head free) (fits : arena.slots.size ≤ 2 ^ 63)
    (notLeft : ¬ key < current) (notRight : ¬ current < key) (start : Nat) :
    ∃ root next occupied remaining stop,
      (cp.TreeSet.erase_rec (fuel + 1) arena i key).run start = some ((root, next), stop) ∧
      stop ≤ start + 6 + 57 * (Tree.node left current right).height ∧
      Layout next.slots root ((Tree.node left current right).erase key) occupied ∧
      FreeChain next.slots next.free_head remaining ∧
      Retained arena next (i.toNat :: (ls ++ rs)) ∧ next.slots.size = arena.slots.size ∧
      occupied ⊆ i.toNat :: (ls ++ rs) := by
  let row := cell arena.slots i
  let releasedArena := released arena i
  have range := pending.allocated
  have inside : (slotOffset i).toNat < arena.slots.size := by rwa [slotOffset_nat _ (by omega)]
  have runChoice := erase_match_run fuel arena i key current start pending.nonnull pending.value notLeft notRight inside
  obtain ⟨releaseRun, releaseSize, releaseFrame, keptLeft, keptRight, nextFree⟩ :=
    released_layout arena i left right current ls rs free pending available fits (start + 2)
  have choiceL : left = Tree.empty → row.left = endIndex := by
    intro eq
    subst left
    exact pending.leftLayout.empty_indexes.1
  have choiceR : right = Tree.empty → row.right = endIndex := by
    intro eq
    subst right
    exact pending.rightLayout.empty_indexes.1
  have releaseWide := releaseFrame.congr_mem (show [i.toNat] ⊆ i.toNat :: (ls ++ rs) by simp)
  cases left with
  | empty =>
    refine ⟨row.right, releasedArena, rs, i.toNat :: free, start + 4, ?_, by omega, ?_, nextFree,
      releaseWide, releaseSize, ?_⟩
    · rw [runChoice, ite_eq_left (choiceL rfl)]
    · simpa [Tree.erase, notLeft, notRight] using keptRight
    · intro n h
      simp [h]
  | node al x ar =>
    have leftNonempty : row.left ≠ endIndex := pending.leftLayout.root_key.1
    cases right with
    | empty =>
      refine ⟨row.left, releasedArena, ls, i.toNat :: free, start + 5, ?_, by omega, ?_, nextFree,
        releaseWide, releaseSize, ?_⟩
      · rw [runChoice, ite_eq_right leftNonempty, ite_eq_left (choiceR rfl)]
      · simpa [Tree.erase, Tree.extractMin, notLeft, notRight] using keptLeft
      · intro n h
        simp [h]
    | node bl y br =>
      have rightNonempty : row.right ≠ endIndex := pending.rightLayout.root_key.1
      have enough : (Tree.node bl y br).height < Cpp.fuel := by
        have room := pending.rightLayout.capacity
        have height := (Tree.node bl y br).height_le_size
        unfold Cpp.fuel
        omega
      obtain ⟨first, child, interim, successor, replacement, newRight, middle, detachRun, detachCost,
        extracted, firstInside, firstNonempty, firstKey, firstNotRight, childLayout, detachFrame, partitions⟩ :=
        generated_detach_layout (Tree.node bl y br) releasedArena row.right rs keptRight (by simp)
          (by rwa [releaseSize]) Cpp.fuel (start + 5) enough
      have insideRight : first.toNat ∈ rs := (partitions _).mpr (Or.inl rfl)
      have apart : List.Disjoint ls newRight := fun {_} l r =>
        pending.disjoint l ((partitions _).mpr (Or.inr r))
      have finalLeft := detachFrame.layout keptLeft apart
      have survivorFits : interim.slots.size ≤ 2 ^ 63 := by rwa [detachFrame.size, releaseSize]
      let linked := replaceRootLinks interim first row.left child
      obtain ⟨updated, linkFrame⟩ := replaceRoot_layout interim first row.left child (.node al x ar) replacement
        successor ls newRight firstInside firstNonempty firstKey finalLeft childLayout
        (fun h => pending.disjoint h insideRight) firstNotRight apart survivorFits
      let beforeBalance := first.toNat :: (ls ++ newRight)
      have linkSize : linked.slots.size = interim.slots.size := linkFrame.size
      obtain ⟨root, next, occupied, stop, balanceRun, balanceCost, layout, balanceFrame, equivalent⟩ :=
        generated_rebalance_layout linked first (.node al x ar) replacement successor ls newRight updated
          (by rwa [linkSize]) middle
      have detachKeepsFree : FreeChain interim.slots interim.free_head (i.toNat :: free) :=
        detachFrame.free_chain nextFree (by
          intro n vacant changed
          have live : n ∈ rs := (partitions _).mpr (Or.inr changed)
          exact keptRight.disjoint_free nextFree live vacant)
      have linkKeepsFree : FreeChain linked.slots linked.free_head (i.toNat :: free) :=
        linkFrame.free_chain detachKeepsFree (by
          intro n vacant changed
          cases List.mem_singleton.mp changed
          have missing := detachKeepsFree.empty_key first vacant
          rw [firstKey] at missing
          contradiction)
      have afterFree : FreeChain next.slots next.free_head (i.toNat :: free) :=
        balanceFrame.free_chain linkKeepsFree (updated.disjoint_free linkKeepsFree)
      have changedScope : beforeBalance ⊆ i.toNat :: (ls ++ rs) := by
        intro n h
        rcases List.mem_cons.mp h with rfl | childMember
        · simp [insideRight]
        · rcases List.mem_append.mp childMember with l | r
          · simp [l]
          · have h := (partitions _).mpr (Or.inr r)
            simp [h]
      have kept := ((releaseWide.trans detachFrame.retained (fun _ h => h) (by
        intro n h
        have h := (partitions _).mpr (Or.inr h)
        simp [h])).trans linkFrame.retained (fun _ h => h) (by
        intro n h
        cases List.mem_singleton.mp h
        simp [insideRight])).trans balanceFrame.retained (fun _ h => h) changedScope
      refine ⟨root, next, occupied, i.toNat :: free, stop, ?_, ?_, ?_,
        afterFree, kept, by rw [balanceFrame.size, linkSize, detachFrame.size, releaseSize],
        fun _ h => changedScope ((equivalent _).mp h)⟩
      · rw [runChoice, ite_eq_right leftNonempty, ite_eq_right rightNonempty]
        have detached : (cp.TreeSet.detach_first releasedArena row.right).run (start + 5) =
            some (((first, child), interim), middle) := detachRun
        change (do
          let p ← (cp.TreeSet.detach_first releasedArena row.right).run (start + 5)
          (cp.TreeSet.rebalance (replaceRootLinks p.1.2 p.1.1.1 row.left p.1.1.2) p.1.1.1).run p.2) = _
        simp only [detached, some_bind]
        exact balanceRun
      · change stop ≤ start + 6 + 57 * (max (Tree.node al x ar).height (Tree.node bl y br).height + 1)
        omega
      · simpa only [Tree.erase, ite_eq_right notLeft, ite_eq_right notRight, extracted] using layout


private theorem pending_erase_left {K : Type} [Inhabited K] {arena next : cp.TreeSet K} {i : UInt64}
    {left replacement right : Tree K} {key : K} {ls rs out : List Nat} {child : UInt64}
    (pending : Pending arena i left key right ls rs)
    (changed : Retained arena next ls) (replaced : Layout next.slots child replacement out)
    (kept : out ⊆ ls) (fits : next.slots.size ≤ 2 ^ 63) :
    Pending (linkLeft next i child) i replacement key right out rs := by
  have inside := lt_of_lt_of_le pending.allocated changed.size
  have original := changed.outside i pending.allocated pending.leftApart
  have written := linkLeft_preserves next i child inside fits
  have right := changed.layout pending.rightLayout (fun {_} hr hl => pending.disjoint hl hr)
  rw [← original] at right
  have outside : i.toNat ∉ out := fun found => pending.leftApart (kept found)
  refine ⟨by simpa using inside, pending.nonnull, ?_, ?_, ?_, outside, pending.rightApart,
    fun {_} hl hr => pending.disjoint (kept hl) hr⟩
  · rw [written, original]
    exact pending.value
  · rw [written]
    exact replaced.putCell_away i _ inside fits outside
  · rw [written]
    exact right.putCell_away i _ inside fits pending.rightApart

private theorem pending_erase_right {K : Type} [Inhabited K] {arena next : cp.TreeSet K} {i : UInt64}
    {left right replacement : Tree K} {key : K} {ls rs out : List Nat} {child : UInt64}
    (pending : Pending arena i left key right ls rs)
    (changed : Retained arena next rs) (replaced : Layout next.slots child replacement out)
    (kept : out ⊆ rs) (fits : next.slots.size ≤ 2 ^ 63) :
    Pending (linkRight next i child) i left key replacement ls out := by
  have inside := lt_of_lt_of_le pending.allocated changed.size
  have original := changed.outside i pending.allocated pending.rightApart
  have written := linkRight_preserves next i child inside fits
  have left := changed.layout pending.leftLayout pending.disjoint
  rw [← original] at left
  have outside : i.toNat ∉ out := fun found => pending.rightApart (kept found)
  refine ⟨by simpa using inside, pending.nonnull, ?_, ?_, ?_, pending.leftApart, outside,
    fun {_} hl hr => pending.disjoint hl (kept hr)⟩
  · rw [written, original]
    exact pending.value
  · rw [written]
    exact left.putCell_away i _ inside fits pending.leftApart
  · rw [written]
    exact replaced.putCell_away i _ inside fits outside


theorem generated_erase_layout {K : Type} [Inhabited K] [LinearOrder K]
    (key : K) (tree : Tree K) (arena : cp.TreeSet K) (i : UInt64) (used free : List Nat)
    (layout : Layout arena.slots i tree used) (available : FreeChain arena.slots arena.free_head free)
    (fits : arena.slots.size ≤ 2 ^ 63) (fuel start : Nat) (enough : tree.height < fuel) :
    ∃ root next occupied remaining stop,
      (cp.TreeSet.erase_rec fuel arena i key).run start = some ((root, next), stop) ∧
      stop ≤ start + 6 + 57 * tree.height ∧
      Layout next.slots root (tree.erase key) occupied ∧
      FreeChain next.slots next.free_head remaining ∧
      Retained arena next used ∧ next.slots.size = arena.slots.size ∧ occupied ⊆ used := by
  induction tree generalizing arena i used free fuel start with
  | empty =>
    cases fuel with
    | zero => simp [Tree.height] at enough
    | succ fuel =>
      cases layout
      exact ⟨endIndex, arena, [], free, start + 3, generated_erase_empty_run fuel arena key start,
        by simp [Tree.height], .empty, available, ⟨rfl, le_rfl, fun _ _ _ => rfl⟩, rfl, fun _ h => h⟩
  | node left current right il ir =>
    cases fuel with
    | zero => simp [Tree.height] at enough
    | succ fuel =>
      obtain ⟨ls, rs, usedEq, pending⟩ := layout_pending layout
      let row := cell arena.slots i
      have childFuelL : left.height < fuel := by simp only [Tree.height] at enough; omega
      have childFuelR : right.height < fuel := by simp only [Tree.height] at enough; omega
      by_cases goLeft : key < current
      · obtain ⟨child, interim, newLeft, remaining, middle, childRun, childCost, childLayout,
          freeInterim, childFrame, childSize, childScope⟩ :=
          il arena row.left ls free pending.leftLayout available fits fuel (start + 2) childFuelL
        have interimFits : interim.slots.size ≤ 2 ^ 63 := by rwa [childSize]
        let linked := linkLeft interim i child
        let touched := i.toNat :: (newLeft ++ rs)
        have modified := pending_erase_left pending childFrame childLayout childScope interimFits
        obtain ⟨root, next, occupied, stop, balanceRun, balanceCost, updated, balanceFrame, equivalent⟩ :=
          generated_rebalance_layout linked i (left.erase key) right current newLeft rs modified
            (by simpa [linked] using interimFits) middle
        have inside : i.toNat < interim.slots.size := lt_of_lt_of_le pending.allocated childFrame.size
        have linkFrame : ChangedWithin interim linked touched :=
          putCell_changedWithin _ _ _ inside interimFits (by simp [touched])
        have oldKey : (cell interim.slots i).key = some current := by
          rw [childFrame.outside i pending.allocated pending.leftApart]
          exact pending.value
        have rootNotFree : i.toNat ∉ remaining := by
          intro vacant
          have missing := freeInterim.empty_key i vacant
          rw [oldKey] at missing
          contradiction
        have linkFree : FreeChain linked.slots linked.free_head remaining :=
          freeInterim.putCell_away i _ inside interimFits rootNotFree
        have afterFree : FreeChain next.slots next.free_head remaining :=
          balanceFrame.free_chain linkFree (modified.disjoint_free linkFree)
        have afterSize : next.slots.size = arena.slots.size := balanceFrame.size.trans
          ((linkLeft_size ..).trans childSize)
        have touchedScope : touched ⊆ used := by
          intro n member
          rcases List.mem_cons.mp member with rfl | below
          · simp [usedEq]
          · rcases List.mem_append.mp below with onLeft | onRight
            · have := childScope onLeft
              simp [usedEq, this]
            · simp [usedEq, onRight]
        have finalFrame := (childFrame.trans linkFrame.retained (by intro n h; simp [usedEq, h]) touchedScope).trans
          balanceFrame.retained (fun _ h => h) touchedScope
        refine ⟨root, next, occupied, remaining, stop, ?_, ?_, ?_, afterFree, finalFrame, afterSize,
          fun {_} n => touchedScope ((equivalent _).mp n)⟩
        · rw [erase_narrow_run fuel arena i key current start pending.nonnull pending.value (.inl goLeft)
            (fun h => not_lt_of_gt h), ite_eq_left goLeft]
          change (do
            let p ← (cp.TreeSet.erase_rec fuel arena row.left key).run (start + 2)
            (cp.TreeSet.rebalance (linkLeft p.1.2 i p.1.1) i).run p.2) = _
          simp only [childRun, some_bind]
          exact balanceRun
        · simp only [Tree.height]
          omega
        · simpa only [Tree.erase, ite_eq_left goLeft] using updated
      · by_cases goRight : current < key
        · obtain ⟨child, interim, newRight, remaining, middle, childRun, childCost, childLayout,
            freeInterim, childFrame, childSize, childScope⟩ :=
            ir arena row.right rs free pending.rightLayout available fits fuel (start + 2) childFuelR
          have interimFits : interim.slots.size ≤ 2 ^ 63 := by rwa [childSize]
          let linked := linkRight interim i child
          let touched := i.toNat :: (ls ++ newRight)
          have modified := pending_erase_right pending childFrame childLayout childScope interimFits
          obtain ⟨root, next, occupied, stop, balanceRun, balanceCost, updated, balanceFrame, equivalent⟩ :=
            generated_rebalance_layout linked i left (right.erase key) current ls newRight modified
              (by simpa [linked] using interimFits) middle
          have inside : i.toNat < interim.slots.size := lt_of_lt_of_le pending.allocated childFrame.size
          have linkFrame : ChangedWithin interim linked touched :=
            putCell_changedWithin _ _ _ inside interimFits (by simp [touched])
          have oldKey : (cell interim.slots i).key = some current := by
            rw [childFrame.outside i pending.allocated pending.rightApart]
            exact pending.value
          have rootNotFree : i.toNat ∉ remaining := by
            intro vacant
            have missing := freeInterim.empty_key i vacant
            rw [oldKey] at missing
            contradiction
          have linkFree : FreeChain linked.slots linked.free_head remaining :=
            freeInterim.putCell_away i _ inside interimFits rootNotFree
          have afterFree : FreeChain next.slots next.free_head remaining :=
            balanceFrame.free_chain linkFree (modified.disjoint_free linkFree)
          have afterSize : next.slots.size = arena.slots.size := balanceFrame.size.trans
            ((linkRight_size ..).trans childSize)
          have touchedScope : touched ⊆ used := by
            intro n member
            rcases List.mem_cons.mp member with rfl | below
            · simp [usedEq]
            · rcases List.mem_append.mp below with onLeft | onRight
              · simp [usedEq, onLeft]
              · have := childScope onRight
                simp [usedEq, this]
          have finalFrame := (childFrame.trans linkFrame.retained (by intro n h; simp [usedEq, h]) touchedScope).trans
            balanceFrame.retained (fun _ h => h) touchedScope
          refine ⟨root, next, occupied, remaining, stop, ?_, ?_, ?_, afterFree, finalFrame, afterSize,
            fun {_} n => touchedScope ((equivalent _).mp n)⟩
          · rw [erase_narrow_run fuel arena i key current start pending.nonnull pending.value (.inr goRight)
              (fun h => not_lt_of_gt h), ite_eq_right goLeft]
            change (do
              let p ← (cp.TreeSet.erase_rec fuel arena row.right key).run (start + 2)
              (cp.TreeSet.rebalance (linkRight p.1.2 i p.1.1) i).run p.2) = _
            simp only [childRun, some_bind]
            exact balanceRun
          · simp only [Tree.height]
            omega
          · simpa only [Tree.erase, ite_eq_right goLeft, ite_eq_left goRight] using updated
        · rw [usedEq]
          exact generated_erase_matching fuel arena i left right key current ls rs free pending
            available fits goLeft goRight start


private theorem generated_remove_program {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (key : K) :
    cp.TreeSet.remove arena key = (do
      Cpp.tick
      let result ← cp.TreeSet.erase arena arena.root key
      return { result.2 with root := result.1 }) := by
  cases arena
  rfl

private theorem generated_remove_run {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (key : K) (start stop : Nat) (index : UInt64) (next : cp.TreeSet K)
    (run : (cp.TreeSet.erase arena arena.root key).run (start + 1) =
      some ((index, next), stop)) :
    (cp.TreeSet.remove arena key).run start = some ({ next with root := index }, stop) := by
  rw [generated_remove_program]
  simp only [StateT.run_bind, tick_run, some_bind, run, pure_run]

theorem generated_remove_spec {K : Type} [Inhabited K] [LinearOrder K]
    (arena : cp.TreeSet K) (tree : Tree K) (key : K) (used free : List Nat)
    (layout : Layout arena.slots arena.root tree used) (available : FreeChain arena.slots arena.free_head free)
    (balanced : tree.Balanced) (ordered : tree.Ordered) (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    ∃ next occupied remaining stop, (cp.TreeSet.remove arena key).run start = some (next, stop) ∧
      stop ≤ start + 7 + 57 * (2 * (tree.size + 1).log2 + 1) ∧
      Layout next.slots next.root (tree.erase key) occupied ∧
      FreeChain next.slots next.free_head remaining ∧ next.slots.size = arena.slots.size ∧
      (tree.erase key).Balanced ∧ (tree.erase key).Ordered ∧
      (tree.erase key).keys = tree.keys.filter (fun k => decide (k ≠ key)) := by
  have capacity := layout.capacity
  have height := tree.height_le_size
  have enough : tree.height < Cpp.fuel := by unfold Cpp.fuel; omega
  obtain ⟨root, next, occupied, remaining, stop, run, cost, placed, vacant, retained, size, scope⟩ :=
    generated_erase_layout key tree arena arena.root used free layout available fits Cpp.fuel (start + 1) enough
  have orderedAfter := tree.erase_ordered key ordered balanced
  have bound := tree.height_logarithmic balanced
  let updated := { next with root := root }
  refine ⟨updated, occupied, remaining, stop, ?_, by omega, placed, vacant, size,
    (tree.erase_balanced key balanced).1, orderedAfter.2, orderedAfter.1⟩
  apply generated_remove_run
  exact run

end Proofs.Cpp.TreeSet
