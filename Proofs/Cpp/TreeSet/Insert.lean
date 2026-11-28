import Proofs.Cpp.TreeSet.Storage
import Proofs.Cpp.TreeSet.Order

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeSet

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

private theorem generated_insert_empty_run {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (fuel : Nat) (arena : cp.TreeSet K) (key : K) (start : Nat) :
    (cp.TreeSet.insert_rec (fuel + 1) arena endIndex key).run start =
      (cp.TreeSet.allocate arena key).run (start + 2) := by
  rcases arena with ⟨slots, root, free⟩
  simp only [cp.TreeSet.insert_rec, StateT.run_bind, tick_run, sentinel_run, some_bind, decide_true,
    ite_true, pure_run, restore_result]

private theorem insert_choice_run {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (fuel : Nat) (arena : cp.TreeSet K) (i : UInt64) (key current : K) (start : Nat)
    (nonnull : i ≠ endIndex) (value : (cell arena.slots i).key = some current) :
    let row := cell arena.slots i
    (cp.TreeSet.insert_rec (fuel + 1) arena i key).run start =
      if key < current then (do
        let p ← (cp.TreeSet.insert_rec fuel arena row.left key).run (start + 2)
        (cp.TreeSet.rebalance (linkLeft p.1.2 i p.1.1) i).run p.2)
      else if current < key then (do
        let p ← (cp.TreeSet.insert_rec fuel arena row.right key).run (start + 2)
        (cp.TreeSet.rebalance (linkRight p.1.2 i p.1.1) i).run p.2)
      else some ((i, arena), start + 2) := by
  rcases arena with ⟨slots, root, free⟩
  change (Cpp.get slots (slotOffset i)).key = some current at value
  simp only [slotOffset] at value
  by_cases lo : key < current <;> by_cases hi : current < key <;>
    simp only [cp.TreeSet.insert_rec, StateT.run_bind, tick_run, sentinel_run, some_bind, nonnull,
      decide_false, Bool.false_eq_true, ite_false, Cpp.optionalValue, value, pure_run, lo, hi,
      decide_true, ite_true, restore_result, linkLeft, linkRight, cell, putCell, slotOffset]

theorem pending_relink_left {K : Type} [Inhabited K] {arena next : cp.TreeSet K} {i : UInt64}
    {left replacement right : Tree K} {key : K} {ls rs out : List Nat} {child : UInt64}
    (pending : Pending arena i left key right ls rs)
    (changed : Retained arena next out) (replaced : Layout next.slots child replacement out)
    (noRoot : i.toNat ∉ out) (apart : List.Disjoint out rs) (fits : next.slots.size ≤ 2 ^ 63) :
    Pending (linkLeft next i child) i replacement key right out rs := by
  have inside := lt_of_lt_of_le pending.allocated changed.size
  have original := changed.outside i pending.allocated noRoot
  have written := linkLeft_preserves next i child inside fits
  have right := changed.layout pending.rightLayout (fun {_} hr hl => apart hl hr)
  rw [← original] at right
  refine ⟨by simpa using inside, pending.nonnull, ?_, ?_, ?_, noRoot, pending.rightApart, apart⟩
  · rw [written, original]
    exact pending.value
  · rw [written]
    exact replaced.putCell_away i _ inside fits noRoot
  · rw [written]
    exact right.putCell_away i _ inside fits pending.rightApart

theorem pending_relink_right {K : Type} [Inhabited K] {arena next : cp.TreeSet K} {i : UInt64}
    {left right replacement : Tree K} {key : K} {ls rs out : List Nat} {child : UInt64}
    (pending : Pending arena i left key right ls rs)
    (changed : Retained arena next out) (replaced : Layout next.slots child replacement out)
    (noRoot : i.toNat ∉ out) (apart : List.Disjoint ls out) (fits : next.slots.size ≤ 2 ^ 63) :
    Pending (linkRight next i child) i left key replacement ls out := by
  have inside := lt_of_lt_of_le pending.allocated changed.size
  have original := changed.outside i pending.allocated noRoot
  have written := linkRight_preserves next i child inside fits
  have left := changed.layout pending.leftLayout apart
  rw [← original] at left
  refine ⟨by simpa using inside, pending.nonnull, ?_, ?_, ?_, pending.leftApart, noRoot, apart⟩
  · rw [written, original]
    exact pending.value
  · rw [written]
    exact left.putCell_away i _ inside fits pending.leftApart
  · rw [written]
    exact replaced.putCell_away i _ inside fits noRoot

theorem Retained.congr_mem {K : Type} [Inhabited K] {a b : cp.TreeSet K} {used out : List Nat}
    (frame : Retained a b used) (covers : used ⊆ out) : Retained a b out :=
  ⟨frame.root, frame.size, fun j allocated outside =>
    frame.outside j allocated (fun inside => outside (covers inside))⟩


theorem generated_insert_layout {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (key : K) (tree : Tree K) (arena : cp.TreeSet K) (i : UInt64) (used free : List Nat)
    (layout : Layout arena.slots i tree used) (available : FreeChain arena.slots arena.free_head free)
    (fits : arena.slots.size < 2 ^ 63) (fuel start : Nat) (enough : tree.height < fuel) :
    ∃ root next occupied remaining stop,
      (cp.TreeSet.insert_rec fuel arena i key).run start = some ((root, next), stop) ∧
      stop ≤ start + 8 + 57 * tree.height ∧ next.slots.size ≤ 2 ^ 63 ∧
      Layout next.slots root (tree.insert key) occupied ∧
      FreeChain next.slots next.free_head remaining ∧
      Retained arena next occupied ∧
      (∀ n ∈ occupied, n ∈ used ∨ n ∈ free ∨ n = arena.slots.size) ∧
      (next.slots.size = arena.slots.size ∨ next.slots.size = arena.slots.size + 1) := by
  induction tree generalizing arena i used free fuel start with
  | empty =>
    cases fuel with
    | zero => simp [Tree.height] at enough
    | succ fuel =>
      cases layout
      obtain ⟨root, next, remaining, stop, run, cost, nextFits, built, chain, frame, place, growth⟩ :=
        generated_allocate_layout arena key free available fits (start + 2)
      refine ⟨root, next, [root.toNat], remaining, stop, ?_, by simp only [Tree.height]; omega,
        nextFits, built, chain, frame, ?_, ?_⟩
      · exact (generated_insert_empty_run fuel arena key start).trans run
      · intro n member
        have same : n = root.toNat := List.mem_singleton.mp member
        subst n
        exact place.elim (fun h => Or.inr (Or.inr h)) (fun h => Or.inr (Or.inl h))
      · cases free <;> simp_all
  | node left current right il ir =>
    cases fuel with
    | zero => simp [Tree.height] at enough
    | succ fuel =>
      obtain ⟨ls, rs, usedEq, pending⟩ := layout_pending layout
      let row := cell arena.slots i
      have rowValue : (cell arena.slots i).key = some current := pending.value
      have nonnull := pending.nonnull
      have notFree := layout.disjoint_free available
      have childFuelL : left.height < fuel := by simp only [Tree.height] at enough; omega
      have childFuelR : right.height < fuel := by simp only [Tree.height] at enough; omega
      by_cases goLeft : key < current
      · obtain ⟨child, interim, newLeft, remaining, middle, childRun, childCost, interimFits,
          childLayout, freeInterim, childFrame, childScope, growth⟩ :=
          il arena row.left ls free pending.leftLayout available fits fuel (start + 2) childFuelL
        have protects {n : Nat} (inOld : n ∈ used) (outside : n ∉ ls) : n ∉ newLeft := by
          intro present
          rcases childScope n present with found | fresh | last
          · exact outside found
          · exact notFree inOld fresh
          · have inside := layout.in_range n inOld
            omega
        have noRoot : i.toNat ∉ newLeft :=
          protects (by simp [usedEq]) pending.leftApart
        have apart : List.Disjoint newLeft rs := by
          intro n onLeft onRight
          exact protects (by simp [usedEq, onRight]) (fun present => pending.disjoint present onRight) onLeft
        let linked := linkLeft interim i child
        let touched := i.toNat :: (newLeft ++ rs)
        have modified := pending_relink_left pending childFrame childLayout noRoot apart interimFits
        obtain ⟨root, next, occupied, stop, balanceRun, balanceCost, updated, balanceFrame, equivalent⟩ :=
          generated_rebalance_layout linked i (left.insert key) right current newLeft rs modified
            (by simpa [linked] using interimFits) middle
        have inside : i.toNat < interim.slots.size := lt_of_lt_of_le pending.allocated childFrame.size
        have linkFrame : ChangedWithin interim linked touched :=
          putCell_changedWithin _ _ _ inside interimFits (by simp [touched])
        have oldKey : (cell interim.slots i).key = some current := by
          rw [childFrame.outside i pending.allocated noRoot]
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
        have afterSize : next.slots.size = interim.slots.size := balanceFrame.size.trans (linkLeft_size ..)
        have inTouched : newLeft ⊆ touched := by intro n h; simp [touched, h]
        have finalFrame := (childFrame.trans linkFrame.retained inTouched (fun _ h => h)).trans
          balanceFrame.retained (fun _ h => h) (fun _ h => h)
        refine ⟨root, next, occupied, remaining, stop, ?_, ?_, by rwa [afterSize], ?_,
          afterFree, finalFrame.congr_mem (fun n h => (equivalent n).mpr h), ?_, by rwa [afterSize]⟩
        · rw [insert_choice_run fuel arena i key current start nonnull rowValue, ite_eq_left goLeft]
          change (do
            let p ← (cp.TreeSet.insert_rec fuel arena row.left key).run (start + 2)
            (cp.TreeSet.rebalance (linkLeft p.1.2 i p.1.1) i).run p.2) = _
          simp only [childRun, some_bind]
          exact balanceRun
        · simp only [Tree.height]
          omega
        · simpa only [Tree.insert, ite_eq_left goLeft] using updated
        · intro n member
          rcases List.mem_cons.mp ((equivalent n).mp member) with rfl | below
          · exact Or.inl (by simp [usedEq])
          · rcases List.mem_append.mp below with found | rightMember
            · rcases childScope n found with original | vacant | appended
              · exact Or.inl (by simp [usedEq, original])
              · exact Or.inr (Or.inl vacant)
              · exact Or.inr (Or.inr appended)
            · exact Or.inl (by simp [usedEq, rightMember])
      · by_cases goRight : current < key
        · obtain ⟨child, interim, newRight, remaining, middle, childRun, childCost, interimFits,
            childLayout, freeInterim, childFrame, childScope, growth⟩ :=
            ir arena row.right rs free pending.rightLayout available fits fuel (start + 2) childFuelR
          have protects {n : Nat} (inOld : n ∈ used) (outside : n ∉ rs) : n ∉ newRight := by
            intro present
            rcases childScope n present with found | fresh | last
            · exact outside found
            · exact notFree inOld fresh
            · have inside := layout.in_range n inOld
              omega
          have noRoot : i.toNat ∉ newRight :=
            protects (by simp [usedEq]) pending.rightApart
          have apart : List.Disjoint ls newRight := by
            intro n onLeft onRight
            exact protects (by simp [usedEq, onLeft]) (fun present => pending.disjoint onLeft present) onRight
          let linked := linkRight interim i child
          let touched := i.toNat :: (ls ++ newRight)
          have modified := pending_relink_right pending childFrame childLayout noRoot apart interimFits
          obtain ⟨root, next, occupied, stop, balanceRun, balanceCost, updated, balanceFrame, equivalent⟩ :=
            generated_rebalance_layout linked i left (right.insert key) current ls newRight modified
              (by simpa [linked] using interimFits) middle
          have inside : i.toNat < interim.slots.size := lt_of_lt_of_le pending.allocated childFrame.size
          have linkFrame : ChangedWithin interim linked touched :=
            putCell_changedWithin _ _ _ inside interimFits (by simp [touched])
          have oldKey : (cell interim.slots i).key = some current := by
            rw [childFrame.outside i pending.allocated noRoot]
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
          have afterSize : next.slots.size = interim.slots.size := balanceFrame.size.trans (linkRight_size ..)
          have inTouched : newRight ⊆ touched := by intro n h; simp [touched, h]
          have finalFrame := (childFrame.trans linkFrame.retained inTouched (fun _ h => h)).trans
            balanceFrame.retained (fun _ h => h) (fun _ h => h)
          refine ⟨root, next, occupied, remaining, stop, ?_, ?_, by rwa [afterSize], ?_,
            afterFree, finalFrame.congr_mem (fun n h => (equivalent n).mpr h), ?_, by rwa [afterSize]⟩
          · rw [insert_choice_run fuel arena i key current start nonnull rowValue, ite_eq_right goLeft, ite_eq_left goRight]
            change (do
              let p ← (cp.TreeSet.insert_rec fuel arena row.right key).run (start + 2)
              (cp.TreeSet.rebalance (linkRight p.1.2 i p.1.1) i).run p.2) = _
            simp only [childRun, some_bind]
            exact balanceRun
          · simp only [Tree.height]
            omega
          · simpa only [Tree.insert, ite_eq_right goLeft, ite_eq_left goRight] using updated
          · intro n member
            rcases List.mem_cons.mp ((equivalent n).mp member) with rfl | below
            · exact Or.inl (by simp [usedEq])
            · rcases List.mem_append.mp below with leftMember | found
              · exact Or.inl (by simp [usedEq, leftMember])
              · rcases childScope n found with original | vacant | appended
                · exact Or.inl (by simp [usedEq, original])
                · exact Or.inr (Or.inl vacant)
                · exact Or.inr (Or.inr appended)
        · refine ⟨i, arena, used, free, start + 2, ?_, by omega, by omega, ?_, available,
            ⟨rfl, le_rfl, fun _ _ _ => rfl⟩, (fun _ member => Or.inl member), Or.inl rfl⟩
          · rw [insert_choice_run fuel arena i key current start nonnull rowValue, ite_eq_right goLeft,
              ite_eq_right goRight]
          · simpa only [Tree.insert, ite_eq_right goLeft, ite_eq_right goRight] using layout


private theorem generated_add_program {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (key : K) :
    cp.TreeSet.add arena key = (do
      Cpp.tick
      let result ← cp.TreeSet.insert arena arena.root key
      return { result.2 with root := result.1 }) := by
  cases arena
  rfl

private theorem generated_add_run {K : Type} [Inhabited K] [LT K] [DecidableLT K]
    (arena : cp.TreeSet K) (key : K) (start stop : Nat) (index : UInt64) (next : cp.TreeSet K)
    (run : (cp.TreeSet.insert arena arena.root key).run (start + 1) =
      some ((index, next), stop)) :
    (cp.TreeSet.add arena key).run start = some ({ next with root := index }, stop) := by
  rw [generated_add_program]
  simp only [StateT.run_bind, tick_run, some_bind, run, pure_run]

theorem generated_add_spec {K : Type} [Inhabited K] [LinearOrder K]
    (arena : cp.TreeSet K) (tree : Tree K) (key : K) (used free : List Nat)
    (layout : Layout arena.slots arena.root tree used) (available : FreeChain arena.slots arena.free_head free)
    (balanced : tree.Balanced) (ordered : tree.Ordered) (fits : arena.slots.size < 2 ^ 63) (start : Nat) :
    ∃ next occupied remaining stop, (cp.TreeSet.add arena key).run start = some (next, stop) ∧
      stop ≤ start + 9 + 57 * (2 * (tree.size + 1).log2 + 1) ∧
      Layout next.slots next.root (tree.insert key) occupied ∧
      FreeChain next.slots next.free_head remaining ∧ next.slots.size ≤ arena.slots.size + 1 ∧
      (tree.insert key).Balanced ∧ (tree.insert key).Ordered ∧
      (∀ k, k ∈ (tree.insert key).keys ↔ k = key ∨ k ∈ tree.keys) := by
  have capacity := layout.capacity
  have height := tree.height_le_size
  have enough : tree.height < Cpp.fuel := by unfold Cpp.fuel; omega
  obtain ⟨root, next, occupied, remaining, stop, run, cost, nextFits, placed, vacant, kept, source, growth⟩ :=
    generated_insert_layout key tree arena arena.root used free layout available fits Cpp.fuel (start + 1) enough
  have orderedAfter := tree.insert_ordered key ordered
  have bound := tree.height_logarithmic balanced
  let updated := { next with root := root }
  refine ⟨updated, occupied, remaining, stop, ?_, by omega, placed, vacant, ?_,
    (tree.insert_balanced key balanced).1, orderedAfter.1, ?_⟩
  · apply generated_add_run
    exact run
  · change next.slots.size ≤ arena.slots.size + 1
    rcases growth with same | grew <;> omega
  · exact orderedAfter.2

end Proofs.Cpp.TreeSet
