import Proofs.Cpp.TreeSet.Rotate

open Proofs Proofs.Cpp Proofs.Cpp.Gen

namespace Proofs.Cpp.TreeSet

def rebalanceLeft {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64) :
    Cpp.M (UInt64 × cp.TreeSet K) := do
  let left := (cell arena.slots i).left
  let outer ← cp.TreeSet.subtree_height arena (cell arena.slots left).left
  let inner ← cp.TreeSet.subtree_height arena (cell arena.slots left).right
  let adjusted ← if decide (outer < inner) then do
    let rotation ← cp.TreeSet.rotate_left arena left
    pure (linkLeft rotation.2 i rotation.1)
  else pure arena
  cp.TreeSet.rotate_right adjusted i

def rebalanceRight {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64) :
    Cpp.M (UInt64 × cp.TreeSet K) := do
  let right := (cell arena.slots i).right
  let outer ← cp.TreeSet.subtree_height arena (cell arena.slots right).right
  let inner ← cp.TreeSet.subtree_height arena (cell arena.slots right).left
  let adjusted ← if decide (outer < inner) then do
    let rotation ← cp.TreeSet.rotate_right arena right
    pure (linkRight rotation.2 i rotation.1)
  else pure arena
  cp.TreeSet.rotate_left adjusted i

def rebalanceProgram {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64) :
    Cpp.M (UInt64 × cp.TreeSet K) := do
  Cpp.tick
  let a ← cp.TreeSet.subtree_height arena (cell arena.slots i).left
  let b ← cp.TreeSet.subtree_height arena (cell arena.slots i).right
  if decide (b + 1 < a) then rebalanceLeft arena i
  else if decide (a + 1 < b) then rebalanceRight arena i
  else do
    let next ← cp.TreeSet.refresh arena i
    return (i, next)

structure ChangedWithin {K : Type} [Inhabited K] (before after : cp.TreeSet K) (used : List Nat) : Prop where
  root : after.root = before.root
  free : after.free_head = before.free_head
  size : after.slots.size = before.slots.size
  outside : ∀ i, i.toNat < before.slots.size → i.toNat ∉ used → cell after.slots i = cell before.slots i

theorem ChangedWithin.layout {K : Type} [Inhabited K] {a b : cp.TreeSet K}
    {index : UInt64} {tree : Tree K} {used keep : List Nat} (frame : ChangedWithin a b used)
    (layout : Layout a.slots index tree keep) (separate : List.Disjoint keep used) :
    Layout b.slots index tree keep := by
  apply layout.frame
  · simpa [frame.size] using layout.in_range
  · intro i mem
    exact (frame.outside i (layout.in_range _ mem) (separate mem)).symm

theorem ChangedWithin.trans {K : Type} [Inhabited K] {a b c : cp.TreeSet K} {ls rs used : List Nat}
    (first : ChangedWithin a b ls) (second : ChangedWithin b c rs)
    (includesLeft : ls ⊆ used) (includesRight : rs ⊆ used) : ChangedWithin a c used :=
  ⟨second.root.trans first.root, second.free.trans first.free, second.size.trans first.size,
    fun j allocated apart => (second.outside j (by rwa [first.size]) (fun mem => apart (includesRight mem))).trans
      (first.outside j allocated (fun mem => apart (includesLeft mem)))⟩

theorem TwoCells.changedWithin {K : Type} [Inhabited K] {a b : cp.TreeSet K} {i j : UInt64}
    {used : List Nat} (frame : TwoCells a b i j) (hasI : i.toNat ∈ used) (hasJ : j.toNat ∈ used) :
    ChangedWithin a b used :=
  ⟨frame.root, frame.free, frame.size, fun k allocated apart =>
    frame.outside k allocated (fun eq => apart (eq.symm ▸ hasI)) (fun eq => apart (eq.symm ▸ hasJ))⟩

theorem putCell_changedWithin {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64)
    (row : cp.TreeSet_Slot K) (inside : i.toNat < arena.slots.size) (fits : arena.slots.size ≤ 2 ^ 63)
    {used : List Nat} (written : i.toNat ∈ used) : ChangedWithin arena (putCell arena i row) used :=
  (TwoCells.putFirst arena i i row inside fits).changedWithin written written


private theorem heightGuard {K : Type} [Inhabited K] {arena : cp.TreeSet K}
    {i j : UInt64} {left right : Tree K} {ls rs : List Nat}
    (l : Layout arena.slots i left ls) (r : Layout arena.slots j right rs)
    (fits : arena.slots.size ≤ 2 ^ 63) :
    modelHeight arena i + 1 < modelHeight arena j ↔ left.height + 1 < right.height := by
  have capacity := l.capacity
  have heightBound := left.height_le_size
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, l.model_height, r.model_height]
  change (left.height + 1) % (2 ^ 64) < right.height ↔ left.height + 1 < right.height
  rw [Nat.mod_eq_of_lt (by omega)]

private theorem tick_run (clock : Nat) : Cpp.tick.run clock = some ((), clock + 1) := rfl

private theorem some_bind {A B : Type} (value : A) (next : A → Option B) :
    (some value >>= next) = next value := rfl

private theorem restore_rotation {K : Type} (source : Option ((UInt64 × cp.TreeSet K) × Nat)) :
    (source >>= fun p => some ((p.1.1, ⟨p.1.2.slots, p.1.2.root, p.1.2.free_head⟩), p.2)) =
      source := by cases source <;> rfl

private theorem pure_run {A : Type} (value : A) (clock : Nat) :
    (pure value : Cpp.M A).run clock = some (value, clock) := rfl

theorem generated_rebalance_program {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64) :
    cp.TreeSet.rebalance arena i = rebalanceProgram arena i := by
  rcases arena with ⟨slots, root, free⟩
  funext start
  change StateT.run _ start = StateT.run _ start
  simp only [cp.TreeSet.rebalance, rebalanceProgram, StateT.run_bind, tick_run, some_bind,
    generated_height_run]
  let arena : cp.TreeSet K := ⟨slots, root, free⟩
  let left := (cell slots i).left
  let right := (cell slots i).right
  by_cases heavyL : modelHeight arena right + 1 < modelHeight arena left
  · by_cases insideGreater :
      modelHeight arena (cell slots left).left < modelHeight arena (cell slots left).right <;>
      simp only [arena, left, right, cell] at heavyL insideGreater <;>
      simp only [rebalanceLeft, StateT.run_bind, some_bind, generated_height_run,
        heavyL, insideGreater, cell, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false,
        pure_run, linkLeft, putCell, slotOffset, restore_rotation]
  · by_cases heavyR : modelHeight arena left + 1 < modelHeight arena right
    · by_cases insideGreater :
        modelHeight arena (cell slots right).right < modelHeight arena (cell slots right).left <;>
        simp only [arena, left, right, cell] at heavyL heavyR insideGreater <;>
        simp only [rebalanceRight, StateT.run_bind, some_bind, generated_height_run,
          heavyL, heavyR, insideGreater, cell, decide_true, decide_false, Bool.false_eq_true, ite_true, ite_false,
          pure_run, linkRight, putCell, slotOffset, restore_rotation]
    · simp only [arena, left, right, cell] at heavyL heavyR
      simp only [StateT.run_bind, some_bind, heavyL, heavyR, cell, decide_false, Bool.false_eq_true, ite_false, pure_run]

theorem generated_rebalance_level {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64)
    (left right : Tree K) (key : K) (ls rs : List Nat)
    (pending : Pending arena i left key right ls rs) (fits : arena.slots.size ≤ 2 ^ 63)
    (lower : ¬right.height + 1 < left.height) (upper : ¬left.height + 1 < right.height) (start : Nat) :
    let next := putCell arena i (refreshRow arena i)
    (cp.TreeSet.rebalance arena i).run start = some ((i, next), start + 16) ∧
    Layout next.slots i (Tree.balance left key right) (i.toNat :: (ls ++ rs)) ∧
    ChangedWithin arena next (i.toNat :: (ls ++ rs)) := by
  let next := putCell arena i (refreshRow arena i)
  have leftGuard : ¬ modelHeight arena (cell arena.slots i).right + 1 <
      modelHeight arena (cell arena.slots i).left := fun h => lower ((heightGuard pending.rightLayout pending.leftLayout fits).mp h)
  have rightGuard : ¬ modelHeight arena (cell arena.slots i).left + 1 <
      modelHeight arena (cell arena.slots i).right := fun h => upper ((heightGuard pending.leftLayout pending.rightLayout fits).mp h)
  have updated := generated_refresh_layout arena i left key right ls rs pending fits (start + 5)
  have run : (cp.TreeSet.refresh arena i).run (start + 5) = some (next, start + 16) := updated.1
  refine ⟨?_, by simpa [Tree.balance, lower, upper] using updated.2, ?_⟩
  · rw [generated_rebalance_program]
    simp only [rebalanceProgram, StateT.run_bind, tick_run, some_bind, generated_height_run,
      leftGuard, rightGuard, decide_false, Bool.false_eq_true, ite_false, pure_run, run]
    rfl
  · exact putCell_changedWithin arena i _ pending.allocated fits (by simp)


theorem generated_rebalance_single_left {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64)
    (a b c : Tree K) (x y : K) (ls rs : List Nat)
    (pending : Pending arena i a x (.node b y c) ls rs) (fits : arena.slots.size ≤ 2 ^ 63)
    (heavy : a.height + 1 < (Tree.node b y c).height) (single : ¬ c.height < b.height) (start : Nat) :
    ∃ root next occupied, (cp.TreeSet.rebalance arena i).run start = some ((root, next), start + 32) ∧
      Layout next.slots root (Tree.balance a x (.node b y c)) occupied ∧
      ChangedWithin arena next (i.toNat :: (ls ++ rs)) ∧
      (∀ k, k ∈ occupied ↔ k ∈ i.toNat :: (ls ++ rs)) := by
  let j := leftPivot arena i
  obtain ⟨bs, cs, rightUsed, child⟩ := layout_pending pending.rightLayout
  change Pending arena j b y c bs cs at child
  change rs = j.toNat :: (bs ++ cs) at rightUsed
  have rightGuard := (heightGuard pending.leftLayout pending.rightLayout fits).mpr heavy
  have leftGuard : ¬ modelHeight arena (cell arena.slots i).right + 1 < modelHeight arena (cell arena.slots i).left := by
    have tooSmall : ¬ (Tree.node b y c).height + 1 < a.height := by omega
    exact fun h => tooSmall ((heightGuard pending.rightLayout pending.leftLayout fits).mp h)
  have innerGuard :
      ¬ modelHeight arena (cell arena.slots (cell arena.slots i).right).right <
        modelHeight arena (cell arena.slots (cell arena.slots i).right).left := by
    change ¬ modelHeight arena (cell arena.slots j).right < modelHeight arena (cell arena.slots j).left
    rwa [UInt64.lt_iff_toNat_lt, child.rightLayout.model_height, child.leftLayout.model_height]
  obtain ⟨next, occupied, run, layout, frame, same⟩ :=
    generated_rotate_left_layout arena i a b c x y ls rs pending fits (start + 9)
  have usedI : i.toNat ∈ i.toNat :: (ls ++ rs) := by simp
  have usedJ : j.toNat ∈ i.toNat :: (ls ++ rs) := by simp [rightUsed]
  refine ⟨j, next, occupied, ?_, ?_, frame.changedWithin usedI usedJ, same⟩
  · rw [generated_rebalance_program]
    simp only [rebalanceProgram, StateT.run_bind, tick_run, some_bind, generated_height_run,
      leftGuard, rightGuard, decide_false, decide_true, Bool.false_eq_true, ite_false, ite_true]
    change (rebalanceRight arena i).run (start + 5) = _
    simp only [rebalanceRight, StateT.run_bind, some_bind, generated_height_run, innerGuard,
      decide_false, Bool.false_eq_true, ite_false, pure_run]
    exact run
  · have notLeft : ¬ (Tree.node b y c).height + 1 < a.height := by omega
    simpa [Tree.balance, Tree.balanceRight, heavy, notLeft, single] using layout

theorem generated_rebalance_single_right {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64)
    (a b c : Tree K) (x y : K) (ls rs : List Nat)
    (pending : Pending arena i (.node c y b) x a ls rs) (fits : arena.slots.size ≤ 2 ^ 63)
    (heavy : a.height + 1 < (Tree.node c y b).height) (single : ¬ c.height < b.height) (start : Nat) :
    ∃ root next occupied, (cp.TreeSet.rebalance arena i).run start = some ((root, next), start + 32) ∧
      Layout next.slots root (Tree.balance (.node c y b) x a) occupied ∧
      ChangedWithin arena next (i.toNat :: (ls ++ rs)) ∧
      (∀ k, k ∈ occupied ↔ k ∈ i.toNat :: (ls ++ rs)) := by
  let j := rightPivot arena i
  obtain ⟨cs, bs, leftUsed, child⟩ := layout_pending pending.leftLayout
  change Pending arena j c y b cs bs at child
  change ls = j.toNat :: (cs ++ bs) at leftUsed
  have leftGuard := (heightGuard pending.rightLayout pending.leftLayout fits).mpr heavy
  have innerGuard :
      ¬ modelHeight arena (cell arena.slots (cell arena.slots i).left).left <
        modelHeight arena (cell arena.slots (cell arena.slots i).left).right := by
    change ¬ modelHeight arena (cell arena.slots j).left < modelHeight arena (cell arena.slots j).right
    rwa [UInt64.lt_iff_toNat_lt, child.leftLayout.model_height, child.rightLayout.model_height]
  obtain ⟨next, occupied, run, layout, frame, same⟩ :=
    generated_rotate_right_layout arena i a b c x y ls rs pending fits (start + 9)
  have usedI : i.toNat ∈ i.toNat :: (ls ++ rs) := by simp
  have usedJ : j.toNat ∈ i.toNat :: (ls ++ rs) := by simp [leftUsed]
  refine ⟨j, next, occupied, ?_, ?_, frame.changedWithin usedI usedJ, same⟩
  · rw [generated_rebalance_program]
    simp only [rebalanceProgram, StateT.run_bind, tick_run, some_bind, generated_height_run,
      leftGuard, decide_true, ite_true]
    change (rebalanceLeft arena i).run (start + 5) = _
    simp only [rebalanceLeft, StateT.run_bind, some_bind, generated_height_run, innerGuard,
      decide_false, Bool.false_eq_true, ite_false, pure_run]
    exact run
  · simpa [Tree.balance, Tree.balanceLeft, heavy, single] using layout


theorem pending_link_left {K : Type} [Inhabited K] {arena next : cp.TreeSet K} {i : UInt64}
    {left replacement right : Tree K} {key : K} {ls rs out : List Nat} {child : UInt64}
    (pending : Pending arena i left key right ls rs)
    (changed : ChangedWithin arena next ls) (replaced : Layout next.slots child replacement out)
    (same : ∀ k, k ∈ out ↔ k ∈ ls) (fits : arena.slots.size ≤ 2 ^ 63) :
    Pending (linkLeft next i child) i replacement key right out rs := by
  have inside : i.toNat < next.slots.size := by rw [changed.size]; exact pending.allocated
  have nextFits : next.slots.size ≤ 2 ^ 63 := by rwa [changed.size]
  have first : cell next.slots i = cell arena.slots i :=
    changed.outside i pending.allocated pending.leftApart
  have written := linkLeft_preserves next i child inside nextFits
  have outApart : i.toNat ∉ out := fun member => pending.leftApart ((same _).mp member)
  have right := changed.layout pending.rightLayout (fun {_} hr hl => pending.disjoint hl hr)
  rw [← first] at right
  refine ⟨by simpa using inside, pending.nonnull, ?_, ?_, ?_, outApart, pending.rightApart, ?_⟩
  · rw [written, first]
    exact pending.value
  · rw [written]
    exact replaced.putCell_away i _ inside nextFits outApart
  · rw [written]
    exact right.putCell_away i _ inside nextFits pending.rightApart
  · intro n lf rt
    exact pending.disjoint ((same n).mp lf) rt

theorem pending_link_right {K : Type} [Inhabited K] {arena next : cp.TreeSet K} {i : UInt64}
    {left right replacement : Tree K} {key : K} {ls rs out : List Nat} {child : UInt64}
    (pending : Pending arena i left key right ls rs)
    (changed : ChangedWithin arena next rs) (replaced : Layout next.slots child replacement out)
    (same : ∀ k, k ∈ out ↔ k ∈ rs) (fits : arena.slots.size ≤ 2 ^ 63) :
    Pending (linkRight next i child) i left key replacement ls out := by
  have inside : i.toNat < next.slots.size := by rw [changed.size]; exact pending.allocated
  have nextFits : next.slots.size ≤ 2 ^ 63 := by rwa [changed.size]
  have first : cell next.slots i = cell arena.slots i :=
    changed.outside i pending.allocated pending.rightApart
  have written := linkRight_preserves next i child inside nextFits
  have outApart : i.toNat ∉ out := fun member => pending.rightApart ((same _).mp member)
  have left := changed.layout pending.leftLayout pending.disjoint
  rw [← first] at left
  refine ⟨by simpa using inside, pending.nonnull, ?_, ?_, ?_, pending.leftApart, outApart, ?_⟩
  · rw [written, first]
    exact pending.value
  · rw [written]
    exact left.putCell_away i _ inside nextFits pending.leftApart
  · rw [written]
    exact replaced.putCell_away i _ inside nextFits outApart
  · intro n lf rt
    exact pending.disjoint lf ((same n).mp rt)


theorem generated_rebalance_double_left {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64)
    (a b c d : Tree K) (x y z : K) (ls rs : List Nat)
    (pending : Pending arena i a x (.node (.node d z b) y c) ls rs) (fits : arena.slots.size ≤ 2 ^ 63)
    (heavy : a.height + 1 < (Tree.node (.node d z b) y c).height)
    (double : c.height < (Tree.node d z b).height) (start : Nat) :
    ∃ root next occupied, (cp.TreeSet.rebalance arena i).run start = some ((root, next), start + 55) ∧
      Layout next.slots root (Tree.balance a x (.node (.node d z b) y c)) occupied ∧
      ChangedWithin arena next (i.toNat :: (ls ++ rs)) ∧
      (∀ k, k ∈ occupied ↔ k ∈ i.toNat :: (ls ++ rs)) := by
  let j := leftPivot arena i
  obtain ⟨ds, cs, rightUsed, child⟩ := layout_pending pending.rightLayout
  change Pending arena j (.node d z b) y c ds cs at child
  change rs = j.toNat :: (ds ++ cs) at rightUsed
  let k := rightPivot arena j
  have hasK : k.toNat ∈ ds := child.leftLayout.index_used.resolve_left child.leftLayout.root_key.1
  have notLeft : ¬ (Tree.node (.node d z b) y c).height + 1 < a.height := by omega
  have leftGuard : ¬ modelHeight arena (cell arena.slots i).right + 1 <
      modelHeight arena (cell arena.slots i).left :=
    fun h => notLeft ((heightGuard pending.rightLayout pending.leftLayout fits).mp h)
  have rightGuard := (heightGuard pending.leftLayout pending.rightLayout fits).mpr heavy
  have innerGuard :
      modelHeight arena (cell arena.slots (cell arena.slots i).right).right <
        modelHeight arena (cell arena.slots (cell arena.slots i).right).left := by
    change modelHeight arena (cell arena.slots j).right < modelHeight arena (cell arena.slots j).left
    rwa [UInt64.lt_iff_toNat_lt, child.rightLayout.model_height, child.leftLayout.model_height]
  obtain ⟨rotated, rotatedUsed, first, updated, firstFrame, sameFirst⟩ :=
    generated_rotate_right_layout arena j c b d y z ds cs child fits (start + 9)
  have partialFrame : ChangedWithin arena rotated rs :=
    firstFrame.changedWithin (by simp [rightUsed]) (show k.toNat ∈ rs by simp [rightUsed, hasK])
  have preserves (n : Nat) : n ∈ rotatedUsed ↔ n ∈ rs := by rw [sameFirst n, rightUsed]
  let linked := linkRight rotated i k
  have adjusted : Pending linked i a x (.node d z (.node b y c)) ls rotatedUsed :=
    pending_link_right pending partialFrame updated preserves fits
  have linkSize : linked.slots.size = arena.slots.size := (linkRight_size ..).trans partialFrame.size
  let target := i.toNat :: (ls ++ rs)
  have frameLink : ChangedWithin rotated linked target :=
    putCell_changedWithin _ _ _ (by rw [partialFrame.size]; exact pending.allocated)
      (by rwa [partialFrame.size]) (by simp [target])
  obtain ⟨next, occupied, second, layout, lastFrame, sameLast⟩ :=
    generated_rotate_left_layout linked i a d (.node b y c) x z ls rotatedUsed adjusted
      (by rwa [linkSize]) (start + 32)
  have childNow : leftPivot linked i = k := by
    have wrote := linkRight_preserves rotated i k (by rw [partialFrame.size]; exact pending.allocated)
      (by rwa [partialFrame.size])
    exact congrArg cp.TreeSet_Slot.right wrote
  have secondRun : (cp.TreeSet.rotate_left linked i).run (start + 32) =
      some ((k, next), start + 55) := by simpa only [childNow] using second
  have allK : k.toNat ∈ target := by simp [target, rightUsed, hasK]
  have lastChanged : ChangedWithin linked next target :=
    lastFrame.changedWithin (by simp [target]) (by rwa [childNow])
  have combined := (partialFrame.trans frameLink (by intro n mem; simp [target, mem]) (fun _ h => h)).trans
    lastChanged (fun _ h => h) (fun _ h => h)
  refine ⟨k, next, occupied, ?_, ?_, combined, ?_⟩
  · rw [generated_rebalance_program]
    simp only [rebalanceProgram, StateT.run_bind, tick_run, some_bind, generated_height_run,
      leftGuard, rightGuard, decide_false, decide_true, Bool.false_eq_true, ite_false, ite_true]
    change (rebalanceRight arena i).run (start + 5) = _
    simp only [rebalanceRight, StateT.run_bind, some_bind, generated_height_run, innerGuard,
      decide_true, ite_true, pure_run]
    change (do
      let p ← (cp.TreeSet.rotate_right arena j).run (start + 9)
      (cp.TreeSet.rotate_left (linkRight p.1.2 i p.1.1) i).run p.2) = _
    have firstRun : (cp.TreeSet.rotate_right arena j).run (start + 9) = some ((k, rotated), start + 32) := first
    simp only [firstRun, some_bind]
    exact secondRun
  · rw [childNow] at layout
    simpa [Tree.balance, Tree.balanceRight, heavy, notLeft, double] using layout
  · intro n
    simp only [sameLast n, List.mem_cons, List.mem_append, preserves n]

theorem generated_rebalance_double_right {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64)
    (a b c d : Tree K) (x y z : K) (ls rs : List Nat)
    (pending : Pending arena i (.node c y (.node b z d)) x a ls rs) (fits : arena.slots.size ≤ 2 ^ 63)
    (heavy : a.height + 1 < (Tree.node c y (.node b z d)).height)
    (double : c.height < (Tree.node b z d).height) (start : Nat) :
    ∃ root next occupied, (cp.TreeSet.rebalance arena i).run start = some ((root, next), start + 55) ∧
      Layout next.slots root (Tree.balance (.node c y (.node b z d)) x a) occupied ∧
      ChangedWithin arena next (i.toNat :: (ls ++ rs)) ∧
      (∀ k, k ∈ occupied ↔ k ∈ i.toNat :: (ls ++ rs)) := by
  let j := rightPivot arena i
  obtain ⟨cs, ds, leftUsed, child⟩ := layout_pending pending.leftLayout
  change Pending arena j c y (.node b z d) cs ds at child
  change ls = j.toNat :: (cs ++ ds) at leftUsed
  let k := leftPivot arena j
  have hasK : k.toNat ∈ ds := child.rightLayout.index_used.resolve_left child.rightLayout.root_key.1
  have leftGuard := (heightGuard pending.rightLayout pending.leftLayout fits).mpr heavy
  have innerGuard :
      modelHeight arena (cell arena.slots (cell arena.slots i).left).left <
        modelHeight arena (cell arena.slots (cell arena.slots i).left).right := by
    change modelHeight arena (cell arena.slots j).left < modelHeight arena (cell arena.slots j).right
    rwa [UInt64.lt_iff_toNat_lt, child.leftLayout.model_height, child.rightLayout.model_height]
  obtain ⟨rotated, rotatedUsed, first, updated, firstFrame, sameFirst⟩ :=
    generated_rotate_left_layout arena j c b d y z cs ds child fits (start + 9)
  have partialFrame : ChangedWithin arena rotated ls :=
    firstFrame.changedWithin (by simp [leftUsed]) (show k.toNat ∈ ls by simp [leftUsed, hasK])
  have preserves (n : Nat) : n ∈ rotatedUsed ↔ n ∈ ls := by rw [sameFirst n, leftUsed]
  let linked := linkLeft rotated i k
  have adjusted : Pending linked i (.node (.node c y b) z d) x a rotatedUsed rs :=
    pending_link_left pending partialFrame updated preserves fits
  have linkSize : linked.slots.size = arena.slots.size := (linkLeft_size ..).trans partialFrame.size
  let target := i.toNat :: (ls ++ rs)
  have frameLink : ChangedWithin rotated linked target :=
    putCell_changedWithin _ _ _ (by rw [partialFrame.size]; exact pending.allocated)
      (by rwa [partialFrame.size]) (by simp [target])
  obtain ⟨next, occupied, second, layout, lastFrame, sameLast⟩ :=
    generated_rotate_right_layout linked i a d (.node c y b) x z rotatedUsed rs adjusted
      (by rwa [linkSize]) (start + 32)
  have childNow : rightPivot linked i = k := by
    have wrote := linkLeft_preserves rotated i k (by rw [partialFrame.size]; exact pending.allocated)
      (by rwa [partialFrame.size])
    exact congrArg cp.TreeSet_Slot.left wrote
  have secondRun : (cp.TreeSet.rotate_right linked i).run (start + 32) =
      some ((k, next), start + 55) := by simpa only [childNow] using second
  have allK : k.toNat ∈ target := by simp [target, leftUsed, hasK]
  have lastChanged : ChangedWithin linked next target :=
    lastFrame.changedWithin (by simp [target]) (by rwa [childNow])
  have combined := (partialFrame.trans frameLink (by intro n mem; simp [target, mem]) (fun _ h => h)).trans
    lastChanged (fun _ h => h) (fun _ h => h)
  refine ⟨k, next, occupied, ?_, ?_, combined, ?_⟩
  · rw [generated_rebalance_program]
    simp only [rebalanceProgram, StateT.run_bind, tick_run, some_bind, generated_height_run,
      leftGuard, decide_true, ite_true]
    change (rebalanceLeft arena i).run (start + 5) = _
    simp only [rebalanceLeft, StateT.run_bind, some_bind, generated_height_run, innerGuard,
      decide_true, ite_true, pure_run]
    change (do
      let p ← (cp.TreeSet.rotate_left arena j).run (start + 9)
      (cp.TreeSet.rotate_right (linkLeft p.1.2 i p.1.1) i).run p.2) = _
    have firstRun : (cp.TreeSet.rotate_left arena j).run (start + 9) = some ((k, rotated), start + 32) := first
    simp only [firstRun, some_bind]
    exact secondRun
  · rw [childNow] at layout
    simpa [Tree.balance, Tree.balanceLeft, heavy, double] using layout
  · intro n
    simp only [sameLast n, List.mem_cons, List.mem_append, preserves n]


theorem generated_rebalance_layout {K : Type} [Inhabited K] (arena : cp.TreeSet K) (i : UInt64)
    (left right : Tree K) (key : K) (ls rs : List Nat)
    (pending : Pending arena i left key right ls rs) (fits : arena.slots.size ≤ 2 ^ 63) (start : Nat) :
    ∃ root next occupied stop, (cp.TreeSet.rebalance arena i).run start = some ((root, next), stop) ∧
      stop ≤ start + 55 ∧ Layout next.slots root (Tree.balance left key right) occupied ∧
      ChangedWithin arena next (i.toNat :: (ls ++ rs)) ∧
      (∀ k, k ∈ occupied ↔ k ∈ i.toNat :: (ls ++ rs)) := by
  by_cases heavyL : right.height + 1 < left.height
  · cases left with
    | empty => simp [Tree.height] at heavyL
    | node outer child inner =>
      by_cases isDouble : outer.height < inner.height
      · cases inner with
        | empty => simp [Tree.height] at isDouble
        | node a pivot b =>
          obtain ⟨root, next, occupied, ran, layout, changed, same⟩ :=
            generated_rebalance_double_right arena i right a outer b key child pivot ls rs
              pending fits heavyL isDouble start
          exact ⟨root, next, occupied, start + 55, ran, le_rfl, layout, changed, same⟩
      · obtain ⟨root, next, occupied, ran, layout, changed, same⟩ :=
          generated_rebalance_single_right arena i right inner outer key child ls rs
            pending fits heavyL isDouble start
        exact ⟨root, next, occupied, start + 32, ran, by omega, layout, changed, same⟩
  · by_cases heavyR : left.height + 1 < right.height
    · cases right with
      | empty => simp [Tree.height] at heavyR
      | node inner child outer =>
        by_cases isDouble : outer.height < inner.height
        · cases inner with
          | empty => simp [Tree.height] at isDouble
          | node a pivot b =>
            obtain ⟨root, next, occupied, ran, layout, changed, same⟩ :=
              generated_rebalance_double_left arena i left b outer a key child pivot ls rs
                pending fits heavyR isDouble start
            exact ⟨root, next, occupied, start + 55, ran, le_rfl, layout, changed, same⟩
        · obtain ⟨root, next, occupied, ran, layout, changed, same⟩ :=
            generated_rebalance_single_left arena i left inner outer key child ls rs
              pending fits heavyR isDouble start
          exact ⟨root, next, occupied, start + 32, ran, by omega, layout, changed, same⟩
    · let next := putCell arena i (refreshRow arena i)
      have computed := generated_rebalance_level arena i left right key ls rs pending fits heavyL heavyR start
      exact ⟨i, next, i.toNat :: (ls ++ rs), start + 16, computed.1, by omega,
        computed.2.1, computed.2.2, fun _ => Iff.rfl⟩

end Proofs.Cpp.TreeSet
