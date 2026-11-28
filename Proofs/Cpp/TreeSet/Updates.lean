import Proofs.Cpp.TreeSet.AVL

namespace Proofs.Cpp.TreeSet.Tree

theorem no_rotation (left : Tree K) (key : K) (right : Tree K)
    (lr : left.height ≤ right.height + 1) (rl : right.height ≤ left.height + 1) :
    balance left key right = .node left key right := by
  unfold balance
  rw [ite_eq_right (by omega : ¬ right.height + 1 < left.height),
      ite_eq_right (by omega : ¬ left.height + 1 < right.height)]

theorem grow (left right : Tree K) (key : K) (oldL oldR : Nat)
    (lb : left.Balanced) (rb : right.Balanced)
    (lr : oldL ≤ oldR + 1) (rl : oldR ≤ oldL + 1)
    (changed : (oldL ≤ left.height ∧ left.height ≤ oldL + 1 ∧ right.height = oldR) ∨
      (oldR ≤ right.height ∧ right.height ≤ oldR + 1 ∧ left.height = oldL)) :
    (balance left key right).Balanced ∧
      max oldL oldR + 1 ≤ (balance left key right).height ∧
      (balance left key right).height ≤ max oldL oldR + 2 := by
  have span : near left right := by
    rcases changed with ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> exact ⟨by omega, by omega⟩
  obtain ⟨valid, low, high⟩ := balance_correct left key right lb rb span
  refine ⟨valid, ?_, ?_⟩
  · by_cases top : max left.height right.height = max oldL oldR
    · have h₁ : left.height ≤ right.height + 1 := by
        rcases changed with ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega
      have h₂ : right.height ≤ left.height + 1 := by
        rcases changed with ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega
      rw [no_rotation left key right h₁ h₂]
      simp [height, top]
    · rcases changed with ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega
  · rcases changed with ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega

theorem shrink (left right : Tree K) (key : K) (oldL oldR : Nat)
    (lb : left.Balanced) (rb : right.Balanced)
    (lr : oldL ≤ oldR + 1) (rl : oldR ≤ oldL + 1)
    (changed : (left.height ≤ oldL ∧ oldL ≤ left.height + 1 ∧ right.height = oldR) ∨
      (right.height ≤ oldR ∧ oldR ≤ right.height + 1 ∧ left.height = oldL)) :
    (balance left key right).Balanced ∧
      max oldL oldR ≤ (balance left key right).height ∧
      (balance left key right).height ≤ max oldL oldR + 1 := by
  have span : near left right := by
    rcases changed with ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> exact ⟨by omega, by omega⟩
  obtain ⟨valid, low, high⟩ := balance_correct left key right lb rb span
  refine ⟨valid, ?_, ?_⟩
  · by_cases top : max left.height right.height < max oldL oldR
    · have h₁ : left.height ≤ right.height + 1 := by
        rcases changed with ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega
      have h₂ : right.height ≤ left.height + 1 := by
        rcases changed with ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega
      rw [no_rotation left key right h₁ h₂]
      simp only [height]
      rcases changed with ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega
    · omega
  · rcases changed with ⟨_, _, _⟩ | ⟨_, _, _⟩ <;> omega

def insert [LT K] [DecidableLT K] (key : K) : Tree K → Tree K
  | .empty => .node .empty key .empty
  | tree@(.node left current right) =>
    if key < current then balance (left.insert key) current right
    else if current < key then balance left current (right.insert key)
    else tree

def extractMin : Tree K → Option (K × Tree K)
  | .empty => none
  | .node .empty key right => some (key, right)
  | .node (left@(.node _ _ _)) key right =>
    (left.extractMin).map fun (first, replacement) => (first, balance replacement key right)

def erase [LT K] [DecidableLT K] (key : K) : Tree K → Tree K
  | .empty => .empty
  | .node left current right =>
    if key < current then balance (left.erase key) current right
    else if current < key then balance left current (right.erase key)
    else
      match left with
      | .empty => right
      | .node _ _ _ =>
        match right.extractMin with
        | none => left
        | some (first, replacement) => balance left first replacement

theorem insert_balanced [LT K] [DecidableLT K] (key : K) (tree : Tree K) (valid : tree.Balanced) :
    (tree.insert key).Balanced ∧ tree.height ≤ (tree.insert key).height ∧
      (tree.insert key).height ≤ tree.height + 1 := by
  induction tree with
  | empty => simp [insert, Balanced, height]
  | node left current right il ir =>
    obtain ⟨lb, rb, lr, rl⟩ := valid
    unfold insert
    split
    · obtain ⟨next, lower, upper⟩ := il lb
      exact grow _ _ current _ _ next rb lr rl (Or.inl ⟨lower, upper, rfl⟩)
    split
    · obtain ⟨next, lower, upper⟩ := ir rb
      exact grow _ _ current _ _ lb next lr rl (Or.inr ⟨lower, upper, rfl⟩)
    · exact ⟨⟨lb, rb, lr, rl⟩, Nat.le_refl _, Nat.le_succ _⟩

theorem extract_balanced (tree : Tree K) (valid : tree.Balanced) (nonempty : tree ≠ .empty) :
    ∃ key result, tree.extractMin = some (key, result) ∧
      result.Balanced ∧ result.height ≤ tree.height ∧ tree.height ≤ result.height + 1 ∧
      tree.keys = key :: result.keys := by
  induction tree with
  | empty => exact (nonempty rfl).elim
  | node left current right il _ =>
    obtain ⟨lb, rb, lr, rl⟩ := valid
    cases left with
    | empty =>
      refine ⟨current, right, by simp [extractMin], rb, ?_, ?_, by simp [keys]⟩ <;> simp [height]
    | node ll k lr' =>
      obtain ⟨first, updated, run, balanceUpdated, lo, hi, items⟩ := il lb (by simp)
      obtain ⟨balanced, minHeight, maxHeight⟩ :=
        shrink updated right current _ _ balanceUpdated rb lr rl (Or.inl ⟨lo, hi, rfl⟩)
      refine ⟨first, balance updated current right, ?_, balanced, maxHeight, ?_, ?_⟩
      · simp [extractMin, run]
      · change max (.node ll k lr' : Tree K).height right.height + 1 ≤ _
        omega
      · change (.node ll k lr' : Tree K).keys ++ [current] ++ right.keys =
          first :: (balance updated current right).keys
        rw [items, balance_keys]
        rfl

theorem erase_balanced [LT K] [DecidableLT K] (key : K) (tree : Tree K) (valid : tree.Balanced) :
    (tree.erase key).Balanced ∧ (tree.erase key).height ≤ tree.height ∧
      tree.height ≤ (tree.erase key).height + 1 := by
  induction tree with
  | empty => simp [erase, Balanced, height]
  | node left current right il ir =>
    obtain ⟨lb, rb, lr, rl⟩ := valid
    unfold erase
    split
    · obtain ⟨updated, lo, hi⟩ := il lb
      obtain ⟨v, low, high⟩ := shrink _ _ current _ _ updated rb lr rl (Or.inl ⟨lo, hi, rfl⟩)
      exact ⟨v, high, by simp only [height]; omega⟩
    split
    · obtain ⟨updated, lo, hi⟩ := ir rb
      obtain ⟨v, low, high⟩ := shrink _ _ current _ _ lb updated lr rl (Or.inr ⟨lo, hi, rfl⟩)
      exact ⟨v, high, by simp only [height]; omega⟩
    · cases left with
      | empty => exact ⟨rb, by simp [height], by simp [height]⟩
      | node ll lk lr' =>
        cases right with
        | empty =>
          simp only [extractMin]
          refine ⟨lb, ?_, ?_⟩ <;> simp [height]
        | node rl' rk rr =>
          obtain ⟨first, replacement, run, updated, lo, hi, _⟩ :=
            extract_balanced (.node rl' rk rr) rb (by simp)
          have h := shrink (.node ll lk lr') replacement first _ _ lb updated lr rl (Or.inr ⟨lo, hi, rfl⟩)
          rw [run]
          refine ⟨h.1, h.2.2, ?_⟩
          change max (.node ll lk lr' : Tree K).height (.node rl' rk rr : Tree K).height + 1 ≤ _
          exact Nat.succ_le_succ h.2.1

end Proofs.Cpp.TreeSet.Tree
