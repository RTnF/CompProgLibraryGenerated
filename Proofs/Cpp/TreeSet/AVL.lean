import Mathlib.Order.Basic

namespace Proofs.Cpp.TreeSet

inductive Tree (K : Type) where
  | empty
  | node (left : Tree K) (key : K) (right : Tree K)

namespace Tree

def height : Tree K → Nat
  | .empty => 0
  | .node left _ right => max left.height right.height + 1

def size : Tree K → Nat
  | .empty => 0
  | .node left _ right => left.size + right.size + 1

def keys : Tree K → List K
  | .empty => []
  | .node left key right => left.keys ++ [key] ++ right.keys

def Balanced : Tree K → Prop
  | .empty => True
  | .node left _ right =>
      left.Balanced ∧ right.Balanced ∧ left.height ≤ right.height + 1 ∧ right.height ≤ left.height + 1

def near (left right : Tree K) : Prop :=
  left.height ≤ right.height + 2 ∧ right.height ≤ left.height + 2

def balanceLeft (left : Tree K) (key : K) (right : Tree K) : Tree K :=
  match left with
  | .empty => .node left key right
  | .node a x b =>
    if a.height < b.height then
      match b with
      | .empty => .node left key right
      | .node c y d => .node (.node a x c) y (.node d key right)
    else .node a x (.node b key right)

def balanceRight (left : Tree K) (key : K) (right : Tree K) : Tree K :=
  match right with
  | .empty => .node left key right
  | .node b x a =>
    if a.height < b.height then
      match b with
      | .empty => .node left key right
      | .node d y c => .node (.node left key d) y (.node c x a)
    else .node (.node left key b) x a

def balance (left : Tree K) (key : K) (right : Tree K) : Tree K :=
  if right.height + 1 < left.height then balanceLeft left key right
  else if left.height + 1 < right.height then balanceRight left key right
  else .node left key right

theorem balanceLeft_keys (left : Tree K) (key : K) (right : Tree K) :
    (balanceLeft left key right).keys = left.keys ++ [key] ++ right.keys := by
  cases left with
  | empty => rfl
  | node a x b =>
    by_cases rotates : a.height < b.height
    · cases b <;> simp [balanceLeft, rotates, keys, List.append_assoc]
    · simp [balanceLeft, rotates, keys, List.append_assoc]

theorem balanceRight_keys (left : Tree K) (key : K) (right : Tree K) :
    (balanceRight left key right).keys = left.keys ++ [key] ++ right.keys := by
  cases right with
  | empty => rfl
  | node b x a =>
    by_cases rotates : a.height < b.height
    · cases b <;> simp [balanceRight, rotates, keys, List.append_assoc]
    · simp [balanceRight, rotates, keys, List.append_assoc]

theorem balance_keys (left : Tree K) (key : K) (right : Tree K) :
    (balance left key right).keys = left.keys ++ [key] ++ right.keys := by
  unfold balance
  split
  · exact balanceLeft_keys left key right
  split
  · exact balanceRight_keys left key right
  · rfl

theorem balanceLeft_correct (left : Tree K) (key : K) (right : Tree K)
    (al : left.Balanced) (ar : right.Balanced) (gap : left.height = right.height + 2) :
    (balanceLeft left key right).Balanced ∧
      left.height ≤ (balanceLeft left key right).height ∧
      (balanceLeft left key right).height ≤ left.height + 1 := by
  cases left with
  | empty => simp [height] at gap
  | node a x b =>
    rcases al with ⟨ha, hb, ab, ba⟩
    by_cases inner : a.height < b.height
    · cases b with
      | empty => simp [height] at inner
      | node c y d =>
        rcases hb with ⟨hc, hd, cd, dc⟩
        simp only [height] at gap inner ab ba
        simp only [balanceLeft, height, inner, ite_true, Balanced]
        refine ⟨⟨⟨ha, hc, ?_, ?_⟩, ⟨hd, ar, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩ <;> omega
    · simp only [balanceLeft, inner, ite_false, Balanced, height] at gap ⊢
      refine ⟨⟨ha, ⟨hb, ar, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩ <;> omega

theorem balanceRight_correct (left : Tree K) (key : K) (right : Tree K)
    (al : left.Balanced) (ar : right.Balanced) (gap : right.height = left.height + 2) :
    (balanceRight left key right).Balanced ∧
      right.height ≤ (balanceRight left key right).height ∧
      (balanceRight left key right).height ≤ right.height + 1 := by
  cases right with
  | empty => simp [height] at gap
  | node b x a =>
    rcases ar with ⟨hb, ha, ba, ab⟩
    by_cases inner : a.height < b.height
    · cases b with
      | empty => simp [height] at inner
      | node d y c =>
        rcases hb with ⟨hd, hc, dc, cd⟩
        simp only [height] at gap inner ab ba
        simp only [balanceRight, height, inner, ite_true, Balanced]
        refine ⟨⟨⟨al, hd, ?_, ?_⟩, ⟨hc, ha, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩ <;> omega
    · simp only [balanceRight, inner, ite_false, Balanced, height] at gap ⊢
      refine ⟨⟨⟨al, hb, ?_, ?_⟩, ha, ?_, ?_⟩, ?_, ?_⟩ <;> omega

theorem balance_correct (left : Tree K) (key : K) (right : Tree K)
    (al : left.Balanced) (ar : right.Balanced) (close : near left right) :
    (balance left key right).Balanced ∧
      max left.height right.height ≤ (balance left key right).height ∧
      (balance left key right).height ≤ max left.height right.height + 1 := by
  obtain ⟨lr, rl⟩ := close
  unfold balance
  split
  · rename_i tooTall
    simpa [Nat.max_eq_left (show right.height ≤ left.height by omega)] using
      balanceLeft_correct left key right al ar (by omega)
  split
  · rename_i tooTall
    simpa [Nat.max_eq_right (show left.height ≤ right.height by omega)] using
      balanceRight_correct left key right al ar (by omega)
  · exact ⟨⟨al, ar, by omega, by omega⟩, by simp [height], by simp [height]⟩

theorem size_keys (tree : Tree K) : tree.keys.length = tree.size := by
  induction tree with
  | empty => rfl
  | node left key right ihL ihR => simp [keys, size, ihL, ihR]; omega

theorem height_exponential (tree : Tree K) (valid : tree.Balanced) :
    2 ^ (tree.height / 2) ≤ tree.size + 1 := by
  induction tree with
  | empty => simp [height, size]
  | node left key right ihL ihR =>
    obtain ⟨lb, rb, lr, rl⟩ := valid
    have leftBound := ihL lb
    have rightBound := ihR rb
    let level := (max left.height right.height + 1) / 2
    let lower := level - 1
    have leftLower : lower ≤ left.height / 2 := by dsimp [lower, level]; omega
    have rightLower : lower ≤ right.height / 2 := by dsimp [lower, level]; omega
    have leftPart := Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) leftLower) leftBound
    have rightPart := Nat.le_trans (Nat.pow_le_pow_right (by decide : 0 < 2) rightLower) rightBound
    change 2 ^ level ≤ left.size + right.size + 1 + 1
    by_cases ground : level = 0
    · simp [ground]
    · have upper : level = lower + 1 := by dsimp [lower]; omega
      rw [upper, Nat.pow_succ]
      omega

theorem height_logarithmic (tree : Tree K) (valid : tree.Balanced) :
    tree.height ≤ 2 * (tree.size + 1).log2 + 1 := by
  have exponent := height_exponential tree valid
  have bound := (Nat.le_log2 (by omega : tree.size + 1 ≠ 0)).mpr exponent
  omega

end Tree
end Proofs.Cpp.TreeSet
