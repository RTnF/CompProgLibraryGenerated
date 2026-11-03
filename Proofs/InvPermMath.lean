namespace Proofs.InvPermMath

-- The inverse array after the first `i` entries of `items` have been processed.
def pinv (items : List Int) (n : Nat) : Nat → List Int
  | 0 => List.replicate n (-1)
  | i+1 => (pinv items n i).set (items[i]?.getD 0).toNat (i : Int)

theorem pinv_length (items : List Int) (n i : Nat) : (pinv items n i).length = n := by
  induction i with
  | zero => simp [pinv]
  | succ i ih => simp [pinv,ih]

theorem toNat_inj (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) (h : x.toNat = y.toNat) : x = y := by omega

-- Every processed source position j is stored at its target items[j].
theorem pinv_written (items : List Int) (n : Nat) (hrange : ∀ (j : Nat) (x : Int), items[j]? = some x → 0 ≤ x ∧ x < n)
    (hinj : ∀ (j k : Nat) (x : Int), items[j]? = some x → items[k]? = some x → j = k) :
    ∀ i, i ≤ items.length → ∀ j x, j < i → items[j]? = some x → (pinv items n i)[x.toNat]? = some (j : Int) := by
  intro i
  induction i with
  | zero => intro _ j x lt; omega
  | succ i ih =>
    intro hi j x lt item
    have iItem : items[i]? = some items[i] := by simp [List.getElem?_eq_getElem (by omega : i < items.length)]
    have ir := hrange i items[i] iItem
    simp only [pinv, iItem, Option.getD_some]
    by_cases same : j = i
    · subst same
      have : x = items[j] := by rw [iItem] at item; exact (Option.some.inj item).symm
      subst this
      exact List.getElem?_set_self (by rw [pinv_length]; have := (hrange _ _ item); omega)
    · have older : j < i := by omega
      have prev := ih (by omega) j x older item
      have differ : x.toNat ≠ items[i].toNat := by
        intro h
        have xr := hrange j x item
        have eq := toNat_inj _ _ xr.1 ir.1 h
        have : j = i := hinj j i x item (by rw [iItem, eq]) 
        exact same this
      rw [List.getElem?_set_ne (Ne.symm differ)]
      exact prev

-- Targets that no processed entry points to are still -1.
theorem pinv_untouched (items : List Int) (n : Nat) (hrange : ∀ (j : Nat) (x : Int), items[j]? = some x → 0 ≤ x ∧ x < n) :
    ∀ i, i ≤ items.length → ∀ p, p < n → (∀ j x, j < i → items[j]? = some x → x.toNat ≠ p) →
      (pinv items n i)[p]? = some (-1) := by
  intro i
  induction i with
  | zero => intro _ p hp _; simp [pinv, hp]
  | succ i ih =>
    intro hi p hp avoid
    have iItem : items[i]? = some items[i] := by simp [List.getElem?_eq_getElem (by omega : i < items.length)]
    simp only [pinv, iItem, Option.getD_some]
    have differ : items[i].toNat ≠ p := avoid i items[i] (by omega) iItem
    rw [List.getElem?_set_ne differ]
    exact ih (by omega) p hp (fun j x lt item => avoid j x (by omega) item)

end Proofs.InvPermMath
