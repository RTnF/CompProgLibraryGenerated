import Std.Do
import Std.Tactic.Do

/-!
# Semantics of the translated C++ subset

`verifier/lean_translate.py` translates each public C++ function into a Lean function in the monad `Cpp.M`
(the rules are listed in `docs/translation.md`). This module defines that monad and the operations the
translation uses, once for all components.

* `Cpp.M := StateT Nat Option`. The state counts ticks: one per function call and loop iteration, plus the
  length of each vector the C++ code builds or copies. `none` means the C++ call does not return normally
  (an `assert` fails, or a `while` loop or a recursion runs out of `Cpp.fuel`).
* Integers are mathematical integers (`Int`); every component states once that its inputs and intermediate
  values fit the C++ type. `/` and `%` round toward zero as in C++; the bit operations use two's complement.
* The C++ standard library is taken to behave as documented, with the documented complexity
  (docs/trust_policy.md): each supported operation is defined here by its documented result, and the
  translation adds ticks of the documented order. No axiom is involved.
* `std::vector<T>` is `Array T`. Element access out of range is undefined behaviour in C++ and is not
  modelled (it reads `default`); the sanitizer tests check that it does not happen.

The `@[spec]` lemmas let `mvcgen` reason about ticks, assertions and `while` loops.
-/

namespace Proofs.Cpp

open Std.Do

abbrev M := StateT Nat Option

/-- The shape of assertions about `M` (the tick counter, then failure). -/
abbrev PS := PostShape.arg Nat (PostShape.except PUnit PostShape.pure)

/-- One step of work (a function call or a loop iteration). -/
@[inline] def tick : M Unit := modify (· + 1)

/-- `n` steps of work (building or copying `n` elements). -/
@[inline] def tickN (n : Nat) : M Unit := modify (· + n)

/-- `assert(c)`: the call stops (`none`) when `c` is false. `mvcgen` unfolds it into the two cases. -/
@[inline, spec] def check (c : Bool) : M Unit := if c then pure () else failure

@[spec] theorem tick_spec {Q : PostCond Unit PS} :
    ⦃fun t => Q.1 () (t + 1)⦄ tick ⦃Q⦄ := by
  mvcgen [tick]

@[spec] theorem tickN_spec {n : Nat} {Q : PostCond Unit PS} :
    ⦃fun t => Q.1 () (t + n)⦄ tickN n ⦃Q⦄ := by
  mvcgen [tickN]


/-! ## Loops -/

/-- `a, a + 1, ..., b - 1` (empty when `b ≤ a`): `for (i = a; i < b; i++)`. -/
def range (a b : Int) : List Int := (List.range (b - a).toNat).map (fun k : Nat => a + (k : Int))

/-- `b, b - 1, ..., a` (empty when `b < a`): `for (i = b; i >= a; i--)`. -/
def rangeDown (a b : Int) : List Int := (List.range (b - a + 1).toNat).map (fun k : Nat => b - (k : Int))

/-- An upper bound on the iterations of a `while` loop and on the depth of a recursion. A loop that
would run longer makes the call fail; a correctness theorem stating that the call succeeds therefore
also proves that it stops. -/
def fuel : Nat := 2 ^ 64

/-- The range of a `while` loop: `for _ in Cpp.forever do` repeats until `break`. -/
structure Forever where

def forever : Forever := {}

def loopFuel {β : Type} : Nat → β → (Unit → β → M (ForInStep β)) → M β
  | 0, _, _ => failure
  | n + 1, b, f => do
      match ← f () b with
      | .done b' => pure b'
      | .yield b' => loopFuel n b' f

instance : ForIn M Forever Unit where
  forIn _ b f := loopFuel fuel b f

/-- The invariant of a `while` loop: `cont` holds before each iteration and `done` after the loop;
`measure` decreases on each iteration that continues. -/
structure WhileInv (β : Type) where
  cont : β → Assertion PS
  done : β → Assertion PS
  measure : β → Nat

theorem loopFuel_spec {β : Type} {f : Unit → β → M (ForInStep β)} (inv : WhileInv β)
    (step : ∀ b, Triple (f () b) (inv.cont b)
      (fun r => match r with
        | .yield b' => spred(inv.cont b' ∧ ⌜inv.measure b' < inv.measure b⌝)
        | .done b' => inv.done b', ExceptConds.false)) :
    ∀ n (init : β), inv.measure init < n →
      Triple (loopFuel n init f) (inv.cont init) (inv.done, ExceptConds.false) := by
  intro n
  induction n with
  | zero => intro init h; omega
  | succ n ih =>
    intro init h
    simp only [loopFuel]
    apply Triple.bind _ _ (step init)
    intro r
    split
    · apply Triple.pure; exact .rfl
    · rename_i b'
      apply Triple.iff.mpr
      mintro ⟨hc, ⌜hm⌝⟩
      exact (Triple.iff.mp (ih b' (by omega)))

@[spec]
theorem Spec.forIn_forever {β : Type} {init : β} {f : Unit → β → M (ForInStep β)} (inv : WhileInv β)
    (step : ∀ b, Triple (f () b) (inv.cont b)
      (fun r => match r with
        | .yield b' => spred(inv.cont b' ∧ ⌜inv.measure b' < inv.measure b⌝)
        | .done b' => inv.done b', ExceptConds.false)) :
    Triple (forIn forever init f) spred(inv.cont init ∧ ⌜inv.measure init < fuel⌝)
      (inv.done, ExceptConds.false) := by
  apply Triple.iff.mpr
  mintro ⟨hc, ⌜hm⌝⟩
  exact Triple.iff.mp (loopFuel_spec inv step fuel init hm)

/-! ## Vectors -/

/-- `v.size()`. -/
@[inline] def size {α : Type} (v : Array α) : Int := v.size

/-- `v[i]`. -/
@[inline] def get {α : Type} [Inhabited α] (v : Array α) (i : Int) : α := v[i.toNat]!

/-- `v[i] = x`. -/
@[inline] def set {α : Type} (v : Array α) (i : Int) (x : α) : Array α := v.set! i.toNat x

/-- `std::vector<T>(n, x)`. -/
@[inline] def replicate {α : Type} (n : Int) (x : α) : Array α := Array.replicate n.toNat x

/-- `v.back()`. -/
@[inline] def back {α : Type} [Inhabited α] (v : Array α) : α := v.back!

/-- `v.resize(n, x)`. -/
def resize {α : Type} (v : Array α) (n : Int) (x : α) : Array α :=
  if n.toNat ≤ v.size then v.extract 0 n.toNat else v ++ Array.replicate (n.toNat - v.size) x

/-! ## Integers -/

/-- `a / b` (rounds toward zero). -/
@[inline] def div (a b : Int) : Int := a.tdiv b

/-- `a % b` (the sign of `a`). -/
@[inline] def mod (a b : Int) : Int := a.tmod b

/-- `a & b` in two's complement (the same definition as Mathlib's `Int.land`). -/
def land : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m &&& n)
  | .ofNat m, .negSucc n => .ofNat (Nat.bitwise (fun x y => x && !y) m n)
  | .negSucc m, .ofNat n => .ofNat (Nat.bitwise (fun x y => !x && y) m n)
  | .negSucc m, .negSucc n => .negSucc (m ||| n)

/-- `a | b` in two's complement (the same definition as Mathlib's `Int.lor`). -/
def lor : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m ||| n)
  | .ofNat m, .negSucc n => .negSucc (Nat.bitwise (fun x y => !x && y) m n)
  | .negSucc m, .ofNat n => .negSucc (Nat.bitwise (fun x y => x && !y) m n)
  | .negSucc m, .negSucc n => .negSucc (m &&& n)

/-- `a ^ b` in two's complement (the same definition as Mathlib's `Int.xor`). -/
def lxor : Int → Int → Int
  | .ofNat m, .ofNat n => .ofNat (m ^^^ n)
  | .ofNat m, .negSucc n => .negSucc (m ^^^ n)
  | .negSucc m, .ofNat n => .negSucc (m ^^^ n)
  | .negSucc m, .negSucc n => .ofNat (m ^^^ n)

/-- `a << b`. -/
@[inline] def shl (a b : Int) : Int := a * 2 ^ b.toNat

/-- `a >> b` (arithmetic shift, as GCC does for negative values). -/
@[inline] def shr (a b : Int) : Int := a >>> b.toNat

end Proofs.Cpp
