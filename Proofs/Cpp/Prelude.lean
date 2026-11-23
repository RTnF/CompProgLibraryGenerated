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

/-- A proof of a translated compile-time template constraint. No instances are
guessed: concrete differential bindings prove the proposition by decision. -/
class TemplateConstraint (p : Prop) : Prop where
  holds : p

/-- Compile-time C++ type properties, tagged by the source template parameter.
`isCvInt128` means equality to signed `__int128` after removing cv qualifiers. -/
class TypeTraits (tag : String) (α : Type) where
  isSigned : Bool
  isCvInt128 : Bool

open Std.Do

abbrev M := StateT Nat Option

/-- Standard numeric traits supplied separately for each C++ template parameter.
The tag distinguishes e.g. `T = int` and `U = long long` even when both are modelled
by `Int`. No global instance guesses a C++ type from its Lean carrier. Values in
discarded constexpr branches need not describe operations available on that type.
`negativeInfinity` is used only in a floating constexpr branch. -/
class NumericTraits (tag : String) (α : Type) where
  isFloatingPoint : Bool
  hasInfinity : Bool
  minimum : α
  maximum : α
  lowest : α
  infinity : α
  negativeInfinity : α

/-- LP64 integral limits for the mathematical integer carrier. -/
@[instance_reducible] def intNumericTraits (tag : String) (bits : Nat) (signed : Bool) : NumericTraits tag Int where
  isFloatingPoint := false
  hasInfinity := false
  minimum := if signed then -(2 ^ (bits - 1) : Int) else 0
  maximum := (2 ^ (if signed then bits - 1 else bits) : Int) - 1
  lowest := if signed then -(2 ^ (bits - 1) : Int) else 0
  infinity := 0
  negativeInfinity := 0

@[instance_reducible] def u32NumericTraits (tag : String) : NumericTraits tag UInt32 where
  isFloatingPoint := false
  hasInfinity := false
  minimum := 0
  maximum := 4294967295
  lowest := 0
  infinity := 0
  negativeInfinity := 0

@[instance_reducible] def u64NumericTraits (tag : String) : NumericTraits tag UInt64 where
  isFloatingPoint := false
  hasInfinity := false
  minimum := 0
  maximum := 18446744073709551615
  lowest := 0
  infinity := 0
  negativeInfinity := 0

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

/-- `std::sort(v.begin(), v.end())` (https://en.cppreference.com/w/cpp/algorithm/sort): a permutation of `v` sorted by
`<`, with O(n log n) comparisons. The order of equivalent elements is unspecified in C++; the model keeps their order
(a stable merge sort). Proofs about `sort` assume a linear order, under which the sorted permutation is unique, so
the choice does not matter. -/
def sort {α : Type} [LT α] [DecidableLT α] (v : Array α) : Array α :=
  (v.toList.mergeSort (fun a b => !decide (b < a))).toArray

/-- `std::unique` followed by `erase`: each run of equal adjacent elements collapses to its first element. -/
def uniqueList {α : Type} [DecidableEq α] : List α → List α
  | a :: b :: t => if a = b then uniqueList (a :: t) else a :: uniqueList (b :: t)
  | l => l

def unique {α : Type} [DecidableEq α] (v : Array α) : Array α := (uniqueList v.toList).toArray

/-- `std::sort` of a vector of `std::pair`s: `operator<` on pairs is lexicographic (`Prod.lexLt`). -/
def sortLex {α β : Type} [LT α] [LT β] [DecidableEq α] [DecidableLT α] [DecidableLT β] (v : Array (α × β)) :
    Array (α × β) :=
  (v.toList.mergeSort (fun a b => !decide (Prod.lexLt b a))).toArray

/-- `std::stable_sort(v.begin(), v.end(), comp)` (https://en.cppreference.com/w/cpp/algorithm/stable_sort): the
permutation of `v` sorted by the strict weak order `comp` that keeps the order of equivalent elements, with
O(n log n) comparisons. `List.mergeSort` is stable. -/
def stableSortBy {α : Type} (comp : α → α → Bool) (v : Array α) : Array α :=
  (v.toList.mergeSort (fun a b => !comp b a)).toArray

/-- `std::iota(v.begin(), v.end(), x)` (https://en.cppreference.com/w/cpp/algorithm/iota) on `n` elements. -/
def iota (n : Nat) (x : Int) : Array Int := Array.ofFn (n := n) fun i => x + i

/-- `std::lower_bound(v.begin(), v.end(), x) - v.begin()` (https://en.cppreference.com/w/cpp/algorithm/lower_bound):
the index of the first element that is not less than `x`. C++ requires the range to be partitioned by `e < x`
(e.g. sorted); on such a range this is the first index where `e < x` fails. -/
def lowerBound {α : Type} [LT α] [DecidableLT α] (v : Array α) (x : α) : Int :=
  (v.toList.findIdx (fun a => !decide (a < x)) : Int)

/-- The cost (ticks) of `std::sort` on `n` elements: the documented O(n log n). -/
def sortCost (n : Nat) : Nat := n * (Nat.log2 n + 1)

/-! ## Integers -/

/-- Integer magnitude and conversion used by the contracts of `std::gcd` and `std::lcm`.
For a generic C++ integral type these operations are explicit model parameters. -/
class NumericGcd (α : Type) where
  magnitude : α → Nat
  ofNat : Nat → α

instance : NumericGcd Int where
  magnitude := Int.natAbs
  ofNat := Int.ofNat

instance : NumericGcd UInt32 where
  magnitude := UInt32.toNat
  ofNat := UInt32.ofNat

instance : NumericGcd UInt64 where
  magnitude := UInt64.toNat
  ofNat := UInt64.ofNat

def numericGcd {α β γ : Type} [NumericGcd α] [NumericGcd β] [NumericGcd γ] (a : α) (b : β) : γ :=
  NumericGcd.ofNat (Nat.gcd (NumericGcd.magnitude a) (NumericGcd.magnitude b))

def numericLcm {α β γ : Type} [NumericGcd α] [NumericGcd β] [NumericGcd γ] (a : α) (b : β) : γ :=
  NumericGcd.ofNat (Nat.lcm (NumericGcd.magnitude a) (NumericGcd.magnitude b))

/-- The standard specifies no complexity bound for gcd/lcm. Proofs using these
operations therefore receive their cost functions explicitly; there is no default instance. -/
class NumericCost where
  gcd : Nat → Nat → Nat
  lcm : Nat → Nat → Nat

def numericGcdCost {α β : Type} [NumericGcd α] [NumericGcd β] [NumericCost]
    (a : α) (b : β) : Nat :=
  NumericCost.gcd (NumericGcd.magnitude a) (NumericGcd.magnitude b)

def numericLcmCost {α β : Type} [NumericGcd α] [NumericGcd β] [NumericCost]
    (a : α) (b : β) : Nat :=
  NumericCost.lcm (NumericGcd.magnitude a) (NumericGcd.magnitude b)

/-- `a / b` (rounds toward zero). -/
@[inline] def div (a b : Int) : Int := a.tdiv b

/-- `a < b` for values of two template parameters `α`, `β` (the operator of the C++ instance). -/
class HLt (α β : Type) where
  hlt : α → β → Bool

/-- The implicit conversion of a value of a template parameter `β` to another one `α`. -/
class Conv (β α : Type) where
  conv : β → α

instance {α : Type} [LT α] [DecidableLT α] : HLt α α := ⟨fun a b => decide (a < b)⟩
instance {α : Type} : Conv α α := ⟨id⟩
instance : Conv Int UInt32 := ⟨UInt32.ofInt⟩
instance : Conv Int UInt64 := ⟨UInt64.ofInt⟩

/-- Integral template conversions to the fixed unsigned carriers wrap modulo
the destination width, just like the concrete C++ casts below. -/
instance : NatCast UInt32 := ⟨UInt32.ofNat⟩
instance : NatCast UInt64 := ⟨UInt64.ofNat⟩

/-- The C++ expression `static_cast<uint32_t>(x % m)`, with the
usual arithmetic conversions performed before `%`. The source parameter tag
keeps distinct C++ types apart when they share the mathematical Int carrier.
Generic user types supply their own operation; no integer law is assumed. -/
class ModToUInt32 (tag : String) (α : Type) where
  apply : α → UInt32 → UInt32

instance (tag : String) : ModToUInt32 tag UInt32 := ⟨fun x m => x % m⟩
instance (tag : String) : ModToUInt32 tag UInt64 := ⟨fun x m => (x % m.toUInt64).toUInt32⟩
instance (tag : String) : ModToUInt32 tag Bool := ⟨fun x m => (if x then 1 else 0) % m⟩

/-- Integral bindings with the Int carrier: narrow integers first promote to
int and then to unsigned int because `m` is unsigned int. Wide integer
operands retain their mathematical value, under their source range premise. -/
@[instance_reducible] def intModToUInt32 (tag : String) (promoteToUnsigned : Bool) : ModToUInt32 tag Int :=
  ⟨fun x m => UInt32.ofInt ((if promoteToUnsigned then ((UInt32.ofInt x).toNat : Int) else x).tmod m.toNat)⟩

/-- Conversion of an unsigned value `v` to a signed `w`-bit type: the value modulo `2^w` in two's complement
(C++20 [conv.integral]; GCC defines the same for earlier standards). -/
def toSigned (w v : Nat) : Int := if v % 2 ^ w < 2 ^ (w - 1) then (v % 2 ^ w : Nat) else (v % 2 ^ w : Nat) - 2 ^ w

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

/-- Abstract standard stream states. Formatting, locale, flags, errors and exception
masks belong to these states; no decimal-only or successful-input restriction is imposed. -/
class Streams where
  Input : Type
  Output : Type

abbrev IStream [Streams] := Streams.Input
abbrev OStream [Streams] := Streams.Output

/-- A standard formatted extraction, including its stream state, target's old value,
and cost. A non-returning extraction is represented by failure in `M`. -/
class StreamRead (α : Type) [Streams] where
  read : IStream → α → M (α × IStream)

/-- A standard formatted insertion, including formatting state, errors and cost. -/
class StreamWrite (α : Type) [Streams] where
  write : OStream → α → M OStream

/-- A concrete C++ extraction overload. The tag distinguishes e.g. `long` and
`long long` even when both use the mathematical integer carrier. -/
class SourceStreamRead (source : String) (α : Type) [Streams] where
  read : IStream → α → M (α × IStream)

/-- A concrete C++ insertion overload, retaining formatting, locale and cost. -/
class SourceStreamWrite (source : String) (α : Type) [Streams] where
  write : OStream → α → M OStream

/-- Character insertion is distinct from insertion of its integer code. -/
structure StreamChar where
  code : Int
  deriving Inhabited, DecidableEq

end Proofs.Cpp
