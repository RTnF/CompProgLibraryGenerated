import Proofs.Cpp.Prelude

/-! # `std::unordered_map<K, V>` (docs/translation.md)

The model of an unordered map is the list of its entries (distinct keys, in insertion order; the order is not
observable through the translated operations). The cost of each operation is the worst case of the documented
contract: `size + 1` steps for a lookup or an insertion, `size + 1` for `clear`. -/

namespace Proofs.Cpp

abbrev UMap (K V : Type) := List (K × V)

/-- The mapped value of `k`, if any. -/
def umapFind {K V : Type} [BEq K] (m : UMap K V) (k : K) : Option V := (m.find? (·.1 == k)).map (·.2)

/-- The map with `k` mapped to `v` (replacing the old value, or appended). -/
def umapPut {K V : Type} [BEq K] (m : UMap K V) (k : K) (v : V) : UMap K V :=
  if (m.find? (·.1 == k)).isSome then m.map (fun e => if e.1 == k then (k, v) else e) else m ++ [(k, v)]

/-- `m[k]`: the mapped value; a new key is inserted with the value-initialized value `default`. -/
def umapIndex {K V : Type} [BEq K] [Inhabited V] (m : UMap K V) (k : K) : M (V × UMap K V) := do
  tickN (m.length + 1)
  match umapFind m k with
  | some v => return (v, m)
  | none => return (default, m ++ [(k, default)])

/-- `m[k] = v`. -/
def umapSet {K V : Type} [BEq K] (m : UMap K V) (k : K) (v : V) : M (UMap K V) := do
  tickN (m.length + 1)
  return umapPut m k v

/-- `m.count(k)`: 1 if the key is present, otherwise 0. -/
def umapCount {K V : Type} [BEq K] (m : UMap K V) (k : K) : M UInt64 := do
  tickN (m.length + 1)
  return if (umapFind m k).isSome then 1 else 0

/-- `m.clear()`. -/
def umapClear {K V : Type} (m : UMap K V) : M (UMap K V) := do
  tickN (m.length + 1)
  return []

end Proofs.Cpp
