import Proofs.UfReadQueries
import Proofs.CppMoveReceiverLayout

namespace Proofs.UfReadPrograms
open Proofs.CppNestedCall
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.DoublingNested Proofs.PrefixSumsCall
open Proofs.UfReadQueries Proofs.CppMoveReceiverLayout Proofs.StraightLine Proofs.VecExpr
open Proofs.QuotientFrame Proofs.CppState

abbrev sizeProgram : NProgram := ⟨[.vector i32 false,.scalar i32 true false,
  .scalar i32 false true,.scalar i32 false true],.scalar i32,sizeBody⟩
abbrev sameProgram : NProgram := ⟨[.vector i32 false,.scalar i32 true false,
  .scalar i32 false true,.scalar i32 false true,.scalar i32 false true],.scalar bT,sameBody⟩
abbrev counterProgram : NProgram := ⟨[.vector i32 false,.scalar i32 true false,
  .scalar i32 false true],.scalar i32,counterBody⟩

def fields (P : List Cell) (address : Nat) (values : List Int) : Proofs.StraightLine.PS :=
  ⟨P++cells i32 values,⟨address,false⟩::valueBindings P.length values.length⟩

theorem size_n (P : List Cell) (address : Nat) (n a : Int) (valid : i32.valid n = true) :
    penv1 (fields P address [n,a]) 2 i32 = some n := by
  simp [fields,cells,valueBindings,addresses,penv1,penv,valid]
theorem size_a (P : List Cell) (address : Nat) (n a : Int) (valid : i32.valid a = true) :
    penv1 (fields P address [n,a]) 3 i32 = some a := by
  simp [fields,cells,valueBindings,addresses,penv1,penv,valid]
theorem same_n (P : List Cell) (address : Nat) (n a b : Int) (valid : i32.valid n = true) :
    penv1 (fields P address [n,a,b]) 2 i32 = some n := by
  simp [fields,cells,valueBindings,addresses,penv1,penv,valid]
theorem same_a (P : List Cell) (address : Nat) (n a b : Int) (valid : i32.valid a = true) :
    penv1 (fields P address [n,a,b]) 3 i32 = some a := by
  simp [fields,cells,valueBindings,addresses,penv1,penv,valid]
theorem same_b (P : List Cell) (address : Nat) (n a b : Int) (valid : i32.valid b = true) :
    penv1 (fields P address [n,a,b]) 4 i32 = some b := by
  simp [fields,cells,valueBindings,addresses,penv1,penv,valid,Nat.add_assoc]

theorem qs_size (initial : NState) (P : List Cell) (address : Nat) (n a : Int)
    (qs : QS initial [] initial.scalars.baseMemory initial.scope
      (P++cells i32 [n,a]) (⟨address,false⟩::valueBindings P.length 2)
      (.vector 0 :: .scalar 0 :: valueSlots 1 2)) :
    QS initial [] initial.scalars.baseMemory initial.scope (fields P address [n,a]).mem
      (fields P address [n,a]).bs (sl1 (fields P address [n,a]).bs.length) := by
  simpa [fields,cells,valueBindings,addresses,valueSlots,sl1,Proofs.Mod61Body.ssl,
    List.range_succ,List.append_assoc,Nat.add_assoc] using qs

theorem qs_same (initial : NState) (P : List Cell) (address : Nat) (n a b : Int)
    (qs : QS initial [] initial.scalars.baseMemory initial.scope
      (P++cells i32 [n,a,b]) (⟨address,false⟩::valueBindings P.length 3)
      (.vector 0 :: .scalar 0 :: valueSlots 1 3)) :
    QS initial [] initial.scalars.baseMemory initial.scope (fields P address [n,a,b]).mem
      (fields P address [n,a,b]).bs (sl1 (fields P address [n,a,b]).bs.length) := by
  simpa [fields,cells,valueBindings,addresses,valueSlots,sl1,Proofs.Mod61Body.ssl,
    List.range_succ,List.append_assoc,Nat.add_assoc] using qs
theorem counter_value (P : List Cell) (address : Nat) (n count : Int)
    (found : P[address]? = some ⟨i32,count⟩) (valid : i32.valid count = true) :
    penv1 (fields P address [n]) 1 i32 = some count := by
  have inside := (List.getElem?_eq_some_iff.mp found).1
  simp [fields,penv1,penv,List.getElem?_append_left inside,found,valid]

theorem qs_counter (initial : NState) (P : List Cell) (address : Nat) (n : Int)
    (qs : QS initial [] initial.scalars.baseMemory initial.scope
      (P++cells i32 [n]) (⟨address,false⟩::valueBindings P.length 1)
      (.vector 0 :: .scalar 0 :: valueSlots 1 1)) :
    QS initial [] initial.scalars.baseMemory initial.scope (fields P address [n]).mem
      (fields P address [n]).bs (sl1 (fields P address [n]).bs.length) := by
  simpa [fields,cells,valueBindings,addresses,valueSlots,sl1,Proofs.Mod61Body.ssl,
    List.range_succ,List.append_assoc,Nat.add_assoc] using qs
end Proofs.UfReadPrograms
