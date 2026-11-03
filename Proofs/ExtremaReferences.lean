import Proofs.ExtremaInstances

namespace Proofs.ExtremaReferences
open Proofs.CppScalar Proofs.CppState

def boolean : Ty := ⟨1,false,true⟩
def integer : Ty := ⟨32,true,false⟩

-- A semantic schema; the four source-generated instances are identified by
-- definitional equality below. This does not replace primary-template lowering.
def schema (ty : Ty) (condition : Expr) : StateProgram :=
  ⟨[⟨ty,true,true⟩,⟨ty,true,false⟩],boolean,
    .scope (.sequence (.branch condition
      (.scope (.scope (.sequence (.assign 0 (.variable ty 1))
        (.sequence (.ret (.cast boolean (.literal integer 1))) .skip)))) .skip)
      (.sequence (.ret (.cast boolean (.literal integer 0))) .skip))⟩

theorem schema_call (ty : Ty) (condition : Expr) (memory : List Cell) (p q : Nat)
    (a b : Int) (update : Bool)
    (hp : memory[p]? = some ⟨ty,a⟩) (hq : memory[q]? = some ⟨ty,b⟩)
    (ha : ty.valid a = true) (hb : ty.valid b = true)
    (evaluated : condition.eval [a,b] = some ⟨if update then 1 else 0,3⟩)
    (nodes : condition.nodes = 3) :
    (schema ty condition).call memory [.reference p,.reference q] =
      some ⟨if update then 1 else 0,
        if update then memory.set p ⟨ty,b⟩ else memory,
        if update then 9 else 7,5⟩ := by
  have boundP : p < memory.length := (List.getElem?_eq_some_iff.mp hp).1
  have boundQ : q < memory.length := (List.getElem?_eq_some_iff.mp hq).1
  have updatedP : (memory.set p ⟨ty,b⟩)[p]? = some ⟨ty,b⟩ := by simp [boundP]
  have updatedQ : (memory.set p ⟨ty,b⟩)[q]? = some ⟨ty,b⟩ := by
    by_cases same : p = q
    · subst q; exact updatedP
    · simp [List.getElem?_set_ne same,hq]
  have takeUpdated : (memory.set p ⟨ty,b⟩).take memory.length = memory.set p ⟨ty,b⟩ := by
    have h := List.take_length (l := memory.set p ⟨ty,b⟩)
    simpa using h
  have cellP : memory[p] = ⟨ty,a⟩ := (List.getElem?_eq_some_iff.mp hp).2
  have cellQ : memory[q] = ⟨ty,b⟩ := (List.getElem?_eq_some_iff.mp hq).2
  have newCellQ : (memory.set p ⟨ty,b⟩)[q]'(by simpa) = ⟨ty,b⟩ :=
    (List.getElem?_eq_some_iff.mp updatedQ).2
  have boolValid0 : boolean.valid 0 = true := by decide
  have boolValid1 : boolean.valid 1 = true := by decide
  have intValid0 : integer.valid 0 = true := by decide
  have intValid1 : integer.valid 1 = true := by decide
  have boolConvert0 : boolean.convert 0 = some 0 := rfl
  have boolConvert1 : boolean.convert 1 = some 1 := rfl
  have converted := Ty.convert_of_valid ty b hb
  cases update <;>
    simp [schema,StateProgram.call,bindArguments,bindArgument,Stmt.run,State.evaluate,
      State.environment,State.observe,Expr.eval,Expr.nodes,
      boolValid0,boolValid1,intValid0,intValid1,boolConvert0,boolConvert1,cellP,cellQ,newCellQ,
      ha,hb,boundP,boundQ,evaluated,nodes,takeUpdated,converted]

def maxCondition (ty : Ty) : Expr := .binary boolean .lt (.variable ty 0) (.variable ty 1)
def minCondition (ty : Ty) : Expr := .binary boolean .lt (.variable ty 1) (.variable ty 0)

theorem maxCondition_eval (ty : Ty) (a b : Int)
    (ha : ty.valid a = true) (hb : ty.valid b = true) :
    (maxCondition ty).eval [a,b] = some ⟨if a < b then 1 else 0,3⟩ := by
  by_cases h : a < b <;> simp [maxCondition,Expr.eval,ha,hb,binaryValue,boolean,Ty.convert,h]

theorem minCondition_eval (ty : Ty) (a b : Int)
    (ha : ty.valid a = true) (hb : ty.valid b = true) :
    (minCondition ty).eval [a,b] = some ⟨if b < a then 1 else 0,3⟩ := by
  by_cases h : b < a <;> simp [minCondition,Expr.eval,ha,hb,binaryValue,boolean,Ty.convert,h]

theorem max_call (ty : Ty) (memory : List Cell) (p q : Nat) (a b : Int)
    (hp : memory[p]? = some ⟨ty,a⟩) (hq : memory[q]? = some ⟨ty,b⟩)
    (ha : ty.valid a = true) (hb : ty.valid b = true) :
    (schema ty (maxCondition ty)).call memory [.reference p,.reference q] =
      some ⟨if a < b then 1 else 0,
        if a < b then memory.set p ⟨ty,b⟩ else memory,if a < b then 9 else 7,5⟩ := by
  simpa using schema_call ty (maxCondition ty) memory p q a b (decide (a < b))
    hp hq ha hb (by simpa using maxCondition_eval ty a b ha hb) rfl

theorem min_call (ty : Ty) (memory : List Cell) (p q : Nat) (a b : Int)
    (hp : memory[p]? = some ⟨ty,a⟩) (hq : memory[q]? = some ⟨ty,b⟩)
    (ha : ty.valid a = true) (hb : ty.valid b = true) :
    (schema ty (minCondition ty)).call memory [.reference p,.reference q] =
      some ⟨if b < a then 1 else 0,
        if b < a then memory.set p ⟨ty,b⟩ else memory,if b < a then 9 else 7,5⟩ := by
  simpa using schema_call ty (minCondition ty) memory p q a b (decide (b < a))
    hp hq ha hb (by simpa using minCondition_eval ty a b ha hb) rfl

theorem signed_max_source : ExtremaInstances.chmax__int__int =
    schema ⟨32,true,false⟩ (maxCondition ⟨32,true,false⟩) := rfl
theorem signed_min_source : ExtremaInstances.chmin__int__int =
    schema ⟨32,true,false⟩ (minCondition ⟨32,true,false⟩) := rfl
theorem unsigned_max_source : ExtremaInstances.chmax__unsigned_int__unsigned_int =
    schema ⟨32,false,false⟩ (maxCondition ⟨32,false,false⟩) := rfl
theorem unsigned_min_source : ExtremaInstances.chmin__unsigned_int__unsigned_int =
    schema ⟨32,false,false⟩ (minCondition ⟨32,false,false⟩) := rfl

theorem chmax_signed (memory : List Cell) (p q : Nat) (a b : Int)
    (hp : memory[p]? = some ⟨⟨32,true,false⟩,a⟩) (hq : memory[q]? = some ⟨⟨32,true,false⟩,b⟩)
    (ha : Ty.valid ⟨32,true,false⟩ a = true) (hb : Ty.valid ⟨32,true,false⟩ b = true) :
    ExtremaInstances.chmax__int__int.call memory [.reference p,.reference q] =
      some ⟨if a < b then 1 else 0,
        if a < b then memory.set p ⟨⟨32,true,false⟩,b⟩ else memory,
        if a < b then 9 else 7,5⟩ := by
  rw [signed_max_source]
  exact max_call ⟨32,true,false⟩ memory p q a b hp hq ha hb

theorem chmin_signed (memory : List Cell) (p q : Nat) (a b : Int)
    (hp : memory[p]? = some ⟨⟨32,true,false⟩,a⟩) (hq : memory[q]? = some ⟨⟨32,true,false⟩,b⟩)
    (ha : Ty.valid ⟨32,true,false⟩ a = true) (hb : Ty.valid ⟨32,true,false⟩ b = true) :
    ExtremaInstances.chmin__int__int.call memory [.reference p,.reference q] =
      some ⟨if b < a then 1 else 0,
        if b < a then memory.set p ⟨⟨32,true,false⟩,b⟩ else memory,
        if b < a then 9 else 7,5⟩ := by
  rw [signed_min_source]
  exact min_call ⟨32,true,false⟩ memory p q a b hp hq ha hb

theorem chmax_unsigned (memory : List Cell) (p q : Nat) (a b : Int)
    (hp : memory[p]? = some ⟨⟨32,false,false⟩,a⟩) (hq : memory[q]? = some ⟨⟨32,false,false⟩,b⟩)
    (ha : Ty.valid ⟨32,false,false⟩ a = true) (hb : Ty.valid ⟨32,false,false⟩ b = true) :
    ExtremaInstances.chmax__unsigned_int__unsigned_int.call memory [.reference p,.reference q] =
      some ⟨if a < b then 1 else 0,
        if a < b then memory.set p ⟨⟨32,false,false⟩,b⟩ else memory,
        if a < b then 9 else 7,5⟩ := by
  rw [unsigned_max_source]
  exact max_call ⟨32,false,false⟩ memory p q a b hp hq ha hb

theorem chmin_unsigned (memory : List Cell) (p q : Nat) (a b : Int)
    (hp : memory[p]? = some ⟨⟨32,false,false⟩,a⟩) (hq : memory[q]? = some ⟨⟨32,false,false⟩,b⟩)
    (ha : Ty.valid ⟨32,false,false⟩ a = true) (hb : Ty.valid ⟨32,false,false⟩ b = true) :
    ExtremaInstances.chmin__unsigned_int__unsigned_int.call memory [.reference p,.reference q] =
      some ⟨if b < a then 1 else 0,
        if b < a then memory.set p ⟨⟨32,false,false⟩,b⟩ else memory,
        if b < a then 9 else 7,5⟩ := by
  rw [unsigned_min_source]
  exact min_call ⟨32,false,false⟩ memory p q a b hp hq ha hb

def updatedMemory (memory : List Cell) (p : Nat) (ty : Ty) (b : Int) (update : Bool) : List Cell :=
  if update then memory.set p ⟨ty,b⟩ else memory

theorem update_frame (ty : Ty) (memory : List Cell) (p q : Nat) (a b : Int) (update : Bool)
    (hp : memory[p]? = some ⟨ty,a⟩) (hq : memory[q]? = some ⟨ty,b⟩) :
    (updatedMemory memory p ty b update).length = memory.length ∧
    (updatedMemory memory p ty b update)[p]? = some ⟨ty,if update then b else a⟩ ∧
    (updatedMemory memory p ty b update)[q]? = some ⟨ty,b⟩ ∧
    ∀ r, r ≠ p → (updatedMemory memory p ty b update)[r]? = memory[r]? := by
  have boundP : p < memory.length := (List.getElem?_eq_some_iff.mp hp).1
  cases update
  · simp [updatedMemory,hp,hq]
  · refine ⟨by simp [updatedMemory],by simp [updatedMemory,boundP],?_,?_⟩
    · by_cases same : p = q
      · subst q; simp [updatedMemory,boundP]
      · simp [updatedMemory,List.getElem?_set_ne same,hq]
    · intro r different
      simp [updatedMemory,List.getElem?_set_ne (Ne.symm different)]

theorem max_alias (ty : Ty) (memory : List Cell) (p : Nat) (a : Int)
    (hp : memory[p]? = some ⟨ty,a⟩) (ha : ty.valid a = true) :
    (schema ty (maxCondition ty)).call memory [.reference p,.reference p] =
      some ⟨0,memory,7,5⟩ := by simpa using max_call ty memory p p a a hp hp ha ha

theorem min_alias (ty : Ty) (memory : List Cell) (p : Nat) (a : Int)
    (hp : memory[p]? = some ⟨ty,a⟩) (ha : ty.valid a = true) :
    (schema ty (minCondition ty)).call memory [.reference p,.reference p] =
      some ⟨0,memory,7,5⟩ := by simpa using min_call ty memory p p a a hp hp ha ha

end Proofs.ExtremaReferences
