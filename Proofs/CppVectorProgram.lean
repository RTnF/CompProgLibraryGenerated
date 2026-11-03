import Proofs.CppMixedInvoke

namespace Proofs.CppVectorProgram
open Proofs.CppScalar Proofs.CppMixedInvoke

-- Slots identify C++ declaration order; vector/scalar bindings use separate
-- indices. The frontend must never reinterpret one kind as the other.
def _root_.Proofs.CppMixedInvoke.State.scalarSlot (s : State) (slot : Nat) : Option Nat := do
  let .scalar index ← s.slots[slot]? | none
  some index

def _root_.Proofs.CppMixedInvoke.State.vectorSlot (s : State) (slot : Nat) : Option Nat := do
  let .vector index ← s.slots[slot]? | none
  some index

def _root_.Proofs.CppMixedInvoke.State.scalarCell (s : State) (slot : Nat) (ty : Ty) :
    Option (CppState.Binding × CppState.Cell) := do
  let index ← s.scalarSlot slot
  let binding ← s.scalars.bindings[index]?
  let cell ← s.scalars.memory[binding.address]?
  if cell.type = ty ∧ ty.valid cell.value then some (binding,cell) else none

-- All expression leaves are reads. Evaluation order changes work counters and
-- conservative observations, but cannot change values visible to another leaf.
inductive Expr where
  | literal (ty : Ty) (value : Int)
  | variable (ty : Ty) (slot : Nat)
  | cast (ty : Ty) (operand : Expr)
  | targetCast (ty : Ty) (operand : Expr)
  | unary (ty : Ty) (op : Unary) (operand : Expr)
  | binary (ty : Ty) (op : Binary) (left right : Expr)
  | divrem (ty : Ty) (remainder : Bool) (left right : Expr)
  | logical (conjunction : Bool) (left right : Expr)
  | size (element : Ty) (slot : Nat)
  | read (element : Ty) (slot : Nat) (index : Expr)
deriving DecidableEq, Repr

def Expr.nodes : Expr → Nat
  | .literal _ _ | .variable _ _ => 1
  | .cast _ e | .targetCast _ e | .unary _ _ e => e.nodes+1
  | .binary _ _ a b | .divrem _ _ a b => a.nodes+b.nodes+1
  | .logical _ a b => a.nodes+b.nodes+1
  | .size _ _ => 2
  | .read _ _ index => index.nodes+2

def _root_.Proofs.CppMixedInvoke.State.charge (s : State) (work temporaries : Nat) : State :=
  let scalars := ({s.scalars with work := s.scalars.work+work} : CppState.State).observe temporaries
  let vectors := s.vectors.observe 0
  (⟨scalars,vectors,s.slots,s.peak⟩ : State).observe

def Expr.eval (s : State) : Expr → Option (State × Int)
  | .literal ty value =>
      if ty.valid value then some (s.charge 1 1,value) else none
  | .variable ty slot => do
      let (_,cell) ← s.scalarCell slot ty
      some (s.charge 1 1,cell.value)
  | .cast ty operand => do
      let (next,value) ← operand.eval (s.charge 0 (operand.nodes+1))
      let converted ← ty.convert value
      some (next.charge 1 1,converted)
  | .targetCast ty operand => do
      let (next,value) ← operand.eval (s.charge 0 (operand.nodes+1))
      let converted ← ty.targetConvert value
      some (next.charge 1 1,converted)
  | .unary ty op operand => do
      let (next,value) ← operand.eval (s.charge 0 (operand.nodes+1))
      let converted ← ty.convert (unaryValue op value)
      some (next.charge 1 1,converted)
  | .binary ty op left right => do
      let (next,a) ← left.eval (s.charge 0 (left.nodes+right.nodes+1))
      let (next,b) ← right.eval next
      let converted ← ty.convert (binaryValue op a b)
      some (next.charge 1 1,converted)
  | .divrem ty remainder left right => do
      let (next,a) ← left.eval (s.charge 0 (left.nodes+right.nodes+1))
      let (next,b) ← right.eval next
      let converted ← checkedDivRem ty remainder a b
      some (next.charge 1 1,converted)
  | .logical conjunction left right => do
      let (next,a) ← left.eval (s.charge 0 (left.nodes+right.nodes+1))
      if conjunction then
        if a == 0 then some (next.charge 1 1,0) else do
          let (last,b) ← right.eval next
          some (last.charge 1 1,if b == 0 then 0 else 1)
      else
        if a == 0 then do
          let (last,b) ← right.eval next
          some (last.charge 1 1,if b == 0 then 0 else 1)
        else some (next.charge 1 1,1)
  | .size ty slot => do
      let index ← s.vectorSlot slot
      let (vectors,value) ← s.vectors.size index ty
      some (({s with vectors := vectors} : State).charge 1 2,value)
  | .read ty slot index => do
      let (next,position) ← index.eval (s.charge 0 (index.nodes+2))
      let binding ← next.vectorSlot slot
      let reference ← next.vectors.elementRef binding ty position
      let (vectors,value) ← next.vectors.read reference
      some (({next with vectors := vectors} : State).charge 1 2,value)

inductive Stmt where
  | skip
  | sequence (first rest : Stmt)
  | scope (body : Stmt)
  | declare (ty : Ty) (writable : Bool) (value : Expr)
  | construct (ty : Ty) (writable : Bool) (count value : Expr)
  | assign (slot : Nat) (ty : Ty) (value : Expr)
  | write (slot : Nat) (ty : Ty) (index value : Expr)
  | reserve (slot : Nat) (ty : Ty) (requested : Expr)
  | appendReserved (slot : Nat) (ty : Ty) (value : Expr)
  | assignRange (target first last : Nat) (ty : Ty) (firstEnd lastEnd : Bool)
  | ret (value : Expr)
  | check (condition : Expr)
deriving DecidableEq, Repr

structure Step where
  state : State
  returned : Option Int := none
deriving DecidableEq, Repr

def Stmt.run (s : State) : Stmt → Option Step
  | .skip => some ⟨s,none⟩
  | .sequence first rest => do
      let step ← first.run s
      if step.returned.isSome then some step else rest.run step.state
  | .scope body => do
      let step ← body.run s
      let restored ← leaveScope s step.state
      some ⟨restored,step.returned⟩
  | .declare ty writable expression => do
      let (next,value) ← expression.eval s
      let value ← ty.convert value
      let scalars : CppState.State := {next.scalars with
        memory := next.scalars.memory ++ [⟨ty,value⟩],bindings := next.scalars.bindings ++ [⟨next.scalars.memory.length,writable⟩]}
      some ⟨({next with scalars := scalars,slots := next.slots ++ [.scalar next.scalars.bindings.length]} : State).charge 1 0,none⟩
  | .construct ty writable count expression => do
      let (next,length) ← count.eval (s.charge 0 (count.nodes+expression.nodes+2))
      let (next,value) ← expression.eval next
      if 0 ≤ length then
        let (vectors,index) ← next.vectors.construct ty writable (CppVectorBindings.sizeLimit ty) length.toNat value
        some ⟨({next with vectors := vectors,slots := next.slots ++ [.vector index]} : State).charge 3 0,none⟩
      else none
  | .assign slot ty expression => do
      let (next,value) ← expression.eval s
      let (binding,cell) ← next.scalarCell slot ty
      if binding.writable then
        let value ← ty.convert value
        let scalars := {next.scalars with memory := next.scalars.memory.set binding.address ⟨cell.type,value⟩}
        some ⟨({next with scalars := scalars} : State).charge 1 0,none⟩
      else none
  | .write slot ty index expression => do
      -- C++17 evaluates an assignment's right operand before its left operand.
      let (next,value) ← expression.eval (s.charge 0 (index.nodes+expression.nodes+2))
      let (next,position) ← index.eval next
      let binding ← next.vectorSlot slot
      let reference ← next.vectors.elementRef binding ty position
      let vectors ← next.vectors.write reference value
      some ⟨({next with vectors := vectors} : State).charge 1 0,none⟩
  | .reserve slot ty expression => do
      let (next,count) ← expression.eval s
      if 0 ≤ count then
        let binding ← next.vectorSlot slot
        let vectors ← next.vectors.reserve binding ty count.toNat
        some ⟨({next with vectors := vectors} : State).charge 1 1,none⟩
      else none
  | .appendReserved slot ty expression => do
      let (next,value) ← expression.eval s
      let binding ← next.vectorSlot slot
      let vectors ← next.vectors.appendReserved binding ty value
      some ⟨({next with vectors := vectors} : State).charge 1 1,none⟩
  | .ret expression => do
      let (next,value) ← expression.eval s
      some ⟨next.charge 1 0,some value⟩
  | .assignRange target first last ty firstEnd lastEnd => do
      -- Three owner expressions, two iterator constructions and one call.
      let next := s.charge 6 7
      let destination ← next.vectorSlot target
      let origin ← next.vectorSlot first
      let ending ← next.vectorSlot last
      let range ← next.vectors.iteratorRange origin ending ty firstEnd lastEnd
      let vectors ← next.vectors.assign destination origin ty range
      some ⟨({next with vectors := vectors} : State).charge 0 0,none⟩
  | .check expression => do
      let (next,value) ← expression.eval s
      if value == 0 then none else some ⟨next.charge 1 0,none⟩

structure Program where
  parameters : List CppVectorBindings.Parameter
  resultType : Ty
  body : Stmt
deriving DecidableEq, Repr

theorem assignRange_runs (s : State) (target first last : Nat) (ty : Ty)
    (firstEnd lastEnd : Bool) (destination origin ending : Nat)
    (range : CppVectorRange.IteratorRange) (vectors : CppVectorBindings.Frame)
    (targetSlot : (s.charge 6 7).vectorSlot target = some destination)
    (firstSlot : (s.charge 6 7).vectorSlot first = some origin)
    (lastSlot : (s.charge 6 7).vectorSlot last = some ending)
    (captured : (s.charge 6 7).vectors.iteratorRange origin ending ty firstEnd lastEnd = some range)
    (assigned : (s.charge 6 7).vectors.assign destination origin ty range = some vectors) :
    (Stmt.assignRange target first last ty firstEnd lastEnd).run s =
      some ⟨({s.charge 6 7 with vectors := vectors} : State).charge 0 0,none⟩ := by
  simp [Stmt.run,targetSlot,firstSlot,lastSlot,captured,assigned]

theorem assignRange_bad_range (s : State) (target first last : Nat) (ty : Ty)
    (firstEnd lastEnd : Bool) (destination origin ending : Nat)
    (targetSlot : (s.charge 6 7).vectorSlot target = some destination)
    (firstSlot : (s.charge 6 7).vectorSlot first = some origin)
    (lastSlot : (s.charge 6 7).vectorSlot last = some ending)
    (rejected : (s.charge 6 7).vectors.iteratorRange origin ending ty firstEnd lastEnd = none) :
    (Stmt.assignRange target first last ty firstEnd lastEnd).run s = none := by
  simp [Stmt.run,targetSlot,firstSlot,lastSlot,rejected]

def Program.call (program : Program) (caller : State) (arguments : List Argument) : Option State := do
  let initial ← prepare caller program.parameters arguments
  let step ← program.body.run initial
  let value ← step.returned
  finishScalar caller step.state program.resultType value

theorem literal_runs (s : State) (ty : Ty) (value : Int) (valid : ty.valid value = true) :
    (Expr.literal ty value).eval s = some (s.charge 1 1,value) := by simp [Expr.eval,valid]

theorem literal_invalid (s : State) (ty : Ty) (value : Int) (invalid : ty.valid value = false) :
    (Expr.literal ty value).eval s = none := by simp [Expr.eval,invalid]

theorem logical_and_skips_right (s next : State) (left right : Expr)
    (evaluated : left.eval (s.charge 0 (left.nodes+right.nodes+1)) = some (next,0)) :
    (Expr.logical true left right).eval s = some (next.charge 1 1,0) := by
  simp [Expr.eval,evaluated]

theorem logical_or_skips_right (s next : State) (left right : Expr) (value : Int)
    (evaluated : left.eval (s.charge 0 (left.nodes+right.nodes+1)) = some (next,value))
    (nonzero : value ≠ 0) :
    (Expr.logical false left right).eval s = some (next.charge 1 1,1) := by
  simp [Expr.eval,evaluated,nonzero]

theorem logical_and_reads_right (s next last : State) (left right : Expr) (a b : Int)
    (evaluated : left.eval (s.charge 0 (left.nodes+right.nodes+1)) = some (next,a))
    (nonzero : a ≠ 0) (evaluatedRight : right.eval next = some (last,b)) :
    (Expr.logical true left right).eval s = some (last.charge 1 1,if b == 0 then 0 else 1) := by
  simp [Expr.eval,evaluated,nonzero,evaluatedRight]

theorem logical_or_reads_right (s next last : State) (left right : Expr) (b : Int)
    (evaluated : left.eval (s.charge 0 (left.nodes+right.nodes+1)) = some (next,0))
    (evaluatedRight : right.eval next = some (last,b)) :
    (Expr.logical false left right).eval s = some (last.charge 1 1,if b == 0 then 0 else 1) := by
  simp [Expr.eval,evaluated,evaluatedRight]

theorem check_false_fails (s next : State) (expression : Expr)
    (evaluated : expression.eval s = some (next,0)) :
    (Stmt.check expression).run s = none := by simp [Stmt.run,evaluated]

theorem check_true_runs (s next : State) (expression : Expr) (value : Int)
    (evaluated : expression.eval s = some (next,value)) (nonzero : value ≠ 0) :
    (Stmt.check expression).run s = some ⟨next.charge 1 0,none⟩ := by
  simp [Stmt.run,evaluated,nonzero]

theorem variable_runs (s : State) (ty : Ty) (slot : Nat) (binding : CppState.Binding)
    (cell : CppState.Cell) (resolved : s.scalarCell slot ty = some (binding,cell)) :
    (Expr.variable ty slot).eval s = some (s.charge 1 1,cell.value) := by
  simp [Expr.eval,resolved]

theorem size_runs (s : State) (ty : Ty) (slot index : Nat)
    (vectors : CppVectorBindings.Frame) (value : Int) (resolved : s.vectorSlot slot = some index)
    (ran : s.vectors.size index ty = some (vectors,value)) :
    (Expr.size ty slot).eval s = some (({s with vectors := vectors} : State).charge 1 2,value) := by
  simp [Expr.eval,resolved,ran]

theorem read_runs (s next : State) (ty : Ty) (slot binding : Nat) (index : Expr)
    (position value : Int) (reference : CppVectorBindings.Reference) (vectors : CppVectorBindings.Frame)
    (evaluated : index.eval (s.charge 0 (index.nodes+2)) = some (next,position))
    (resolved : next.vectorSlot slot = some binding)
    (address : next.vectors.elementRef binding ty position = some reference)
    (read : next.vectors.read reference = some (vectors,value)) :
    (Expr.read ty slot index).eval s = some (({next with vectors := vectors} : State).charge 1 2,value) := by
  simp [Expr.eval,evaluated,resolved,address,read]

theorem scalar_slot_rejects_vector (s : State) (slot index : Nat)
    (found : s.slots[slot]? = some (.vector index)) : s.scalarSlot slot = none := by
  simp [CppMixedInvoke.State.scalarSlot,found]

theorem vector_slot_rejects_scalar (s : State) (slot index : Nat)
    (found : s.slots[slot]? = some (.scalar index)) : s.vectorSlot slot = none := by
  simp [CppMixedInvoke.State.vectorSlot,found]

theorem charge_preserves (s : State) (work temporaries : Nat) :
    (s.charge work temporaries).scalars.memory = s.scalars.memory ∧
    (s.charge work temporaries).scalars.bindings = s.scalars.bindings ∧
    (s.charge work temporaries).vectors.store = s.vectors.store ∧
    (s.charge work temporaries).slots = s.slots := by exact ⟨rfl,rfl,rfl,rfl⟩

theorem charge_work (s : State) (work temporaries : Nat) :
    (s.charge work temporaries).work = s.work+work := by
  simp [CppMixedInvoke.State.charge,CppMixedInvoke.State.work,CppMixedInvoke.State.observe,CppState.State.observe,CppVectorBindings.Frame.observe]
  omega

theorem sequence_after_return (s : State) (first rest : Stmt) (step : Step)
    (ran : first.run s = some step) (returned : step.returned.isSome = true) :
    (Stmt.sequence first rest).run s = some step := by simp [Stmt.run,ran,returned]

theorem call_without_return (program : Program) (caller initial : State) (arguments : List Argument)
    (prepared : prepare caller program.parameters arguments = some initial) (step : Step)
    (ran : program.body.run initial = some step) (noReturn : step.returned = none) :
    program.call caller arguments = none := by simp [Program.call,prepared,ran,noReturn]

theorem scope_runs (s : State) (body : Stmt) (step : Step) (restored : State)
    (ran : body.run s = some step) (restoration : leaveScope s step.state = some restored) :
    (Stmt.scope body).run s = some ⟨restored,step.returned⟩ := by
  simp [Stmt.run,ran,restoration]

theorem construct_runs (s counted valued : State) (ty : Ty) (writable : Bool) (count expression : Expr)
    (length value : Int) (vectors : CppVectorBindings.Frame) (index : Nat)
    (countedValue : count.eval (s.charge 0 (count.nodes+expression.nodes+2)) = some (counted,length))
    (elementValue : expression.eval counted = some (valued,value)) (nonnegative : 0 ≤ length)
    (constructed : valued.vectors.construct ty writable (CppVectorBindings.sizeLimit ty) length.toNat value = some (vectors,index)) :
    (Stmt.construct ty writable count expression).run s = some
      ⟨({valued with vectors := vectors,slots := valued.slots ++ [.vector index]} : State).charge 3 0,none⟩ := by
  simp [Stmt.run,countedValue,elementValue,nonnegative,constructed]

end Proofs.CppVectorProgram
