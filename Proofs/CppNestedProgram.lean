import Proofs.CppNestedOps
import Proofs.CppFrameCopyCore
import Proofs.CppAppendRow
import Proofs.CppMixedInvoke

namespace Proofs.CppNestedProgram
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedVectorBindings
open Proofs.CppVectorOwnership Proofs.CppNestedVectorStore

-- Scalar locals and nested vector locals share one declaration-ordered slot
-- map. `scope` is the lexical scope ID given to newly constructed roots. The
-- frame's binding list holds both declared locals and expression temporaries.
structure NState where
  scalars : CppState.State
  frame : Frame
  slots : List Location := []
  scope : Nat := 0
  peak : Nat := 0
deriving DecidableEq, Repr

def NState.scalarSlot (s : NState) (slot : Nat) : Option Nat := do
  let .scalar index ← s.slots[slot]? | none
  some index

def NState.vectorSlot (s : NState) (slot : Nat) : Option Nat := do
  let .vector index ← s.slots[slot]? | none
  some index

def NState.scalarCell (s : NState) (slot : Nat) (ty : Ty) :
    Option (CppState.Binding × CppState.Cell) := do
  let index ← s.scalarSlot slot
  let binding ← s.scalars.bindings[index]?
  let cell ← s.scalars.memory[binding.address]?
  if cell.type = ty ∧ ty.valid cell.value then some (binding,cell) else none

def NState.work (s : NState) : Nat := s.scalars.work+s.frame.state.storage.work

-- Conservative combination of the scalar and nested-storage peaks. Slot maps,
-- binding lists and forest tags are ghost metadata, not C++ memory.
def NState.observe (s : NState) : NState :=
  {s with peak := max s.peak (s.scalars.peak+s.frame.state.storage.peak)}

def NState.charge (s : NState) (work temporaries : Nat) : NState :=
  let scalars := ({s.scalars with work := s.scalars.work+work} : CppState.State).observe temporaries
  ({s with scalars := scalars} : NState).observe

-- Reference temporaries die at the end of the full expression.
def NState.release (after before : NState) : NState :=
  {after with frame := {after.frame with bindings := after.frame.bindings.take before.frame.bindings.length}}

mutual
inductive Container where
  | local (slot : Nat)
  | row (parent : Container) (element : Element) (index : NExpr)
inductive NExpr where
  | literal (ty : Ty) (value : Int)
  | variable (ty : Ty) (slot : Nat)
  | cast (ty : Ty) (operand : NExpr)
  | targetCast (ty : Ty) (operand : NExpr)
  | unary (ty : Ty) (op : Unary) (operand : NExpr)
  | binary (ty : Ty) (op : Binary) (left right : NExpr)
  | divrem (ty : Ty) (remainder : Bool) (left right : NExpr)
  | logical (conjunction : Bool) (left right : NExpr)
  | size (element : Element) (container : Container)
  | read (element : Ty) (container : Container) (index : NExpr)
end

mutual
def Container.nodes : Container → Nat
  | .local _ => 1
  | .row parent _ index => parent.nodes+index.nodes+1
def NExpr.nodes : NExpr → Nat
  | .literal _ _ | .variable _ _ => 1
  | .cast _ e | .targetCast _ e | .unary _ _ e => e.nodes+1
  | .binary _ _ a b | .divrem _ _ a b => a.nodes+b.nodes+1
  | .logical _ a b => a.nodes+b.nodes+1
  | .size _ container => container.nodes+2
  | .read _ container index => container.nodes+index.nodes+2
end

mutual
def Container.eval (s : NState) : Container → Option (NState × Nat)
  | .local slot => do
      let binding ← s.vectorSlot slot
      some (s.charge 1 1,binding)
  | .row parent element index => do
      let (next,owner) ← parent.eval (s.charge 0 (parent.nodes+index.nodes+1))
      let (next,position) ← index.eval next
      let (frame,binding) ← next.frame.child owner element position
      some (({next with frame := frame} : NState).charge 1 1,binding)
def NExpr.eval (s : NState) : NExpr → Option (NState × Int)
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
  | .size element container => do
      let (next,owner) ← container.eval (s.charge 0 (container.nodes+2))
      let (frame,value) ← next.frame.size owner element
      some (({next with frame := frame} : NState).charge 1 2,value)
  | .read ty container index => do
      let (next,owner) ← container.eval (s.charge 0 (container.nodes+index.nodes+2))
      let (next,position) ← index.eval next
      let reference ← next.frame.elementRef owner ty position
      let value ← next.frame.read reference
      some (next.charge 1 2,value)
end

-- A vector result carries its root ID and element type; the enclosing scope
-- exit and call return transfer that root, so it is never retired early.
inductive Ret where
  | scalar (value : Int)
  | vector (owner : Nat) (element : Element)
  | unit
deriving DecidableEq, Repr

inductive NStmt where
  | skip
  | declare (ty : Ty) (writable : Bool) (value : NExpr)
  | constructRows (ty : Ty) (writable : Bool) (count : NExpr)
  | declareVector (ty : Ty) (writable : Bool)
  | fillVector (ty : Ty) (writable : Bool) (count value : NExpr)
  | assign (slot : Nat) (ty : Ty) (value : NExpr)
  | write (container : Container) (ty : Ty) (index value : NExpr)
  | reserve (container : Container) (ty : Ty) (requested : NExpr)
  | append (container : Container) (ty : Ty) (value : NExpr)
  | assignRange (target : Container) (first last : Nat) (ty : Ty) (firstEnd lastEnd : Bool)
  | ret (value : NExpr)
  | retVector (slot : Nat)
  | check (condition : NExpr)
  | sortVec (container : Container) (ty : Ty)
  | sortPairs (first second : Container) (ty : Ty)
  | dedupVec (container : Container) (ty : Ty)
  | appendRow (container : Container) (ty : Ty)
  | copyVector (source : Container) (ty : Ty) (writable : Bool)
  | retUnit

structure NStep where
  state : NState
  returned : Option Ret := none
  breaking : Bool := false
deriving DecidableEq, Repr

def _root_.Proofs.CppCopyStatement.run (s : NState) (source : Container) (ty : Ty) (writable : Bool) : Option NStep := do
  let (next,index) ← source.eval s
  let (binding,_) ← next.frame.resolve index (.integer ty)
  let released := next.release s
  let (frame,target) ← Proofs.CppFrameCopy.copyOwner released.frame binding.owner ty released.scope writable
  some ⟨({released with frame := frame,slots := released.slots++[.vector target]} : NState).charge 1 0,none,false⟩

def NStmt.run (s : NState) : NStmt → Option NStep
  | .skip => some ⟨s,none,false⟩
  | .declare ty writable expression => do
      let (next,value) ← expression.eval s
      let released := next.release s
      let value ← ty.convert value
      let scalars : CppState.State := {released.scalars with
        memory := released.scalars.memory ++ [⟨ty,value⟩],
        bindings := released.scalars.bindings ++ [⟨released.scalars.memory.length,writable⟩]}
      some ⟨({released with scalars := scalars,slots := released.slots ++ [.scalar released.scalars.bindings.length]} : NState).charge 1 0,none,false⟩
  | .constructRows ty writable count => do
      let (next,length) ← count.eval s
      if 0 ≤ length then
        let released := next.release s
        let state ← released.frame.state.constructRows ty released.scope length.toNat
        let root := released.frame.state.storage.objects.length
        let grown : Frame := {released.frame with
          state := state,
          rootWritable := released.frame.rootWritable ++ [writable] ++ List.replicate length.toNat false}
        let (frame,binding) ← grown.bindRoot root (.vector (.integer ty)) released.scope writable
        some ⟨({released with frame := frame,slots := released.slots ++ [.vector binding]} : NState).charge 3 0,none,false⟩
      else none
  | .declareVector ty writable => do
      let state ← s.frame.state.declareVector ty s.scope
      let root := s.frame.state.storage.objects.length
      let grown : Frame := {s.frame with state := state,rootWritable := s.frame.rootWritable ++ [writable]}
      let (frame,binding) ← grown.bindRoot root (.integer ty) s.scope writable
      some ⟨({s with frame := frame,slots := s.slots ++ [.vector binding]} : NState).charge 1 0,none,false⟩
  | .fillVector ty writable count value => do
      let (next,length) ← count.eval s
      let (next,x) ← value.eval next
      if 0 ≤ length then
        let released := next.release s
        let state ← released.frame.state.fillVector ty released.scope length.toNat x
        let root := released.frame.state.storage.objects.length
        let grown : Frame := {released.frame with state := state,rootWritable := released.frame.rootWritable ++ [writable]}
        let (frame,binding) ← grown.bindRoot root (.integer ty) released.scope writable
        some ⟨({released with frame := frame,slots := released.slots ++ [.vector binding]} : NState).charge 3 0,none,false⟩
      else none
  | .assign slot ty expression => do
      let (next,value) ← expression.eval s
      let released := next.release s
      let (binding,cell) ← released.scalarCell slot ty
      if binding.writable then
        let value ← ty.convert value
        let scalars := {released.scalars with
          memory := released.scalars.memory.set binding.address ⟨cell.type,value⟩}
        some ⟨({released with scalars := scalars} : NState).charge 1 0,none,false⟩
      else none
  | .write container ty index expression => do
      -- C++17 evaluates an assignment's right operand before its left operand.
      let (next,value) ← expression.eval (s.charge 0 (container.nodes+index.nodes+expression.nodes+3))
      let (next,owner) ← container.eval next
      let (next,position) ← index.eval next
      let reference ← next.frame.elementRef owner ty position
      let frame ← next.frame.write reference value
      some ⟨(({next with frame := frame} : NState).release s).charge 1 0,none,false⟩
  | .reserve container ty expression => do
      let (next,owner) ← container.eval (s.charge 0 (container.nodes+expression.nodes+2))
      let (next,count) ← expression.eval next
      if 0 ≤ count then
        let frame ← next.frame.reserve owner (.integer ty) count.toNat
        some ⟨(({next with frame := frame} : NState).release s).charge 1 1,none,false⟩
      else none
  | .append container ty expression => do
      let (next,owner) ← container.eval (s.charge 0 (container.nodes+expression.nodes+2))
      let (next,value) ← expression.eval next
      let frame ← next.frame.append owner ty value
      some ⟨(({next with frame := frame} : NState).release s).charge 1 1,none,false⟩
  | .appendRow container ty => do
      let (next,owner) ← container.eval (s.charge 0 (container.nodes+2))
      let frame ← next.frame.appendRow owner ty
      some ⟨(({next with frame := frame} : NState).release s).charge 1 1,none,false⟩
  | .assignRange target first last ty firstEnd lastEnd => do
      -- Three owner expressions, two iterator constructions and one call.
      let (next,destination) ← target.eval (s.charge 6 (target.nodes+7))
      let origin ← next.vectorSlot first
      let ending ← next.vectorSlot last
      let range ← next.frame.iteratorRange origin ending ty firstEnd lastEnd
      let frame ← next.frame.assign destination origin ty range
      some ⟨({next with frame := frame} : NState).release s,none,false⟩
  | .ret expression => do
      let (next,value) ← expression.eval s
      some ⟨(next.release s).charge 1 0,some (.scalar value),false⟩
  | .retVector slot => do
      let index ← s.vectorSlot slot
      let binding ← s.frame.bindings[index]?
      some ⟨s.charge 1 0,some (.vector binding.owner binding.element),false⟩
  | .check expression => do
      let (next,value) ← expression.eval s
      if value == 0 then none else some ⟨(next.release s).charge 1 0,none,false⟩
  | .sortVec container ty => do
      let (next,owner) ← container.eval (s.charge 0 (container.nodes+2))
      let frame ← next.frame.sortAll owner ty
      some ⟨(({next with frame := frame} : NState).release s).charge 1 1,none,false⟩
  | .sortPairs first second ty => do
      let (next,a) ← first.eval (s.charge 0 (first.nodes+second.nodes+3))
      let (next,b) ← second.eval next
      let frame ← next.frame.sortPairsAll a b ty
      some ⟨(({next with frame := frame} : NState).release s).charge 1 1,none,false⟩
  | .dedupVec container ty => do
      let (next,owner) ← container.eval (s.charge 0 (container.nodes+2))
      let frame ← next.frame.dedupAll owner ty
      some ⟨(({next with frame := frame} : NState).release s).charge 1 1,none,false⟩
  | .copyVector source ty writable => Proofs.CppCopyStatement.run s source ty writable
  | .retUnit => some ⟨s.charge 1 0,some .unit,false⟩

-- Leave a lexical scope. A returned vector root is first transferred to the
-- enclosing scope; then every remaining object of the inner scope is retired.
def NState.leave (outer inner : NState) (returned : Option Ret) : Option NState := do
  if outer.scalars.memory.length ≤ inner.scalars.memory.length ∧
      (inner.scalars.memory.take outer.scalars.memory.length).map CppState.Cell.type =
        outer.scalars.memory.map CppState.Cell.type then
    let moved ← match returned with
      | some (.vector owner element) =>
          inner.frame.transferRoot owner element (outer.scope+1) outer.scope
      | _ => some inner.frame
    let retired ← moved.retireScope (outer.scope+1)
    let scalars : CppState.State := {outer.scalars with
      memory := inner.scalars.memory.take outer.scalars.memory.length,
      work := inner.scalars.work+1,peak := max outer.scalars.peak inner.scalars.peak}
    let frame := {retired with bindings := retired.bindings.take outer.frame.bindings.length}
    some ((⟨scalars.observe 0,frame,outer.slots,outer.scope,max outer.peak inner.peak⟩ : NState).observe)
  else none

inductive Command where
  | primitive (statement : NStmt)
  | sequence (first rest : Command)
  | scope (body : Command)
  | branch (condition : NExpr) (yes no : Command)
  | whileLoop (condition : NExpr) (body : Command)
  | breakLoop
  -- A pure scalar call through the shared scalar program interpreter. Like
  -- `CppState.Stmt.invoke`, it appends one hidden read-only result variable;
  -- the arguments are expressions over scalar binding indices.
  | invokeScalar (program : Proofs.CppLoop.LoopProgram) (arguments : List Expr)

open Proofs.CppLoop in
def runFuel : Nat → Command → NState → Outcome NStep
  | 0,_,_ => .exhausted
  | fuel+1,command,s => match command with
    | .primitive statement => liftChecked (statement.run s)
    | .sequence first rest => do
        let step ← runFuel fuel first s
        if step.returned.isSome || step.breaking then pure step else runFuel fuel rest step.state
    | .scope body => do
        let step ← runFuel fuel body {s with scope := s.scope+1}
        let restored ← liftChecked (s.leave step.state step.returned)
        pure {step with state := restored}
    | .branch condition yes no => do
        let (next,value) ← liftChecked (condition.eval s)
        let released := next.release s
        if value == 0 then runFuel fuel no (released.charge 1 0)
        else runFuel fuel yes (released.charge 1 0)
    | .whileLoop condition body => do
        let (next,value) ← liftChecked (condition.eval s)
        let released := next.release s
        if value == 0 then pure ⟨released.charge 1 0,none,false⟩ else do
          let step ← runFuel fuel body (released.charge 1 0)
          if step.returned.isSome then pure step
          else if step.breaking then pure {step with breaking := false}
          else runFuel fuel (.whileLoop condition body) step.state
    | .breakLoop => pure ⟨s.charge 1 0,none,true⟩
    | .invokeScalar program arguments => do
        let values ← liftChecked (arguments.mapM s.scalars.evaluate)
        let result ← program.callFuel fuel s.scalars.memory
          (values.map fun value => CppState.Argument.value value.value)
        let scalars : CppState.State := {s.scalars with
          memory := result.memory ++ [⟨program.resultType,result.value⟩],
          bindings := s.scalars.bindings ++ [⟨s.scalars.memory.length,false⟩],
          work := s.scalars.work+(values.map (·.work)).sum+result.work+1,
          peak := max s.scalars.peak
            (s.scalars.memory.length-s.scalars.baseMemory+s.scalars.bindings.length+result.peak)}
        pure ⟨({s with scalars := scalars.observe 0,slots := s.slots ++ [.scalar s.scalars.bindings.length]} : NState).observe,none,false⟩

end Proofs.CppNestedProgram
