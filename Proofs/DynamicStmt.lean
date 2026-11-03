import Proofs.DynamicExprDerive

namespace Proofs.DynamicStmt
open Proofs.CppScalar Proofs.CppMixedInvoke Proofs.CppNestedProgram
open Proofs.CppVectorOwnership Proofs.MultiVecDynamic Proofs.DynamicContents Proofs.DynamicExpr

structure State where
  locals : Locals
  contents : ContentsHeap

structure Step where
  state : State
  returned : Option Int := none

def declared (l : Locals) (ty : Ty) (writable : Bool) (value : Int) : Locals :=
  ⟨l.memory ++ [⟨ty,value⟩],l.bindings ++ [⟨l.memory.length,writable⟩],l.slots ++ [.scalar l.bindings.length]⟩

def scalarCell (l : Locals) (slot : Nat) (ty : Ty) : Option (Proofs.CppState.Binding × Proofs.CppState.Cell) := do
  let .scalar idx ← l.slots[slot]? | none
  let binding ← l.bindings[idx]?
  let cell ← l.memory[binding.address]?
  if cell.type = ty ∧ ty.valid cell.value then some (binding,cell) else none

def assigned (l : Locals) (binding : Proofs.CppState.Binding) (cell : Proofs.CppState.Cell) (value : Int) : Locals :=
  {l with memory := l.memory.set binding.address ⟨cell.type,value⟩}

def parameter (params : List Parameter) (l : Locals) (slot : Nat) : Option Parameter := do
  let .vector rb ← l.slots[slot]? | none
  params.find? (fun p => p.slot == rb)

def mutableRoot (params : List Parameter) (st : State) (slot : Nat) (expected : Element) : Option Parameter := do
  let p ← parameter params st.locals slot
  let view ← st.contents p.owner
  if p.writable = true ∧ p.maximum = true ∧ p.element = expected ∧
      view.element = expected ∧ view.scope = p.scope then some p else none

-- Pure execution keeps contents and scalar locals, not capacities or epochs.
-- Unsupported vector construction/copy operations still fail explicitly.
def run (params : List Parameter) : NStmt → State → Option Step
  | .skip,st => some ⟨st,none⟩
  | .declare ty writable e,st => do
      let v ← denote params st.locals st.contents e
      let value ← ty.convert v
      some ⟨⟨declared st.locals ty writable value,st.contents⟩,none⟩
  | .assign slot ty e,st => do
      let v ← denote params st.locals st.contents e
      let (binding,cell) ← scalarCell st.locals slot ty
      if binding.writable then
        let value ← ty.convert v
        some ⟨⟨assigned st.locals binding cell value,st.contents⟩,none⟩
      else none
  | .ret e,st => do
      let v ← denote params st.locals st.contents e
      some ⟨st,some v⟩
  | .check e,st => do
      let v ← denote params st.locals st.contents e
      if v ≠ 0 then some ⟨st,none⟩ else none
  | .appendRow (.local slot) ty,st => do
      let p ← mutableRoot params st slot (.vector (.integer ty))
      let heap ← DynamicContents.appendRoot st.contents p.owner ty
      some ⟨{st with contents := heap},none⟩
  | .append (.row (.local slot) (.integer element) idx) ty value,st => do
      let p ← mutableRoot params st slot (.vector (.integer ty))
      let i ← denote params st.locals st.contents idx
      let x ← denote params st.locals st.contents value
      if element = ty ∧ 0 ≤ i then
        let heap ← DynamicContents.appendChild st.contents p.owner ty i.toNat x
        some ⟨{st with contents := heap},none⟩
      else none
  | _,_ => none

end Proofs.DynamicStmt
