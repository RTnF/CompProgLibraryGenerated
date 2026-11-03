namespace BeatsSlotEvalExamples
open Proofs.CppNestedProgram Proofs.CppScalar Proofs.CppMixedInvoke
open Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore Proofs.CppVectorOwnership
open Proofs.BeatsSlotCycle Proofs.CppSlotRename

def i32 : Ty := ⟨32,true,false⟩
def u64 : Ty := ⟨64,false,false⟩
def atom : Element := .integer i32

def flat : NState :=
  { scalars := ⟨[⟨i32,0⟩],[⟨0,true⟩],3,5,0⟩,
    frame := ⟨⟨⟨(List.range 16).map (fun _ => some ⟨atom,none,some 0,[]⟩)⟩,
      ⟨(List.range 16).map (fun i => some ⟨i,[.integer (i : Int),.integer (i+100 : Int)],3,64,0⟩),0,0,0⟩⟩,
      List.replicate 16 true,(List.range 16).map (fun i => ⟨i,atom,true,.root 0⟩)⟩,
    slots := (List.range 16).map Location.vector ++ [.scalar 0],scope := 0,peak := 7 }

def index : NExpr := .cast u64 (.variable i32 16)
def value : NExpr := .read i32 (.local 0) index
def size : NExpr := .size atom (.local 15)
def compound : NExpr := .binary i32 .add value size
def bad : NExpr := .read i32 (.local 0) (.literal u64 2)
def short : NExpr := .logical true (.literal i32 0) bad

#guard flat.frame.state.wellFormed
#guard (compound.eval (permute flat)).map (·.2) == some 3
#guard ((expr cycle compound).eval flat).map (·.2) == some 3
#guard (bad.eval (permute flat)) == none
#guard ((expr cycle bad).eval flat) == none
#guard (short.eval (permute flat)).map (·.2) == some 0
#guard ((expr cycle short).eval flat).map (·.2) == some 0
#guard (((expr cycle short).eval flat).map (fun p => (permute p.1,p.2))) == short.eval (permute flat)
#guard (((expr cycle compound).eval flat).map (fun p => (permute p.1,p.2))) == compound.eval (permute flat)
#guard ((expr cycle compound).eval flat).map (fun p => decide (p.1.scalars.work > flat.scalars.work)) == some true

def rows : NState :=
  { scalars := ⟨[],[],2,3,0⟩,
    frame := ⟨⟨⟨[some ⟨.vector atom,none,some 0,[1]⟩,some ⟨atom,some 0,none,[]⟩]⟩,
      ⟨[some ⟨0,[.child 1],1,64,0⟩,some ⟨1,[.integer 17,.integer 23],2,64,0⟩],0,0,0⟩⟩,
      [true,false],[⟨0,.vector atom,true,.root 0⟩]⟩,
    slots := List.replicate 16 (.vector 0),scope := 0,peak := 5 }

def row : Container := .row (.local 0) atom (.literal i32 0)
def rowValue : NExpr := .read i32 row (.literal u64 1)
def rowSize : NExpr := .size atom row

#guard rows.frame.state.wellFormed
#guard (rowValue.eval (permute rows)).map (·.2) == some 23
#guard (rowSize.eval (permute rows)).map (·.2) == some 2
#guard ((expr cycle rowValue).eval rows).map (fun p => p.1.frame.bindings.length) == some 2
#guard (((expr cycle rowValue).eval rows).map (fun p => (permute p.1,p.2))) == rowValue.eval (permute rows)
#guard (((container cycle row).eval rows).map (fun p => (permute p.1,p.2))) == row.eval (permute rows)

-- General theorems compare the whole resulting state, including counters and
-- newly added frame bindings, and include failed evaluations.
example (s : NState) (long : 16 ≤ s.slots.length) (e : NExpr) :
    ((expr cycle e).eval s).map (fun p => (permute p.1,p.2)) = e.eval (permute s) :=
  expr_eval_permute s long e

example (s : NState) (long : 16 ≤ s.slots.length) (e : NExpr) :
    (expr cycle e).eval s = none ↔ e.eval (permute s) = none :=
  expr_fault_permute s long e

example (s : NState) (c : Container) (t : NState) (owner : Nat)
    (ran : (container cycle c).eval s = some (t,owner)) : t.slots = s.slots :=
  (container_related c).slots s t owner ran

end BeatsSlotEvalExamples
