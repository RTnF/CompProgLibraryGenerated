import Proofs.Generated.UnionFindConstruction
import Proofs.DynamicOwnedControl
import Proofs.DynamicFlatSound
import Proofs.UfFieldsCounter

set_option maxRecDepth 4000

namespace Proofs.UfConstructionStage
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.DoublingNested
open Proofs.DynamicExpr Proofs.DynamicContents Proofs.DynamicOwnedState
open Proofs.MultiVecDynamic
open Proofs.CppState (Cell)

-- The stage starts after arguments are prepared. P may include the caller's
-- cells and bookkeeping padding; old logical heap/reference data are arbitrary.
def entry (P : List Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope n : Nat) : State :=
  ⟨⟨⟨P++[⟨i32,n⟩],[⟨P.length,true⟩],[.scalar 0]⟩,h⟩,params,owner,binding,scope⟩

def final (P : List Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope n : Nat) : State :=
  ⟨⟨⟨P++[⟨i32,n⟩,⟨i32,n⟩,⟨i32,n⟩],
      [⟨P.length,true⟩,⟨P.length+1,true⟩,⟨P.length+2,true⟩],
      [.scalar 0,.vector binding,.scalar 1,.scalar 2]⟩,
      putContents h owner (.flat i32 scope (List.replicate n (-1)))⟩,
    params++[⟨binding,owner,.integer i32,scope,true,true⟩],owner+1,binding+1,scope⟩

theorem cons_primitive (k : Nat) (stmt : NStmt) (rest : Command) (st next : State)
    (out : Proofs.DynamicOwnedControl.Step)
    (head : Proofs.DynamicOwnedControl.primitive stmt st = some ⟨next,none,false⟩)
    (tail : Proofs.DynamicOwnedControl.runFuel (k+1) rest next = .finished out) :
    Proofs.DynamicOwnedControl.runFuel (k+2) (.sequence (.primitive stmt) rest) st = .finished out := by
  change (do
    let p ← Proofs.CppLoop.liftChecked (Proofs.DynamicOwnedControl.primitive stmt st)
    if p.returned.isSome || p.breaking then pure p else
      Proofs.DynamicOwnedControl.runFuel (k+1) rest p.state) = .finished out
  rw [head]
  simpa [Proofs.CppLoop.liftChecked,bind,Proofs.CppLoop.Outcome.bind] using tail

theorem nat_i32 (n : Nat) (small : n < 2147483648) : i32.valid (n : Int) = true :=
  Proofs.VectorSumCall.i32_valid _ (by omega) (by omega)

theorem nat_u64 (n : Nat) (small : n < 2147483648) : u64.valid (n : Int) = true :=
  Proofs.DoublingNested.u64_valid_nat _ (by omega)

theorem nat_limit (n : Nat) (small : n < 2147483648) : n ≤ Proofs.CppVectorBindings.sizeLimit i32 := by
  change n ≤ 2305843009213693951
  omega

def vectorState (P : List Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope n : Nat) : State :=
  allocated (entry P h params owner binding scope n) (.integer i32) true
    (.flat i32 scope (List.replicate n (-1))) 1

def countState (P : List Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope n : Nat) : State :=
  let st := vectorState P h params owner binding scope n
  {st with core := ⟨DynamicStmt.declared st.core.locals i32 true n,st.core.contents⟩}

abbrev argument : NExpr := .variable i32 0
abbrev countExpr : NExpr := .cast u64 argument
abbrev valueExpr : NExpr := .unary i32 .neg (.literal i32 1)
abbrev checkExpr : NExpr := .binary ⟨1,false,true⟩ .ge argument (.literal i32 0)

def argLocals (P tail : List Cell) (n : Int) (bs : List Proofs.CppState.Binding)
    (slots : List Proofs.CppMixedInvoke.Location) : Locals :=
  ⟨P++⟨i32,n⟩::tail,⟨P.length,true⟩::bs,.scalar 0::slots⟩

theorem env_argument (P tail : List Cell) (n : Int) (bs : List Proofs.CppState.Binding)
    (slots : List Proofs.CppMixedInvoke.Location) (valid : i32.valid n = true) :
    environment (argLocals P tail n bs slots) 0 i32 = some n := by
  simp [argLocals,environment,valid]

theorem eval_argument (P tail : List Cell) (n : Int) (bs : List Proofs.CppState.Binding)
    (slots : List Proofs.CppMixedInvoke.Location) (valid : i32.valid n = true)
    (params : List Parameter) (h : ContentsHeap) :
    denote params (argLocals P tail n bs slots) h argument = some n := by
  rw [denote_scalar _ _ _ _ rfl]
  exact env_argument P tail n bs slots valid

theorem eval_count (P tail : List Cell) (n : Int) (bs : List Proofs.CppState.Binding)
    (slots : List Proofs.CppMixedInvoke.Location) (valid : i32.valid n = true)
    (unsigned : u64.valid n = true) (params : List Parameter) (h : ContentsHeap) :
    denote params (argLocals P tail n bs slots) h countExpr = some n := by
  rw [denote_scalar _ _ _ _ rfl]
  simp [NExpr.denote,env_argument P tail n bs slots valid,
    Ty.convert_of_valid u64 n unsigned]

theorem eval_check (P tail : List Cell) (n : Int) (bs : List Proofs.CppState.Binding)
    (slots : List Proofs.CppMixedInvoke.Location) (valid : i32.valid n = true)
    (positive : 0 ≤ n) (params : List Parameter) (h : ContentsHeap) :
    denote params (argLocals P tail n bs slots) h checkExpr = some 1 := by
  rw [denote_scalar _ _ _ _ rfl]
  have zero : i32.valid 0 = true := rfl
  simp [checkExpr,argument,NExpr.denote,env_argument P tail n bs slots valid,
    zero,binaryValue,Int.not_lt.mpr positive,Ty.convert]

theorem declare_value (st : State) (ty : Ty) (wr : Bool) (e : NExpr) (x y : Int)
    (evaluated : denote st.params st.core.locals st.core.contents e = some x)
    (converted : ty.convert x = some y) :
    Proofs.DynamicOwnedControl.primitive (.declare ty wr e) st =
      some ⟨{st with core := ⟨DynamicStmt.declared st.core.locals ty wr y,st.core.contents⟩},none,false⟩ := by
  simp [Proofs.DynamicOwnedControl.primitive,DynamicStmt.run,evaluated,converted]

theorem fill_step (P : List Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope n : Nat) (small : n < 2147483648) :
    Proofs.DynamicOwnedControl.primitive (.fillVector i32 true countExpr valueExpr) (entry P h params owner binding scope n) = some ⟨vectorState P h params owner binding scope n,none,false⟩ := by
  have nv : i32.valid (n : Int) = true := nat_i32 n small
  have uv : u64.valid (n : Int) = true := nat_u64 n small
  have uc := Ty.convert_of_valid u64 (n : Int) uv
  have one : i32.valid 1 = true := rfl
  have minus : i32.valid (-1) = true := rfl
  have minusConv : i32.convert (-1) = some (-1) := rfl
  have supported : Proofs.CppVectorBindings.supported i32 := by decide
  have limit : n ≤ Proofs.CppVectorBindings.sizeLimit i32 := nat_limit n small
  have evaluated : denote (entry P h params owner binding scope n).params (entry P h params owner binding scope n).core.locals (entry P h params owner binding scope n).core.contents countExpr = some (n : Int) := by
    simpa [argLocals,entry,countState,vectorState,entry,final,allocated,newParameter,
      DynamicConstructCore.appended,DynamicStmt.declared,List.append_assoc] using
      (eval_count P [] (n : Int) [] [] nv uv (entry P h params owner binding scope n).params (entry P h params owner binding scope n).core.contents)
  have filledValue : denote (entry P h params owner binding scope n).params
      (entry P h params owner binding scope n).core.locals (entry P h params owner binding scope n).core.contents valueExpr = some (-1) := by
    rw [denote_scalar _ _ _ _ rfl]
    rfl
  simp only [Proofs.DynamicOwnedControl.primitive,runConstruct,evaluated,filledValue,Option.bind_some]
  simp [supported,limit,minus,vectorState,entry,allocated,newParameter]

theorem count_step (P : List Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope n : Nat) (small : n < 2147483648) :
    Proofs.DynamicOwnedControl.primitive (.declare i32 true argument) (vectorState P h params owner binding scope n) = some ⟨countState P h params owner binding scope n,none,false⟩ := by
  have nv : i32.valid (n : Int) = true := nat_i32 n small
  have nc := Ty.convert_of_valid i32 (n : Int) nv
  have evaluated : denote (vectorState P h params owner binding scope n).params (vectorState P h params owner binding scope n).core.locals (vectorState P h params owner binding scope n).core.contents argument = some (n : Int) := by
    simpa [argLocals,vectorState,countState,vectorState,entry,final,allocated,newParameter,
      DynamicConstructCore.appended,DynamicStmt.declared,List.append_assoc] using
      (eval_argument P [] (n : Int) [] [.vector binding] nv (vectorState P h params owner binding scope n).params (vectorState P h params owner binding scope n).core.contents)
  exact declare_value _ i32 true argument n n evaluated nc

theorem n_step (P : List Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope n : Nat) (small : n < 2147483648) :
    Proofs.DynamicOwnedControl.primitive (.declare i32 true argument) (countState P h params owner binding scope n) = some ⟨final P h params owner binding scope n,none,false⟩ := by
  have nv : i32.valid (n : Int) = true := nat_i32 n small
  have nc := Ty.convert_of_valid i32 (n : Int) nv
  have evaluated : denote (countState P h params owner binding scope n).params (countState P h params owner binding scope n).core.locals (countState P h params owner binding scope n).core.contents argument = some (n : Int) := by
    simpa [argLocals,countState,countState,vectorState,entry,final,allocated,newParameter,
      DynamicConstructCore.appended,DynamicStmt.declared,List.append_assoc] using
      (eval_argument P [⟨i32,(n : Int)⟩] (n : Int) [⟨P.length+1,true⟩] [.vector binding,.scalar 1] nv (countState P h params owner binding scope n).params (countState P h params owner binding scope n).core.contents)
  have stateEq : {countState P h params owner binding scope n with core :=
      ⟨DynamicStmt.declared (countState P h params owner binding scope n).core.locals i32 true n,
        (countState P h params owner binding scope n).core.contents⟩} = final P h params owner binding scope n := by
    simp [countState,vectorState,entry,final,allocated,newParameter,DynamicConstructCore.appended,
      DynamicStmt.declared,List.append_assoc]
  rw [← stateEq]
  exact declare_value _ i32 true argument n n evaluated nc

theorem check_step (P : List Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope n : Nat) (small : n < 2147483648) :
    Proofs.DynamicOwnedControl.primitive (.check checkExpr) (final P h params owner binding scope n) = some ⟨final P h params owner binding scope n,none,false⟩ := by
  have nv : i32.valid (n : Int) = true := nat_i32 n small
  have zero : i32.valid 0 = true := rfl
  have evaluated : denote (final P h params owner binding scope n).params (final P h params owner binding scope n).core.locals (final P h params owner binding scope n).core.contents checkExpr = some 1 := by
    simpa [argLocals,final,countState,vectorState,entry,final,allocated,newParameter,
      DynamicConstructCore.appended,DynamicStmt.declared,List.append_assoc] using
      (eval_check P [⟨i32,(n : Int)⟩,⟨i32,(n : Int)⟩] (n : Int) [⟨P.length+1,true⟩,⟨P.length+2,true⟩] [.vector binding,.scalar 1,.scalar 2] nv (Int.natCast_nonneg n) (final P h params owner binding scope n).params (final P h params owner binding scope n).core.contents)
  simp [Proofs.DynamicOwnedControl.primitive,DynamicStmt.run,evaluated]

theorem sized_pure (P : List Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope n : Nat) (small : n < 2147483648) :
    Proofs.DynamicOwnedControl.runFuel 8
      Proofs.UnionFindConstructionInstance.UnionFind_construct1.body
      (entry P h params owner binding scope n) =
      .finished ⟨final P h params owner binding scope n,none,false⟩ := by
  have fill := fill_step P h params owner binding scope n small
  have dc := count_step P h params owner binding scope n small
  have dn := n_step P h params owner binding scope n small
  have checked := check_step P h params owner binding scope n small
  have last : Proofs.DynamicOwnedControl.runFuel 4 (.primitive .skip)
      (final P h params owner binding scope n) = .finished ⟨final P h params owner binding scope n,none,false⟩ := rfl
  change Proofs.DynamicOwnedControl.runFuel 8
    (.sequence (.primitive (.fillVector i32 true countExpr valueExpr))
      (.sequence (.primitive (.declare i32 true argument))
        (.sequence (.primitive (.declare i32 true argument))
          (.sequence (.primitive (.check checkExpr)) (.primitive .skip))))) (entry P h params owner binding scope n) = _
  exact cons_primitive 6 _ _ _ _ _ fill
    (cons_primitive 5 _ _ _ _ _ dc (cons_primitive 4 _ _ _ _ _ dn (cons_primitive 3 _ _ _ _ _ checked last)))

-- No successful stage execution is an input: the pure execution is proved above.
-- Realizes supplies the typed prepared state and valid ownership/resource frame.
theorem sized_stage (P : List Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope n : Nat) (small : n < 2147483648) (s : NState)
    (real : Realizes (entry P h params owner binding scope n) s) :
    ∃ out, CppNestedProgram.runFuel 8
      Proofs.UnionFindConstructionInstance.UnionFind_construct1.body s = .finished out ∧
      Realizes (final P h params owner binding scope n) out.state ∧
      out.returned = none ∧ out.breaking = false ∧
      Proofs.UfClassInvariant.Valid (List.replicate n (-1)) n (fun _ => 0) := by
  obtain ⟨out,ran,matched⟩ := Proofs.DynamicOwnedControl.sound 8 _ _ s real _
    (sized_pure P h params owner binding scope n small)
  exact ⟨out,ran,matched.state,matched.returned,matched.breaking,
    Proofs.UfClassInvariant.initial_valid n small⟩


-- Recover concrete receiver fields from the abstract simulation certificate.
theorem final_fields (P : List Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope n : Nat) (s : NState)
    (real : Realizes (final P h params owner binding scope n) s) :
    snapshot s = ⟨P++[⟨i32,n⟩,⟨i32,n⟩,⟨i32,n⟩],
      [⟨P.length,true⟩,⟨P.length+1,true⟩,⟨P.length+2,true⟩],
      [.scalar 0,.vector binding,.scalar 1,.scalar 2]⟩ ∧
    s.frame.bindings[binding]? = some ⟨owner,.integer i32,true,.root scope⟩ ∧
    s.frame.rootWritable[owner]? = some true ∧
    Proofs.CppRootModel.Flat s.frame.state owner i32 scope (List.replicate n (-1)) := by
  obtain ⟨heap,resources,family,erased⟩ := real.data.heap
  let q : Parameter := ⟨binding,owner,.integer i32,scope,true,true⟩
  have member : q ∈ (final P h params owner binding scope n).params := by
    simp [final,q]
  have found : Proofs.DynamicContents.eraseHeap heap owner =
      some (.flat i32 scope (List.replicate n (-1))) := by
    rw [erased]
    simp [final,putContents]
  have lifted := Proofs.DynamicFlatSound.flat_lift heap owner i32 scope (List.replicate n (-1)) found
  exact ⟨real.data.locals,family.bindings q member,family.flags q member,family.models owner _ lifted⟩


def defaultEntry (P : List Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope : Nat) : State :=
  ⟨⟨⟨P,[],[]⟩,h⟩,params,owner,binding,scope⟩

def defaultFinal (P : List Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope : Nat) : State :=
  ⟨⟨⟨P++[⟨i32,0⟩,⟨i32,0⟩],[⟨P.length,true⟩,⟨P.length+1,true⟩],
      [.vector binding,.scalar 0,.scalar 1]⟩,
      putContents h owner (.flat i32 scope [])⟩,
    params++[⟨binding,owner,.integer i32,scope,true,true⟩],owner+1,binding+1,scope⟩

theorem default_pure (P : List Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope : Nat) :
    Proofs.DynamicOwnedControl.runFuel 8
      Proofs.UnionFindConstructionInstance.UnionFind_construct0.body
      (defaultEntry P h params owner binding scope) =
      .finished ⟨defaultFinal P h params owner binding scope,none,false⟩ := by
  simp [Proofs.UnionFindConstructionInstance.UnionFind_construct0,
    Proofs.DynamicOwnedControl.runFuel,Proofs.DynamicOwnedControl.primitive,
    runConstruct,allocated,newParameter,defaultEntry,defaultFinal,DynamicConstructCore.appended,
    DynamicStmt.run,DynamicStmt.declared,denote,environment,NExpr.denote,NExpr.scalarOnly,
    Proofs.CppVectorBindings.supported,Ty.valid,Ty.convert,List.append_assoc,
    Proofs.CppLoop.liftChecked,bind,pure,Proofs.CppLoop.Outcome.bind]

theorem default_stage (P : List Cell) (h : ContentsHeap) (params : List Parameter)
    (owner binding scope : Nat) (s : NState)
    (real : Realizes (defaultEntry P h params owner binding scope) s) :
    ∃ out, CppNestedProgram.runFuel 8
      Proofs.UnionFindConstructionInstance.UnionFind_construct0.body s = .finished out ∧
      Realizes (defaultFinal P h params owner binding scope) out.state ∧
      out.returned = none ∧ out.breaking = false ∧
      Proofs.UfClassInvariant.Valid [] 0 (fun _ => 0) := by
  obtain ⟨out,ran,matched⟩ := Proofs.DynamicOwnedControl.sound 8 _ _ s real _
    (default_pure P h params owner binding scope)
  exact ⟨out,ran,matched.state,matched.returned,matched.breaking,
    Proofs.UfClassInvariant.initial_valid 0 (by decide)⟩

end Proofs.UfConstructionStage
