import Proofs.UfConstructedReceiver
import Proofs.UfSameReady
import Proofs.UfSizeReady
import Proofs.UfUniteReady
import Proofs.UfCounterReady

namespace Proofs.UfReceiverState
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedVectorBindings
open Proofs.CppVector Proofs.CppNestedVectorStore Proofs.UfClassInvariant Proofs.UfCompression
open Proofs.UfFindCall Proofs.CppNestedEval
open Proofs.DoublingNested (i32)

structure Layout where
  vectorSlot : Nat
  vectorBinding : Nat
  owner : Nat
  scope : Nat
  countSlot : Nat
  nSlot : Nat
  deriving DecidableEq, Repr

structure Inv (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (buf : Buffer Value) (cb nb : Proofs.CppState.Binding) : Prop where
  ok : VOKWF s layout.vectorSlot layout.vectorBinding layout.owner layout.scope buf
  items : buf.items = ps.map Value.integer
  bufferValid : buf.Valid (accepts (.integer i32))
  limit : buf.limit = Proofs.CppVectorBindings.sizeLimit i32
  owner : buf.owner = layout.owner
  math : Valid ps count rank
  countCell : s.scalarCell layout.countSlot i32 = some (cb,⟨i32,count⟩)
  writable : cb.writable = true
  nCell : s.scalarCell layout.nSlot i32 = some (nb,⟨i32,ps.length⟩)
  different : nb.address ≠ cb.address

def Represents (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat) : Prop :=
  ∃ buf cb nb, Inv s layout ps count rank buf cb nb

def nExpr (layout : Layout) : NExpr := .variable i32 layout.nSlot

def arguments (layout : Layout) : List NArgument :=
  [.vectorReference layout.vectorSlot,.scalarReference layout.countSlot,.value (nExpr layout)]

theorem literal_value (x : Int) (valid : i32.valid x = true) (s : NState) :
    (NExpr.literal i32 x).denote (envOf s) = some x := by simp [NExpr.denote,valid]

theorem Inv.n_value {s layout ps count rank buf cb nb} (inv : Inv s layout ps count rank buf cb nb) :
    (nExpr layout).denote (envOf s) = some (ps.length : Int) := by
  simp [nExpr,NExpr.denote,envOf,inv.nCell]

theorem Inv.readonly_transition {s layout ps count rank buf cb nb}
    (inv : Inv s layout ps count rank buf cb nb) (out : NState) (vec : List Int)
    (math : Valid vec count rank) (length : vec.length = ps.length)
    (ready : ∃ next, VOKWF out layout.vectorSlot layout.vectorBinding layout.owner layout.scope next ∧
      next.items = vec.map Value.integer ∧ next.Valid (accepts (.integer i32)) ∧
      next.limit = Proofs.CppVectorBindings.sizeLimit i32 ∧ next.owner = layout.owner)
    (cells : ∀ slot ty, out.scalarCell slot ty = s.scalarCell slot ty) :
    Represents out layout vec count rank := by
  obtain ⟨next,ok,items,valid,limit,owner⟩ := ready
  refine ⟨next,cb,nb,ok,items,valid,limit,owner,math,?_,inv.writable,?_,inv.different⟩
  · rw [cells]; exact inv.countCell
  · rw [cells,length]; exact inv.nCell

theorem root_step (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Represents s layout ps count rank) (a : Nat) (inside : a < ps.length) :
    ∃ fuel out, ∃ (r : Nat) (vec : List Int),
      Proofs.UnionFindCandidateInstance.UnionFind_root.callFuel fuel s
        (arguments layout ++ [.value (.literal i32 a)]) = .finished (out,.scalar (r : Int)) ∧
      Compressed ps vec a r ∧ Represents out layout vec count rank := by
  obtain ⟨buf,cb,nb,inv⟩ := represented
  have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
  obtain ⟨init,fuel,out,r,vec,prep,call,compressed,forest,oldRun,post,ready,cells⟩ :=
    Proofs.UfRootReady.root_call_ready s inv.ok cb count inv.countCell inv.writable ps rank inv.math.forest
      inv.items inv.math.length inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) a
      rfl rfl rfl rfl inv.n_value (literal_value a av s) inside
  exact ⟨fuel,out,r,vec,call,compressed,
    inv.readonly_transition out vec (inv.math.compressed compressed) compressed.length ready cells⟩

theorem getter_step (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Represents s layout ps count rank) :
    ∃ fuel out, Proofs.UnionFindCandidateInstance.UnionFind_num_groups.callFuel fuel s (arguments layout) =
      .finished (out,.scalar count) ∧ Represents out layout ps count rank := by
  obtain ⟨buf,cb,nb,inv⟩ := represented
  obtain ⟨init,fuel,out,prep,call,bindings,base,post,ready,cells⟩ :=
    Proofs.UfCounterReady.num_groups_call_ready s inv.ok cb count inv.countCell inv.writable ps rank inv.math
      inv.items inv.bufferValid inv.limit inv.owner (nExpr layout) rfl rfl inv.n_value
  rw [← inv.math.count] at call
  exact ⟨fuel,out,call,inv.readonly_transition out ps inv.math rfl ready cells⟩

theorem same_step (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Represents s layout ps count rank) (a b : Nat) (ha : a < ps.length) (hb : b < ps.length) :
    ∃ fuel out, ∃ (r1 r2 : Nat) (middle vec : List Int),
      Proofs.UnionFindCandidateInstance.UnionFind_same.callFuel fuel s
        (arguments layout ++ [.value (.literal i32 a),.value (.literal i32 b)]) =
          .finished (out,.scalar (if r1=r2 then 1 else 0)) ∧
      Compressed ps middle a r1 ∧ Compressed middle vec b r2 ∧
      (r1=r2 ↔ Proofs.UfFieldsSame.Connected ps a b) ∧ Represents out layout vec count rank := by
  obtain ⟨buf,cb,nb,inv⟩ := represented
  have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
  have bv := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by have h := inv.math.length; omega)
  obtain ⟨init,fuel,out,r1,r2,middle,vec,prep,call,c1,c2,forest,connected,post,ready,cells⟩ :=
    Proofs.UfSameReady.same_call_ready s inv.ok cb count inv.countCell inv.writable ps rank inv.math.forest
      inv.items inv.math.length inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) (.literal i32 b)
      a b rfl rfl rfl rfl rfl rfl inv.n_value (literal_value a av s) (literal_value b bv s) ha hb
  have rep := inv.readonly_transition out vec ((inv.math.compressed c1).compressed c2)
    (c2.length.trans c1.length) ready cells
  exact ⟨fuel,out,r1,r2,middle,vec,call,c1,c2,connected,rep⟩

theorem size_step (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Represents s layout ps count rank) (a : Nat) (inside : a < ps.length) :
    ∃ fuel out, ∃ (r : Nat) (vec : List Int), Proofs.UnionFindCandidateInstance.UnionFind_size.callFuel fuel s
      (arguments layout ++ [.value (.literal i32 a)]) =
        .finished (out,.scalar ((component ps a).length : Int)) ∧ Compressed ps vec a r ∧ Represents out layout vec count rank := by
  obtain ⟨buf,cb,nb,inv⟩ := represented
  have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
  obtain ⟨init,fuel,out,r,w,vec,prep,call,found,negative,compressed,forest,weights,post,ready,cells⟩ :=
    Proofs.UfSizeReady.size_call_ready s inv.ok cb count inv.countCell inv.writable ps rank inv.math.forest
      inv.math.weights inv.items inv.math.length inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) a
      rfl rfl rfl rfl inv.n_value (literal_value a av s) inside
  have result := inv.math.size_value found negative
  rw [← component_eq_members ps a r compressed.reach ⟨w,found,negative⟩] at result
  rw [result] at call
  exact ⟨fuel,out,r,vec,call,compressed,
    inv.readonly_transition out vec (inv.math.compressed compressed) compressed.length ready cells⟩

theorem unite_step (s : NState) (layout : Layout) (ps : List Int) (count : Int) (rank : Nat → Nat)
    (represented : Represents s layout ps count rank) (a b : Nat) (ha : a < ps.length) (hb : b < ps.length) :
    ∃ fuel out, ∃ (r1 r2 : Nat) (middle two vec : List Int) (nextRank : Nat → Nat),
      Proofs.UnionFindCandidateInstance.UnionFind_unite.callFuel fuel s
        (arguments layout ++ [.value (.literal i32 a),.value (.literal i32 b)]) =
          .finished (out,.scalar (Proofs.UfUniteCall.uniteX two r1 r2 : Int)) ∧
      Compressed ps middle a r1 ∧ Compressed middle two b r2 ∧
      vec = Proofs.UfUniteCall.uniteVec two r1 r2 ∧ (r1=r2 ↔ Proofs.UfFieldsSame.Connected ps a b) ∧
      vec.length = ps.length ∧ Represents out layout vec (Proofs.UfFieldsUnite.countAfter count r1 r2) nextRank := by
  obtain ⟨buf,cb,nb,inv⟩ := represented
  have av := Proofs.VectorSumCall.i32_valid (a : Int) (by omega) (by have h := inv.math.length; omega)
  have bv := Proofs.VectorSumCall.i32_valid (b : Int) (by omega) (by have h := inv.math.length; omega)
  obtain ⟨init,fuel,out,r1,r2,middle,two,vec,prep,call,c1,c2,finalEq,newValid,connected,
      bindings,base,post,ready,counter,other,aliases⟩ :=
    Proofs.UfUniteReady.unite_call_ready s inv.ok cb count inv.countCell inv.writable ps rank inv.math
      inv.items inv.bufferValid inv.limit inv.owner (nExpr layout) (.literal i32 a) (.literal i32 b)
      a b rfl rfl rfl rfl rfl rfl inv.n_value (literal_value a av s) (literal_value b bv s) ha hb
  obtain ⟨nextRank,math⟩ := newValid
  obtain ⟨next,ok,items,valid,limit,owner⟩ := ready
  have length : vec.length = ps.length := by
    have len1 := c1.length
    have len2 := c2.length
    rw [finalEq]
    unfold Proofs.UfUniteCall.uniteVec
    split_ifs <;> (try simp only [List.length_set]) <;> omega
  have savedN := other layout.nSlot i32 nb ⟨i32,ps.length⟩ inv.nCell inv.different
  refine ⟨fuel,out,r1,r2,middle,two,vec,nextRank,call,c1,c2,finalEq,connected,length,next,cb,nb,ok,items,valid,limit,owner,
    math,counter,inv.writable,?_,inv.different⟩
  rw [length]
  exact savedN

def layoutOf (caller : NState) : Layout :=
  ⟨caller.slots.length,caller.frame.bindings.length,caller.frame.state.storage.objects.length,
    caller.scope,caller.slots.length+1,caller.slots.length+2⟩

theorem initialized_rep (caller out : NState) (n : Nat)
    (initialized : Proofs.UfConstructionExport.Initialized caller out (List.replicate n (-1)) n n)
    (ok : VOKWF out caller.slots.length caller.frame.bindings.length caller.frame.state.storage.objects.length caller.scope
      (Proofs.UfConstructedReceiver.buffer caller.frame.state.storage.objects.length n))
    (math : Valid (List.replicate n (-1)) n (fun _ => 0)) :
    Represents out (layoutOf caller) (List.replicate n (-1)) n (fun _ => 0) := by
  obtain ⟨tag,found,owner,payload⟩ := wellFormed_buffer out.frame.state caller.frame.state.storage.objects.length
    (Proofs.UfConstructedReceiver.buffer caller.frame.state.storage.objects.length n) ok.valid ok.vfound
  have tagEq := Option.some.inj (found.symm.trans ok.vtag)
  subst tag
  refine ⟨Proofs.UfConstructedReceiver.buffer caller.frame.state.storage.objects.length n,
    ⟨caller.scalars.memory.length,true⟩,⟨caller.scalars.memory.length+1,true⟩,ok,?_,payload.1,rfl,rfl,math,
    initialized.2.2.1,rfl,?_,?_⟩
  · simp [Proofs.UfConstructedReceiver.buffer,List.map_replicate]
  · simpa [layoutOf] using initialized.2.2.2.1
  · simp

theorem construct_sized (caller : NState) (heap : Proofs.CppRootModel.Heap)
    (valid : caller.frame.state.wellFormed = true) (models : Proofs.CppRootModel.HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length)
    (en : NExpr) (n : Nat) (small : n < 2147483648) (scalar : en.scalarOnly = true)
    (type : en.resultType = i32) (value : en.denote (envOf caller) = some (n : Int)) :
    ∃ out, Proofs.UnionFindConstructionInstance.UnionFind_construct1.constructFuel 8 caller [.value en]
      (Proofs.UfConstructionExport.vectorField true) (.integer i32) (Proofs.UfConstructionExport.fields true) =
        .finished (out,Proofs.CppConstructorFinish.reference caller 2) ∧
      Represents out (layoutOf caller) (List.replicate n (-1)) n (fun _ => 0) := by
  obtain ⟨out,ran,initialized,ok,math⟩ := Proofs.UfConstructedReceiver.sized_ready caller heap valid models lengths strict base en n small scalar type value
  exact ⟨out,ran,initialized_rep caller out n initialized ok math⟩

theorem construct_default (caller : NState) (heap : Proofs.CppRootModel.Heap)
    (valid : caller.frame.state.wellFormed = true) (models : Proofs.CppRootModel.HeapModels caller.frame.state heap)
    (lengths : caller.frame.rootWritable.length = caller.frame.state.forest.objects.length)
    (strict : ∀ owner scope, caller.frame.state.forest.context owner = some scope → scope ≤ caller.scope)
    (base : caller.scalars.baseMemory ≤ caller.scalars.memory.length) :
    ∃ out, Proofs.UnionFindConstructionInstance.UnionFind_construct0.constructFuel 8 caller []
      (Proofs.UfConstructionExport.vectorField false) (.integer i32) (Proofs.UfConstructionExport.fields false) =
        .finished (out,Proofs.CppConstructorFinish.reference caller 2) ∧
      Represents out (layoutOf caller) [] 0 (fun _ => 0) := by
  obtain ⟨out,ran,initialized,ok,math⟩ := Proofs.UfConstructedReceiver.default_ready caller heap valid models lengths strict base
  exact ⟨out,ran,initialized_rep caller out 0 initialized ok math⟩

end Proofs.UfReceiverState
