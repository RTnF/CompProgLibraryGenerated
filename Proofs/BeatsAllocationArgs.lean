import Proofs.BeatsAllocationLayout
import Proofs.SegmentTreeBeatsCall

namespace Proofs.BeatsAllocationArgs
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.MultiVecDynamic
open Proofs.BeatsAllocation Proofs.BeatsAllocationLayout Proofs.BeatsExec Proofs.BeatsRep Proofs.BeatsModel

def slot (st : Proofs.DynamicOwnedState.State) (i : Nat) : Nat :=
  if i < 15 then st.core.locals.slots.length+i else 0
def binding (st : Proofs.DynamicOwnedState.State) (p : Parameter) (i : Nat) : Nat :=
  if i < 15 then st.nextBinding+i else p.slot
def owner (st : Proofs.DynamicOwnedState.State) (p : Parameter) (i : Nat) : Nat :=
  if i < 15 then st.nextOwner+i else p.owner
def scope (st : Proofs.DynamicOwnedState.State) (p : Parameter) (i : Nat) : Nat :=
  if i < 15 then st.scope else p.scope
def buffer (st : Proofs.DynamicOwnedState.State) (n : Nat)
    (input : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value) (i : Nat) :=
  if i < 15 then fieldBuffer st n i else input

def initial (n : Nat) : BS :=
  let z := List.replicate (8*n+8) (0 : Int)
  ⟨z,z,z,z,z,z,z,z,List.replicate (8*n+8) INF,z,z,
    List.replicate 256 0,List.replicate 256 0,List.replicate 256 0,z⟩

theorem initial_field (n i : Nat) (bound : i < 15) :
    VVB (initial n) i = List.replicate (fieldCount n i) (fieldValue i) := by
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 := by omega
  rcases cases with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst i <;> rfl

theorem initial_valid (n : Nat) : ValidOK (initial n) := by
  constructor <;> intro w member <;> simp only [initial,List.mem_replicate] at member <;>
    obtain ⟨_,rfl⟩ := member <;> decide

theorem initial_capacities (n : Nat) : Capacities (initial n) (8*n+8) 256 := by
  constructor <;> simp only [initial,List.length_replicate,Nat.le_refl]

theorem replicate_zero (n j : Nat) : (List.replicate n (0 : Int)).getD j 0 = 0 := by
  simp only [List.getD,List.getElem?_replicate]
  split <;> rfl

theorem initial_fresh (n : Nat) : Proofs.BeatsSeparate.BFreshS (8*n+8) 256 (initial n) := by
  refine ⟨initial_valid n,initial_capacities n,
    by simp only [initial,List.length_replicate,Nat.le_refl],
    by simp only [initial,List.length_replicate,Nat.le_refl],
    replicate_zero _,replicate_zero _,replicate_zero _,replicate_zero _,replicate_zero _,
    replicate_zero _,replicate_zero _,replicate_zero _,?_,replicate_zero _,replicate_zero _⟩
  intro j bound
  change j < (List.replicate (8*n+8) INF).length at bound
  have bounded : j < 8*n+8 := by simpa only [List.length_replicate] using bound
  change (List.replicate (8*n+8) INF).getD j 0 = INF
  simp only [List.getD,List.getElem?_replicate_of_lt bounded,Option.getD_some]

theorem ctor_field (n : Nat) (a : List Int) (i : Nat) (bound : i < 15) :
    VVA a (initial n) i = List.replicate (fieldCount n i) (fieldValue i) := by
  simpa only [VVA,ite_eq_right (show i ≠ 15 by omega)] using initial_field n i bound

theorem field_type (i : Nat) (bound : i < 15) : cty i = fieldTy i := by
  simp only [cty,fieldTy,show i ≠ 15 by omega,or_false]

theorem owner_distinct (st : Proofs.DynamicOwnedState.State) (p : Parameter)
    (fresh : p.owner < st.nextOwner) :
    ∀ j k, j < 16 → k < 15 → j ≠ k → owner st p j ≠ owner st p k := by
  intro j k _ hk different
  by_cases field : j < 15
  · simp only [owner,ite_eq_left field,ite_eq_left hk]
    omega
  · simp only [owner,ite_eq_right field,ite_eq_left hk]
    omega

-- The input parameter is the readonly reference already prepared for the
-- constructor; its maximum permission may still be writable.
theorem cvecs {st : Proofs.DynamicOwnedState.State} {p : Parameter} {a : List Int}
    (h : Input st p a) (n : Nat) (length : a.length = n) (small : 4*n < 2147483648)
    (s : NState) (real : Proofs.DynamicOwnedState.Realizes (states st n 15) s)
    (buf : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value)
    (fields : ∀ j, j < 15 → Proofs.MatMulPrepare.VOKG s (fieldTy j)
      (st.core.locals.slots.length+j) (st.nextBinding+j) (st.nextOwner+j) st.scope true true (fieldBuffer st n j))
    (input : Proofs.MatMulPrepare.VOKG s Proofs.IntSim.s64 0 p.slot p.owner p.scope p.writable p.maximum buf)
    (readonly : p.writable = false) (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit Proofs.IntSim.s64) :
    CVecs s (slot st) (binding st p) (owner st p) (scope st p) p.maximum (buffer st n buf) (VVA a (initial n)) := by
  have facts := input_argument h n 15 s real buf input.vfound input.strict input.base
  have fieldFacts := fun j bound => field_argument st n s real
    (fun k hk => (fields k hk).vfound) input.strict input.base j bound
  constructor
  · intro i bound
    by_cases field : i < 15
    · simpa only [slot,binding,owner,scope,buffer,ite_eq_left field,field_type i field,cw,
        decide_eq_true field] using fields i field
    · have last : i = 15 := by omega
      subst i
      simpa [slot,binding,owner,scope,buffer,cty,cw,readonly] using input
  · exact owner_distinct st p h.fresh
  · intro i bound
    by_cases field : i < 15
    · rw [ctor_field n a i field]
      simp only [buffer,ite_eq_left field,fieldBuffer,List.map_replicate]
    · have last : i = 15 := by omega
      subst i
      exact facts.2.2.1
  · intro i bound
    by_cases field : i < 15
    · simpa only [buffer,ite_eq_left field,field_type i field] using (fieldFacts i field).2.1
    · have last : i = 15 := by omega
      subst i
      exact facts.2.1
  · intro i bound
    by_cases field : i < 15
    · simp only [buffer,ite_eq_left field,fieldBuffer,field_type i field]
    · have last : i = 15 := by omega
      subst i
      exact limit
  · intro i bound
    by_cases field : i < 15
    · simp only [buffer,owner,ite_eq_left field,fieldBuffer]
    · have last : i = 15 := by omega
      subst i
      exact facts.2.2.2
  · intro i bound
    by_cases field : i < 15
    · rw [ctor_field n a i field,List.length_replicate]
      unfold fieldCount
      split <;> omega
    · have last : i = 15 := by omega
      subst i
      simpa only [VVA_get15,length] using (show n < 18446744073709551616 by omega)

theorem prefix_cvecs {st : Proofs.DynamicOwnedState.State} {p : Parameter} {a : List Int}
    (h : Input st p a) (n : Nat) (length : a.length = n) (small : 4*n < 2147483648)
    (s : NState) (real : Proofs.DynamicOwnedState.Realizes st s)
    (strict : ∀ owner c, s.frame.state.forest.context owner = some c → c ≤ s.scope)
    (base : s.scalars.baseMemory ≤ s.scalars.memory.length)
    (buf : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value)
    (stored : s.frame.state.storage.lookup p.owner = some buf)
    (readonly : p.writable = false) (limit : buf.limit = Proofs.CppVectorBindings.sizeLimit Proofs.IntSim.s64) :
    ∃ out, CppNestedProgram.runFuel 16 (fillPrefix 0 15) s = .finished ⟨out,none,false⟩ ∧
      Proofs.DynamicOwnedState.Realizes (states st n 15) out ∧
      out.frame.state.storage.work = s.frame.state.storage.work+storageWork n 0 15 ∧
      CVecs out (slot st) (binding st p) (owner st p) (scope st p) p.maximum (buffer st n buf) (VVA a (initial n)) := by
  obtain ⟨out,ran,after,_,work,fields,input⟩ := prefix_arguments h n length small s real strict base buf stored
  exact ⟨out,ran,after,work,cvecs h n length small out after buf fields input readonly limit⟩

end Proofs.BeatsAllocationArgs
