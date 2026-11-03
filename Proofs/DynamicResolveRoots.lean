import Proofs.DynamicArguments

namespace Proofs.DynamicResolveRoots
open Proofs.CppScalar Proofs.CppVector Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.CppNestedFacts Proofs.CppRootModel Proofs.CppRowsFrame
open Proofs.MultiVecDynamic Proofs.DynamicExpr Proofs.DynamicRealizes

-- Only allocation metadata is used here. Values and row IDs remain arbitrary.
theorem root_object (f : Frame) (owner : Nat) (v : View) (model : Models f.state owner v) :
    ∃ buffer tag, f.object owner v.element = some (buffer,tag) ∧ f.state.forest.lookup owner = some tag ∧
      tag.parent = none ∧ tag.scope = some v.scope := by
  cases v with
  | flat ty sc values =>
    obtain ⟨buffer,found,_⟩ := model.buffer
    exact ⟨buffer,_,object_runs f owner _ buffer _ model.valid found model.tag rfl,model.tag,rfl,rfl⟩
  | rows ty sc ids epoch values =>
    obtain ⟨buffer,found,_,_⟩ := model.rows.buffer
    exact ⟨buffer,_,object_runs f owner _ buffer _ model.rows.valid found model.rows.rootTag rfl,model.rows.rootTag,rfl,rfl⟩

theorem resolve_root {params : List Parameter} {h : Heap} {m : Resources} {s : NState}
    (family : Family params h s.frame m) (p : Parameter) (member : p ∈ params)
    (expected : Element) (typed : p.element = expected) :
    ∃ buffer, s.frame.resolve p.slot expected = some (p.binding,buffer) := by
  obtain ⟨v,lookup,element,scope⟩ := family.views p member
  obtain ⟨buffer,tag,obj,found,parent,sc⟩ := root_object s.frame p.owner v (family.models p.owner v lookup)
  have object : s.frame.object p.owner expected = some (buffer,tag) := by rw [← typed,← element]; exact obj
  have maximum := maximum_runs s.frame p.owner p.owner p.maximum family.lengths
    (CppVectorOwnership.root_runs s.frame.state.forest p.owner tag found parent) (family.flags p member)
  exact ⟨buffer,CppNestedFacts.resolve_root s.frame p.slot expected p.binding p.scope buffer tag p.maximum
    (family.bindings p member) rfl typed object parent (by rw [scope] at sc; exact sc) maximum (family.permissions p member)⟩

end Proofs.DynamicResolveRoots
