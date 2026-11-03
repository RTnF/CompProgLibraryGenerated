import Proofs.DynamicForestEffects

namespace Proofs.DynamicPhysicalEffects
open Proofs.CppScalar Proofs.CppVectorOwnership Proofs.CppNestedVectorStore Proofs.CppNestedVectorBindings
open Proofs.CppNestedProgram Proofs.CppNestedStmt Proofs.CppNestedSim Proofs.CppNestedEval
open Proofs.DynamicForestEffects

-- Old owner flags retain their positions; added children may add new flags.
def Authority (before after : Frame) : Prop :=
  (∃ extra, after.rootWritable = before.rootWritable ++ extra) ∧ Preserves before.state.forest after.state.forest

def Change (before after : NState) : Prop := Authority before.frame after.frame ∧ after.scope = before.scope

theorem Authority.refl (f : Frame) : Authority f f := ⟨⟨[],by simp⟩,Preserves.refl _⟩
theorem Authority.same {f g : Frame} (forest : g.state.forest = f.state.forest) (flags : g.rootWritable = f.rootWritable) : Authority f g :=
  ⟨⟨[],by simp [flags]⟩,by rw [forest]; exact Preserves.refl _⟩
theorem Authority.trans {a b c : Frame} (ab : Authority a b) (bc : Authority b c) : Authority a c := by
  obtain ⟨⟨x,hx⟩,forest1⟩ := ab
  obtain ⟨⟨y,hy⟩,forest2⟩ := bc
  exact ⟨⟨x ++ y,by rw [hy,hx,List.append_assoc]⟩,forest1.trans forest2⟩

theorem Authority.flag {before after : Frame} (effect : Authority before after) (owner : Nat) (value : Bool)
    (found : before.rootWritable[owner]? = some value) : after.rootWritable[owner]? = some value := by
  obtain ⟨extra,same⟩ := effect.1
  rw [same,List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

theorem Authority.absent {before after : Frame} (effect : Authority before after) (scope : Nat)
    (absent : NoScope before.state.forest scope) : NoScope after.state.forest scope := effect.2 scope absent

theorem Change.refl (s : NState) : Change s s := ⟨Authority.refl _,rfl⟩
theorem Change.trans {a b c : NState} (ab : Change a b) (bc : Change b c) : Change a c :=
  ⟨ab.1.trans bc.1,bc.2.trans ab.2⟩

theorem charge (s : NState) (work temporary : Nat) : Change s (s.charge work temporary) := Change.refl s
theorem release (s before : NState) : Change s (s.release before) := ⟨Authority.refl _,rfl⟩
theorem declared (s : NState) (ty : Ty) (wr : Bool) (x : Int) : Change s (s.declared ty wr x) := ⟨Authority.refl _,rfl⟩

theorem goodF {s t : NState} {w p : Nat} (good : GoodF s t w p) : Change s t :=
  ⟨Authority.same (congrArg State.forest good.1) good.2.1,good.2.2.2.1⟩

theorem updated (f : Frame) (owner : Nat) (old : Proofs.CppVector.Buffer Value) (r : Proofs.CppVector.Result Value Unit) :
    Authority f (f.updated owner old r) := Authority.same rfl rfl

theorem appendRow (f next : Frame) (slot : Nat) (ty : Ty) (run : f.appendRow slot ty = some next) : Authority f next := by
  unfold Frame.appendRow at run
  obtain ⟨pair,_,rest⟩ := Proofs.DynamicResultValid.bind_some _ _ _ run
  obtain ⟨binding,buffer⟩ := pair
  cases wr : binding.writable with
  | false => simp [wr] at rest
  | true =>
    simp only [wr,ite_true] at rest
    obtain ⟨state,appended,same⟩ := Proofs.DynamicResultValid.bind_some _ _ _ rest
    have equal := Option.some.inj same
    subst next
    obtain ⟨old,tag,r,valid,_,found,_,_,rfl⟩ := Proofs.CppAppendRow.appendRow_inv f.state state binding.owner ty appended
    exact ⟨⟨[false],rfl⟩,append_preserves f.state.forest binding.owner tag (.integer ty) (wellFormed_parts f.state valid).2.1 found⟩

-- This derives the effects of the canonical statement from its actual run;
-- it does not impose a layout or a capacity reservation on the parent.
theorem appendRoot_stmt (s : NState) (slot : Nat) (ty : Ty) (out : NStep)
    (run : (NStmt.appendRow (.local slot) ty).run s = some out) : Change s out.state := by
  cases loc : s.vectorSlot slot with
  | none =>
    have missing : (Container.local slot).eval (s.charge 0 ((Container.local slot).nodes+2)) = none := by
      have loc' : (s.charge 0 ((Container.local slot).nodes+2)).vectorSlot slot = none := loc
      simp [Container.eval,loc']
    simp [NStmt.run,missing] at run
  | some rb =>
    have eval := eval_local (s.charge 0 ((Container.local slot).nodes+2)) slot rb (by simpa [NState.vectorSlot] using loc)
    cases step : s.frame.appendRow rb ty with
    | none => simp [NStmt.run,eval,step] at run
    | some frame =>
      simp only [NStmt.run,eval,Bind.bind,Option.bind] at run
      change (s.frame.appendRow rb ty).bind _ = _ at run
      simp only [step,Option.bind_some] at run
      have same := Option.some.inj run
      subst out
      exact ⟨appendRow s.frame frame rb ty step,rfl⟩

-- Scalar updates and buffer updates can be interleaved with temporary
-- expression bindings without changing authority or ownership contexts.
theorem scalars (s : NState) (sc : Proofs.CppState.State) : Change s {s with scalars := sc} := ⟨Authority.refl _,rfl⟩

theorem update_state (s : NState) (owner : Nat) (old : Proofs.CppVector.Buffer Value)
    (r : Proofs.CppVector.Result Value Unit) : Change s {s with frame := s.frame.updated owner old r} :=
  ⟨updated s.frame owner old r,rfl⟩

theorem updated_statement {s t : NState} {w p : Nat} (good : GoodF s t w p)
    (owner : Nat) (old : Proofs.CppVector.Buffer Value) (r : Proofs.CppVector.Result Value Unit)
    (work temporary : Nat) :
    Change s ((({t with frame := t.frame.updated owner old r} : NState).release s).charge work temporary) :=
  (goodF good).trans ((update_state t owner old r).trans ((release _ s).trans (charge _ work temporary)))

theorem restored {caller callee : NState} (effects : Authority caller.frame callee.frame) :
    Authority caller.frame (Proofs.DynamicFinish.restored caller callee).frame := effects

end Proofs.DynamicPhysicalEffects
