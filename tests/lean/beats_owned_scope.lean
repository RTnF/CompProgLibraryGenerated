namespace BeatsOwnedScopeExamples
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedHoare Proofs.CppNestedVectorBindings
open Proofs.CppNestedVectorStore Proofs.CppNestedSim Proofs.CppNestedEval
open Proofs.MultiVec Proofs.QuotientFrame Proofs.StraightLine

-- The stronger old scope premise excludes a root allocated in the current
-- scope; the owned-body theorem instead permits mv.sc = current scope + 1.
example (mv : MV) (vv : Nat → List Int) (bb : Nat → Proofs.CppVector.Buffer Value)
    (wk : Nat) (s : NState) (fw : FWM mv vv bb wk s.frame) (owner : Nat)
    (current : s.frame.state.forest.context owner = some s.scope) : ¬ mv.sc ≤ s.scope := by
  have := fw.strict owner s.scope current
  omega

example (mv : MV) (vv : Nat → List Int) (bb : Nat → Proofs.CppVector.Buffer Value)
    (wk : Nat) (s : NState) (fw : FWM mv vv bb wk s.frame) (boundary : mv.sc = s.scope+1) :
    ∀ owner, s.frame.state.forest.context owner ≠ some (s.scope+1) := fw.fresh_owned (by omega)

example (mv : MV) (w : Nat → Bool) (permissions : ∀ k, w k = true → mv.wV k = true ∧ mv.flag k = true)
    (cmd : Command) (writes : WrM w cmd = true) (fuel : Nat) (ps : PS) (vv : Nat → List Int) (r : PRM)
    (executed : pexecM mv fuel cmd ps vv = some r)
    (B sc SPB TPB W wk : Nat) (bb : Nat → Proofs.CppVector.Buffer Value) (s : NState)
    (qs : QS s [] B sc ps.mem ps.bs (slN mv.nv ps.bs.length)) (fw : FWM mv vv bb wk s.frame)
    (resources : Cq SPB TPB W s) (base : B ≤ ps.mem.length) (live : ps.mem.length+ps.bs.length ≤ SPB+B)
    (need : r.need ≤ SPB+B) (boundary : mv.sc = sc+1) (space : mv.L0+1 ≤ TPB) :
    RunsTo cmd s (QpostM mv r B sc SPB TPB W wk) :=
  soundM_owned mv w permissions cmd writes fuel ps vv r executed s qs fw resources base live need (by omega) space

-- A nested scalar scope must leave the vector owned by its outer/current
-- scope alive. This exercises the actual leave/retirement semantics.
def ty : Ty := ⟨32,true,false⟩
def current : NState :=
  {scalars := ⟨[],[],0,0,0⟩,
   frame := ⟨⟨⟨[some ⟨.integer ty,none,some 0,[]⟩]⟩,
     ⟨[some ⟨0,[.integer 7],1,Proofs.CppVectorBindings.sizeLimit ty,0⟩],0,0,0⟩⟩,
     [true],[⟨0,.integer ty,true,.root 0⟩]⟩,
   slots := [.vector 0],scope := 0,peak := 0}
def inner : NState := {(current.declared ty true 9) with scope := 1}
#guard current.frame.state.wellFormed
#guard (current.leave inner none).isSome
#guard (current.leave inner none).bind (fun s => s.frame.state.forest.context 0) == some 0
#guard (current.leave inner none).bind (fun s => s.frame.state.storage.lookup 0) == current.frame.state.storage.lookup 0
#guard (current.leave inner none).map (·.slots) == some [.vector 0]

end BeatsOwnedScopeExamples
