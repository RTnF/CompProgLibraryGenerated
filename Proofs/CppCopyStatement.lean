import Proofs.CppFrameCopyCore
import Proofs.CppNestedProgram

namespace Proofs.CppCopyStatement
open Proofs.CppScalar Proofs.CppNestedProgram Proofs.CppNestedVectorBindings
open Proofs.CppFrameCopy Proofs.CppVectorOwnership

-- Prototype for the new NStmt branch, to be integrated below Container.eval.
-- Resolve before release: a row expression may have allocated a temporary
-- binding. Copy after release: the fresh binding must survive this expression.
theorem run_of_steps (s next : NState) (source : Container) (ty : Ty) (writable : Bool)
    (index target : Nat) (binding : Binding) (buffer : Proofs.CppVector.Buffer Proofs.CppNestedVectorStore.Value)
    (frame : Frame)
    (evaluated : source.eval s = some (next,index))
    (resolved : next.frame.resolve index (.integer ty) = some (binding,buffer))
    (copied : copyOwner (next.release s).frame binding.owner ty (next.release s).scope writable = some (frame,target)) :
    run s source ty writable = some ⟨({next.release s with
      frame := frame,slots := (next.release s).slots++[.vector target]} : NState).charge 1 0,none,false⟩ := by
  simp [run,evaluated,resolved,copied]

-- The statement interpreter uses exactly the already proved copy operation.
theorem statement_run (s : NState) (source : Container) (ty : Ty) (writable : Bool) :
    (NStmt.copyVector source ty writable).run s = run s source ty writable := rfl

end Proofs.CppCopyStatement
