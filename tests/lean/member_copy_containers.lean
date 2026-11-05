namespace MemberCopyContainersRegression

open Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppNestedVectorStore Proofs.CppVectorOwnership
def i32 : Proofs.CppScalar.Ty := ⟨32,true,false⟩
def atom : Element := .integer i32
def row : Element := .vector atom
def baseFrame : Frame := ⟨⟨⟨[some ⟨atom,none,some 0,[]⟩,some ⟨row,none,some 1,[2]⟩,some ⟨atom,some 1,none,[]⟩,some ⟨(.vector row),none,some 1,[4]⟩,some ⟨row,some 3,none,[5]⟩,some ⟨atom,some 4,none,[]⟩]⟩,⟨[some ⟨0,[(Value.integer (19))],4,64,1⟩,some ⟨1,[.child 2],3,64,2⟩,some ⟨2,[(Value.integer (0)),(Value.integer (7))],4,64,3⟩,some ⟨3,[.child 4],2,64,4⟩,some ⟨4,[.child 5],3,64,5⟩,some ⟨5,[(Value.integer (91))],5,64,6⟩],7,0,0⟩⟩,[true,true,true,true,true,true],
  [⟨0,atom,true,.root 0⟩,⟨1,row,true,.root 1⟩,⟨1,row,false,.root 1⟩,⟨3,.vector row,true,.root 1⟩]⟩
def borrowed := (baseFrame.bindChild 3 row 0 true).bind fun p => p.1.bindChild p.2 atom 0 false
theorem check_1 : borrowed.isSome = true := by decide +kernel
def caller : NState := ⟨⟨[⟨i32,42⟩],[⟨0,true⟩],0,0,0⟩,(borrowed.map Prod.fst).getD baseFrame,
  [.vector 0,.vector 1,.vector 2,.vector 3,.vector 4,.vector 5,.scalar 0],1,0⟩
theorem check_2 : caller.frame.state.wellFormed = true := by decide +kernel
theorem check_3 : (caller.frame.resolve 4 row).isSome = true := by decide +kernel
theorem check_4 : (caller.frame.resolve 5 atom).isSome = true := by decide +kernel
def reference := caller.frame.elementRef 5 i32 0
theorem check_5 : reference.bind caller.frame.read = some 91 := by decide +kernel
def fields : List MemberCopy.Field := [.vector 0 i32 true,.scalar 6 i32 true,.vector 0 i32 false]
def copied : Option NState := match MemberCopy.runCopyFuel 4 caller fields with
  | .finished step => some step.state
  | _ => none
theorem check_6 : copied.isSome = true := by decide +kernel
theorem check_7 : copied.bind (fun s => s.frame.resolve 1 row) = caller.frame.resolve 1 row := by decide +kernel
theorem check_8 : copied.bind (fun s => s.frame.resolve 3 (.vector row)) = caller.frame.resolve 3 (.vector row) := by decide +kernel
theorem check_9 : copied.bind (fun s => s.frame.resolve 4 row) = caller.frame.resolve 4 row := by decide +kernel
theorem check_10 : copied.bind (fun s => s.frame.resolve 5 atom) = caller.frame.resolve 5 atom := by decide +kernel
theorem check_11 : copied.bind (fun s => reference.bind s.frame.read) = some 91 := by decide +kernel
theorem check_12 : (copied.bind (fun s => s.scalarCell 6 i32) |>.map (fun p => p.2.value)) = some 42 := by decide +kernel

theorem nested_headers_preserved :
    copied.bind (fun s => s.frame.resolve 4 row) = caller.frame.resolve 4 row ∧
    copied.bind (fun s => s.frame.resolve 5 atom) = caller.frame.resolve 5 atom := by
  decide +kernel
theorem captured_read_preserved : copied.bind (fun s => reference.bind s.frame.read) = some 91 := by
  decide +kernel
end MemberCopyContainersRegression

namespace MemberCopyContainersRegression
-- Reallocating the outer row invalidates its borrowed child header, while
-- the captured reference into the child's separate allocation remains live.
def staleCaller : Proofs.CppNestedProgram.NState :=
  {caller with frame := (caller.frame.reserve 4 row 6).getD caller.frame}

theorem borrowed_header_stale : staleCaller.frame.resolve 5 atom = none := by decide +kernel

theorem captured_read_still_live : reference.bind staleCaller.frame.read = some 91 := by decide +kernel

def staleCopied : Option Proofs.CppNestedProgram.NState :=
  match MemberCopy.runCopyFuel 4 staleCaller fields with
  | .finished step => some step.state
  | _ => none

theorem copy_after_header_invalidation : staleCopied.isSome = true := by decide +kernel

theorem captured_read_after_copy : staleCopied.bind (fun s => reference.bind s.frame.read) = some 91 := by
  decide +kernel
end MemberCopyContainersRegression
