namespace ConstructorMultiFinishExamples
open Proofs.CppNestedProgram Proofs.CppNestedVectorBindings Proofs.CppConstructorRoots
open Proofs.CppRootModel Proofs.CppConstructorMultiFinish Proofs.CppVectorOwnership
open ConstructorRootsExamples

def caller : NState := ⟨⟨[⟨i32,5⟩],[⟨0,true⟩],7,0,1⟩,
  {frame with bindings := [⟨0,.integer i32,false,.root 2⟩]},[.scalar 0,.vector 0],2,2⟩
def b1 : Binding := ⟨1,.integer i32,false,.root 3⟩
def b16 : Binding := ⟨16,.vector (.integer i32),true,.root 3⟩
def callee : NState := ⟨⟨[⟨i32,9⟩,⟨i32,17⟩],[⟨1,true⟩],20,0,2⟩,
  {frame with bindings := frame.bindings ++ [b1]},[.vector 2,.vector 1,.scalar 0],3,4⟩
def vectors : List VectorField := [⟨0,.integer i32⟩,⟨1,.vector (.integer i32)⟩]
def scalars : List Proofs.CppConstructorFinish.ScalarField := [⟨2,i32⟩]
def values : List Proofs.CppConstructorFinish.ScalarValue := [(⟨i32,17⟩,true)]
def bindings : List Binding := [b1,b16]
def finished := finish caller callee vectors scalars
def out : NState := (finished.getD (caller,⟨[],[]⟩)).1

#guard captureVectors callee vectors == some bindings
#guard finished.isSome
#guard (finished.map Prod.snd) == some (reference caller 2 1)
#guard out.scalars.memory == [⟨i32,9⟩,⟨i32,17⟩]
#guard out.scalars.bindings == [⟨0,true⟩,⟨1,true⟩]
#guard out.scalarCell 0 i32 == some (⟨0,true⟩,⟨i32,9⟩)
#guard out.scalarCell 4 i32 == some (⟨1,true⟩,⟨i32,17⟩)
#guard out.vectorSlot 2 == some 1
#guard out.vectorSlot 3 == some 2
#guard out.frame.resolve 1 (.integer i32) == some
  (⟨1,.integer i32,false,.root 2⟩,flatBuffer 1)
#guard out.frame.resolve 2 (.vector (.integer i32)) == some
  (⟨16,.vector (.integer i32),true,.root 2⟩,⟨16,[.child 17],1,64,11⟩)
#guard out.frame.bindings.take caller.frame.bindings.length == caller.frame.bindings
#guard out.frame.rootWritable == frame.rootWritable
#guard out.frame.state.storage.lookup 17 == frame.state.storage.lookup 17
#guard out.frame.state.storage.lookup 18 == none
#guard out.scope == caller.scope
#guard out.scalars.baseMemory == caller.scalars.baseMemory
#guard captureVector callee ⟨2,.integer i32⟩ == none
#guard captureVector callee ⟨0,.vector (.integer i32)⟩ == none
#guard captureVector callee ⟨10,.integer i32⟩ == none
#guard finish caller callee [⟨0,.integer i32⟩,⟨0,.integer i32⟩] [] == none
#guard finish caller {callee with scope := 2} vectors scalars == none
#guard finish caller {callee with scalars := {callee.scalars with memory := []}} vectors scalars == none
#guard finish caller {callee with scalars := {callee.scalars with memory := [⟨⟨64,true,false⟩,9⟩,⟨i32,17⟩]}}
  vectors scalars == none
def overgranted : NState := {callee with
  frame := {callee.frame with bindings := [⟨1,.integer i32,true,.root 3⟩]},
  slots := [.vector 0]}
#guard captureVector overgranted ⟨0,.integer i32⟩ == none
def childHeader : NState := {callee with
  frame := {callee.frame with bindings := [⟨17,.integer i32,true,.child ⟨16,11,0⟩⟩]},
  slots := [.vector 0]}
#guard (childHeader.frame.resolve 0 (.integer i32)).isSome
#guard captureVector childHeader ⟨0,.integer i32⟩ == none

-- Scalar-only, vector-only, and empty retained layouts use the same finish.
def scalarOnly := finish caller callee [] scalars
def vectorOnly := finish caller callee vectors []
#guard (scalarOnly.map Prod.snd) == some (reference caller 0 1)
#guard (scalarOnly.map (fun result => result.1.scalars.memory)) == some [⟨i32,9⟩,⟨i32,17⟩]
#guard (scalarOnly.bind (fun result => result.1.frame.state.storage.lookup 16)) == none
#guard (vectorOnly.map Prod.snd) == some (reference caller 2 0)
#guard (vectorOnly.map (fun result => result.1.scalars.memory)) == some [⟨i32,9⟩]
#guard (finish caller callee [] []).isSome

theorem matchedVectors : VectorFieldsMatch callee vectors bindings :=
  ⟨⟨2,flatBuffer 1,by decide +kernel,by decide +kernel,rfl,rfl⟩,
    ⟨⟨1,⟨16,[.child 17],1,64,11⟩,by decide +kernel,by decide +kernel,rfl,rfl⟩,True.intro⟩⟩
theorem matchedScalars : Proofs.CppConstructorFinish.FieldsMatch callee scalars values :=
  ⟨⟨⟨1,true⟩,by decide +kernel,rfl⟩,True.intro⟩
example := finish_ok caller callee vectors scalars bindings values roots
  rfl (by decide) rfl matchedVectors matchedScalars rfl (by decide)
  (by decide +kernel) models
example := restored_vector caller callee result bindings values 1 b16 (by decide)
example := restored_scalar caller callee result bindings values 0 ⟨i32,17⟩ true
  (by decide) (by decide) (by decide)

end ConstructorMultiFinishExamples
