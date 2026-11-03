namespace UfReadCallMapping
open Proofs.CppMoveContext Proofs.CppMoveReadReceiver Proofs.CppConstructorFinish
open Proofs.CppNestedProgram Proofs.CppNestedCall Proofs.DoublingNested
open Proofs.CppMoveReceiverPermissions Proofs.UfReadPrograms

example : UnionFindPublicCompat.Methods.UnionFind_size_1_2 = sizeProgram := rfl
example : UnionFindPublicCompat.Methods.UnionFind_same_2_2 = sameProgram := rfl
example : UnionFindPublicCompat.Methods.UnionFind_num_groups_0_2 = counterProgram := rfl

example (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32) (e : NExpr) (v : Int) :
    UnionFindPublicCompat.UnionFind_size_1_2_arguments object [.value e] =
      some (readArguments s object receiver [(e,v)]) := by
  simpa [readArguments,Proofs.CppMoveReceiverResolve.arguments] using
    UnionFindPublicCompat.UnionFind_size_1_2_arguments_of_fields object [.value e]
      receiver.counter.slot receiver.size.slot receiver.fields rfl

example (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32)
    (ea eb : NExpr) (a b : Int) :
    UnionFindPublicCompat.UnionFind_same_2_2_arguments object [.value ea,.value eb] =
      some (readArguments s object receiver [(ea,a),(eb,b)]) := by
  simpa [readArguments,Proofs.CppMoveReceiverResolve.arguments] using
    UnionFindPublicCompat.UnionFind_same_2_2_arguments_of_fields object [.value ea,.value eb]
      receiver.counter.slot receiver.size.slot receiver.fields rfl

example (s : Context) (object : ObjectRef) (receiver : ReadReceiver s object i32) :
    UnionFindPublicCompat.UnionFind_num_groups_0_2_arguments object [] =
      some (readArguments s object receiver []) := by
  simpa [readArguments,Proofs.CppMoveReceiverResolve.arguments] using
    UnionFindPublicCompat.UnionFind_num_groups_0_2_arguments_of_fields object []
      receiver.counter.slot receiver.size.slot receiver.fields rfl
end UfReadCallMapping
