namespace DisjointSetGetterCallFuelChecks
open Proofs.CppNestedProgram DisjointSetGetterChecks
#guard (match Proofs.Generated.DisjointSetMethods.DisjointSet_getNum_callFuel 2
    (initial [-2,0,-1,-1] 3 4) ⟨0,[1,2]⟩ [] with
  | .finished (out,result) => result == .scalar 3 && out.scalars.memory.map (·.value) == [4,3]
  | _ => false)
#guard (match Proofs.Generated.DisjointSetMethods.DisjointSet_getNum_callFuel 2
    (initial [] 0 0) ⟨0,[1,2]⟩ [] with
  | .finished (_,result) => result == .scalar 0 | _ => false)
#guard (match Proofs.Generated.DisjointSetMethods.DisjointSet_getNum_callFuel 2
    (initial [] 1 4) ⟨0,[1,2]⟩ [] with
  | .finished (_,result) => result == .scalar 1 | _ => false)
example (s : NState) (e : NExpr) (v : Int) (rest : Command)
    (scalar : e.scalarOnly = true) (value : e.denote (Proofs.CppNestedEval.envOf s) = some v) :
    ∃ out, Proofs.CppNestedProgram.runFuel 2 (.sequence (.primitive (.ret e)) rest) s =
      .finished ⟨out,some (.scalar v),false⟩ ∧ Proofs.CppNestedEval.Core s out ∧
      out.work ≤ s.work+e.nodes+1 :=
  Proofs.CppScalarGetterCall.body_runs s e rest v scalar value
end DisjointSetGetterCallFuelChecks
