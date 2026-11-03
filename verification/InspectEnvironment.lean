import Lean

open Lean

def kind : ConstantInfo → String
  | .axiomInfo _ => "axiom"
  | .thmInfo _ => "theorem"
  | .defnInfo _ => "definition"
  | .opaqueInfo _ => "opaque"
  | .inductInfo _ => "inductive"
  | .ctorInfo _ => "constructor"
  | .recInfo _ => "recursor"
  | .quotInfo _ => "quotient"

def namesJson (names : Array Name) : Json :=
  toJson (names.map Name.toString)

partial def dumpClosure (env : Environment) (pending : List Name) (seen : NameSet) : IO Unit := do
  match pending with
  | [] => pure ()
  | name :: rest =>
    if seen.contains name then dumpClosure env rest seen
    else
      let some ci := env.find? name | throw (IO.userError s!"missing declaration {name}")
      let typeDeps := ci.type.getUsedConstants
      let body := ci.value? (allowOpaque := true)
      let bodyDeps := body.map (·.getUsedConstants) |>.getD #[]
      let ctorDeps := match ci with
        | .inductInfo i => i.ctors.toArray
        | _ => #[]
      let owner := (env.getModuleIdxFor? name).map
        (fun idx => env.header.moduleNames[idx.toNat]!) |>.getD .anonymous
      let fields := [("name", toJson name.toString), ("internal", toJson name.isInternalOrNum), ("kind", toJson (kind ci)),
        ("module", toJson owner.toString), ("type", toJson (reprStr ci.type)),
        ("levels", toJson (reprStr ci.levelParams)), ("unsafe", toJson ci.isUnsafe),
        ("type_dependencies", namesJson typeDeps),
        ("dependencies", namesJson (typeDeps ++ bodyDeps ++ ctorDeps)),
        ("body", toJson (if kind ci == "theorem" then "" else body.map reprStr |>.getD ""))]
      IO.println (Json.mkObj fields).compress
      -- depth-first: prepending the new work keeps each step linear (appending to `rest` copied the whole worklist)
      dumpClosure env ((typeDeps ++ bodyDeps ++ ctorDeps).toList ++ rest) (seen.insert name)

def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let module := args.headD "Proofs" |>.toName
  let env ← importModules #[{module}] {} (trustLevel := 0)
  let roots := if module == `Init then [`propext, `Classical.choice, `Quot.sound]
    else env.constants.toList.filterMap fun (name, _) =>
      let owner := (env.getModuleIdxFor? name).map
        (fun idx => env.header.moduleNames[idx.toNat]!) |>.getD .anonymous
      if (`Proofs).isPrefixOf owner then some name else none
  dumpClosure env (roots ++ (args.drop 1).map String.toName) {}
