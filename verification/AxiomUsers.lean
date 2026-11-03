import Lean

open Lean

-- Usage: AxiomUsers MODULE ALLOWED_AXIOM...
-- Prints "AXIOM <- CONSTANT @ MODULE[ unsafe]" for every constant of the import closure of MODULE whose type or value
-- mentions an axiom outside the allowed list. Any dependence on an axiom needs a constant that mentions it
-- directly, so a user list without constants of Mathlib and its packages proves that nothing there depends on
-- an unreviewed axiom.
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := args.headD "Init" |>.toName}] {} (trustLevel := 0)
  let allowed : List Name := (args.drop 1).map String.toName
  let mut axioms : NameSet := {}
  for (name, ci) in env.constants.toList do
    if ci matches .axiomInfo _ then axioms := axioms.insert name
  for (name, ci) in env.constants.toList do
    let used := ci.type.getUsedConstants ++ (ci.value? (allowOpaque := true) |>.map (·.getUsedConstants) |>.getD #[])
    for u in used do
      if axioms.contains u && !allowed.contains u then
        let owner := (env.getModuleIdxFor? name).map (fun idx => env.header.moduleNames[idx.toNat]!) |>.getD .anonymous
        IO.println s!"{u} <- {name} @ {owner}{if ci.isUnsafe then " unsafe" else ""}"
