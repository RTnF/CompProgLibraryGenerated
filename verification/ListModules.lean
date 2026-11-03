import Lean

open Lean

-- Print every module of the import closure of the module named by the first argument.
def main (args : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{module := args.headD "Init" |>.toName}] {} (trustLevel := 0)
  for name in env.header.moduleNames do
    IO.println name.toString
