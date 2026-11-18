import Lean.CoreM
import Lean.Replay

open Lean

unsafe def main (args : List String) : IO Unit := do
  let [root, reviewedPath] := args
    | throw (IO.userError "expected a project module and a reviewed dependency list")
  initSearchPath (← findSysroot)
  let reviewed := (← IO.FS.lines reviewedPath).foldl
    (fun names line => names.insert line.toName) ({} : NameSet)
  let isProject := fun name => (`Proofs).isPrefixOf name
  Lean.withImportModules #[{module := root.toName}] {} fun env => do
    let imports := env.header.moduleNames.filter (!isProject ·)
    unless imports.all reviewed.contains do
      throw (IO.userError "project imports a dependency outside the reviewed module list")
    let declarations := env.constants.map₁.fold (init := {}) fun result name info =>
      match env.getModuleIdxFor? name with
      | some idx =>
        if isProject env.header.moduleNames[idx.toNat]! then result.insert name info else result
      | none => result
    if declarations.isEmpty then
      throw (IO.userError "project replay has no declarations")
    Lean.withImportModules (imports.map fun module => {module}) {} fun seed => do
      unless seed.header.moduleNames.all (fun name => !isProject name && reviewed.contains name) do
        throw (IO.userError "replay seed contains a project or unreviewed module")
      discard <| seed.toKernelEnv.replay declarations
    IO.println s!"Kernel replay passed for {declarations.size} project declarations"
