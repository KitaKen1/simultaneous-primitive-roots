import Main

/-!
Operational component driver. The caller prepends the Comparator library to LEAN_PATH,
because Lean4export also has a module named Main. This file alone executes no builds.
The Linux wrapper appends an explicit call to `run`; it must not use `lean --run`.
The upstream Comparator functions and the final complete comparison are unchanged.
-/

namespace SPRComponentBuildHarness

def componentTargets (document : Lean.Json) (component : String) :
    Except String (Array Lean.Name) := do
  let version ← document.getObjValAs? Nat "schema_version"
  if version != 1 then
    throw "Unsupported component target schema"
  let components ← document.getObjValAs? (Array Lean.Json) "components"
  let some entry := components.find? (fun entry =>
      (entry.getObjValAs? String "name").toOption == some component)
    | throw s!"Unknown component: {component}"
  let targets ← entry.getObjValAs? (Array String) "targets"
  if targets.isEmpty then
    throw "A component must name at least one target"
  return targets.map String.toName

def buildComponents (targets : Array Lean.Name) : Comparator.M Unit := do
  for target in targets do
    Comparator.safeLakeBuild target

/-- Build only the configured component roots using the unchanged sandboxed build call. -/
def run (configPath targetsPath : System.FilePath) (component : String) : IO Unit := do
  let contents ← IO.FS.readFile configPath
  let cfg : Comparator.Config ← IO.ofExcept <|
    Lean.FromJson.fromJson? <| ← IO.ofExcept <| Lean.Json.parse contents
  let document ← IO.ofExcept <| Lean.Json.parse (← IO.FS.readFile targetsPath)
  let targets ← IO.ofExcept <| componentTargets document component
  Comparator.M.run (buildComponents targets) cfg

end SPRComponentBuildHarness
