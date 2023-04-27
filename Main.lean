import Dedukti.Trans
import Dedukti.Print

open Dedukti

def main (args : List String) : IO UInt32 := do
  let path := ⟨"Test.lean"⟩

  -- run elaborator on Lean file
  let (leanEnv, success) ← Lean.Elab.runFrontend (← IO.FS.readFile path) default path.toString default
  if not success then
    throw $ IO.userError $ "elab failed"

  if false then
    IO.println s!"number of constants: {leanEnv.constants.size}"
    leanEnv.constants.forM (fun _ const => do
      IO.println s!"definition: {repr const}"
    )

  -- translate elaborated Lean environment to Dedukti
  let (_, {env := dkEnv}) := (StateT.run (ReaderT.run (transEnv leanEnv) default) default)

  if false then
    dkEnv.constMap.forM (fun _ const => do
      IO.println s!"definition: {repr const}"
    )

  -- print Dedukti environment
  let dkEnvString ← match (ExceptT.run (StateT.run (ReaderT.run (dkEnv.print) {env := dkEnv}) default)) with
    | .error s => throw $ IO.userError s
    | .ok (_, s) => pure $ "\n\n".intercalate s.out
  let dkEnvString := dkEnvString ++ "\n"

  IO.FS.writeFile "out.dk" dkEnvString

  return 0
