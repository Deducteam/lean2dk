import Dedukti.Trans
import Dedukti.Print

open Dedukti

def main (args : List String) : IO UInt32 := do
  let path := ⟨"Test.lean"⟩
  let fileName := path.toString

  -- run elaborator on Lean file
  let (leanEnv, success) ← Lean.Elab.runFrontend (← IO.FS.readFile path) default fileName default
  if not success then
    throw $ IO.userError $ "elab failed"

  if false then
    IO.println s!"number of constants: {leanEnv.constants.size}"
    leanEnv.constants.forM (fun _ const => do
      IO.println s!"definition: {repr const}"
    )

  -- translate elaborated Lean environment to Dedukti
  let (_, {env := dkEnv, ..}) ← ((Trans.translateEnv leanEnv).toIO { options := default, fileName := "", fileMap := default } {env := leanEnv}
  -- Prod.fst <$> x.toIO { options := ppCtx.opts, currNamespace := ppCtx.currNamespace, openDecls := ppCtx.openDecls, fileName := "<PrettyPrinter>", fileMap := default }
  --                     { env := ppCtx.env, ngen := { namePrefix := `_pp_uniq } }
)

  if false then
    dkEnv.constMap.forM (fun _ const => do
      IO.println s!"definition: {repr const}"
    )

  -- print Dedukti environment
  let dkEnvString ← match (ExceptT.run (StateT.run (ReaderT.run (dkEnv.print) {env := dkEnv}) default)) with
    | .error s => throw $ IO.userError s
    | .ok (_, s) => pure $ "\n\n".intercalate s.out
  let dkPrelude := "#REQUIRE normalize.\n"
  let dkEnvString := dkPrelude ++ dkEnvString ++ "\n"

  IO.FS.writeFile "dk/out.dk" dkEnvString

  return 0
