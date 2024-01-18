import Dedukti.Trans
import Dedukti.Print
import Cli

open Dedukti

open Cli

def printDkEnv (dkEnv : Env) (printDeps : Bool) : IO Unit := do
  -- print Dedukti environment
  match (ExceptT.run (StateT.run (ReaderT.run (dkEnv.print (deps := printDeps)) {env := dkEnv}) default)) with
    | .error s => throw $ IO.userError s
    | .ok (_, s) =>
      let dkEnvString := "\n\n".intercalate s.out
      if not printDeps then
        IO.println dkEnvString
      else
        let dkPrelude := "#REQUIRE normalize.\n"
        let dkEnvString := dkPrelude ++ dkEnvString ++ "\n"
        IO.FS.writeFile "dk/out.dk" dkEnvString

def runTransCmd (p : Parsed) : IO UInt32 := do
  let path := ⟨"Test.lean"⟩
  let fileName := path.toString
  let onlyConsts? := p.flag? "only" |>.map fun setPathsFlag => 
    setPathsFlag.as! (Array String)

  -- run elaborator on Lean file
  let (leanEnv, success) ← Lean.Elab.runFrontend (← IO.FS.readFile path) default fileName default
  if not success then
    throw $ IO.userError $ "elab failed"

  let mut write := true
  if let some onlyConsts := onlyConsts? then
    IO.println s!"Only translating constants: {onlyConsts}"
    write := (not $ p.hasFlag "print") || p.hasFlag "write"

  let onlyConstsToTrans? := onlyConsts?.map fun onlyConsts => onlyConsts.map (·.toName)
  -- translate elaborated Lean environment to Dedukti
  let (_, {env := dkEnv, ..}) ← ((Trans.translateEnv onlyConstsToTrans? (transDeps := write)).toIO { options := default, fileName := "", fileMap := default } {env := leanEnv} {env := leanEnv}
)

  -- let write := if let some _ := onlyConsts? then (p.hasFlag "write") else true -- REPORT why does this not work?

  if write then
    printDkEnv dkEnv true

  if p.hasFlag "print" then
    printDkEnv dkEnv false

  return 0

def transCmd : Cmd := `[Cli|
  transCmd VIA runTransCmd; ["0.0.1"]
  "Translate from Lean to Dedukti."

  FLAGS:
    p, print;               "Print translation of specified constants to standard output (relevant only with '-o ...')."
    w, write;               "Also write translation of specified constants (with dependencies) to file (relevant only with '-p')."
    o, only : Array String; "Only translate the specified constants and their dependencies."

  ARGS:
    input : String;         "Input .lean file."

  -- SUBCOMMANDS:
  --   installCmd;
  --   testCmd

  -- The EXTENSIONS section denotes features that
  -- were added as an external extension to the library.
  -- `./Cli/Extensions.lean` provides some commonly useful examples.
  EXTENSIONS:
    author "rish987"
]

def main (args : List String) : IO UInt32 := do
  transCmd.validate args
