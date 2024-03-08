import Dedukti.Trans
import Dedukti.Print
import Cli
import Lean.Replay
import Dedukti.Util

open Dedukti

abbrev RED        := "\x1b[31m"
abbrev YELLOW     := "\x1b[1;33m"
abbrev BLUE       := "\x1b[0;34m"
abbrev LIGHT_BLUE := "\x1b[1;34m"
abbrev LIGHT_GRAY := "\x1b[1;36m"
abbrev GREEN      := "\x1b[0;32m"
abbrev PURPLE     := "\x1b[0;35m"
abbrev NOCOLOR    := "\x1b[0m"

def eprintColor (color s : String) := IO.eprintln s!"{color}{s}{NOCOLOR}"
def printColor (color s : String) := IO.println s!"{color}{s}{NOCOLOR}"

open Cli

def printDkEnv (dkEnv : Env) (only? : Option $ Lean.NameSet) : IO Unit := do
  let printDeps := if let some _ := only? then false else true

  -- print Dedukti environment
  match (ExceptT.run (StateT.run (ReaderT.run (dkEnv.print (deps := printDeps)) {env := dkEnv}) default)) with
    | .error s => throw $ IO.userError s
    | .ok (_, s) =>
      let dkEnvString := "\n\n".intercalate s.out
      if let some only := only? then
        for name in only do
          let maxConstPrint := 400 -- FIXME make "constant"
          let constString := s.printedConsts.find! (fixLeanName name)
          let constString := if constString.length > maxConstPrint then constString.extract ⟨0⟩ ⟨maxConstPrint⟩ ++ "..." else constString
          IO.println $ "\n" ++ constString
      else
        let dkPrelude := "#REQUIRE normalize.\n"
        let dkEnvString := dkPrelude ++ dkEnvString ++ "\n"
        IO.FS.writeFile "dk/out.dk" dkEnvString

def getCheckableConstants (env : Lean.Environment) (consts : Lean.NameSet) (printErr := false) : IO Lean.NameSet := do
  let mut onlyConstsToTrans : Lean.NameSet := default

  -- constants that should be skipped on account of already having been typechecked
  let mut skipConsts : Lean.NameSet := default
  -- constants that should throw an error if encountered on account of having previously failed to typecheck
  let mut errConsts : Lean.NameSet := default
  let mut modEnv := (← Lean.mkEmptyEnvironment).setProofIrrelevance false
  for const in consts do
    try
      if not $ skipConsts.contains const then
        let mut (_, {map := map, ..}) ← ((Deps.namedConstDeps const).toIO { options := default, fileName := "", fileMap := default } {env} {env})
        let mapConsts := map.fold (init := default) fun acc const _ => acc.insert const

        let erredConsts : Lean.NameSet := mapConsts.intersectBy (fun _ _ _ => default) errConsts
        if erredConsts.size > 0 then
          throw $ IO.userError "Encountered untypecheckable constant dependencies: {erredConsts}."

        let skippedConsts : Lean.NameSet := mapConsts.intersectBy (fun _ _ _ => default) skipConsts
        for skipConst in skippedConsts do
          map := map.erase skipConst

        modEnv ← modEnv.replay map
        skipConsts := skipConsts.union mapConsts -- TC success, so want to skip in future runs (already in environment)
      onlyConstsToTrans := onlyConstsToTrans.insert const
    catch
    | e =>
      if printErr then
        IO.eprintln s!"Error typechecking constant '{const}': {e.toString}"
      errConsts := errConsts.insert const

  pure onlyConstsToTrans

def runTransCmd (p : Parsed) : IO UInt32 := do
  let path := ⟨p.positionalArg! "input" |>.value⟩
  let fileName := path.toString
  let moduleName ← Lean.moduleNameOfFileName path .none 
  IO.println s!"\n{BLUE}>> Translation file: {YELLOW}{fileName}{NOCOLOR}"
  let onlyConsts? := p.flag? "only" |>.map fun setPathsFlag => 
    setPathsFlag.as! (Array String)

  IO.println s!"\n{BLUE}>> Elaborating... {YELLOW}\n"
  -- run elaborator on Lean file
  Lean.initSearchPath (← Lean.findSysroot)
  let (env, success) ← Lean.Elab.runFrontend (← IO.FS.readFile path) default fileName moduleName
  if not success then
    throw $ IO.userError $ "elab failed"

  let mut write := true
  IO.println s!"{NOCOLOR}"

  let mut onlyConstsArr := #[]
  if let some _onlyConsts := onlyConsts? then
    write := (not $ p.hasFlag "print") || p.hasFlag "write"
    printColor BLUE s!">> Using CLI-specified constants: {_onlyConsts}..."
    onlyConstsArr := _onlyConsts.map (·.toName)
  else
    printColor BLUE s!">> Using all constants from given module: {moduleName}..."
    onlyConstsArr := env.constants.map₂.toArray.map fun (x : Name × Lean.ConstantInfo) => x.1

  let onlyConstsInit := onlyConstsArr.foldl (init := default) fun acc const =>
    if !const.isImplementationDetail && !const.isCStage then acc.insert const else acc

  let onlyConsts ← getCheckableConstants env onlyConstsInit (printErr := true)

  let ignoredConsts := onlyConstsInit.diff onlyConsts
  if ignoredConsts.size > 0 then
    printColor RED s!"WARNING: Skipping translation of {ignoredConsts.size} constants: {ignoredConsts.toArray}..."

  printColor BLUE s!">> Translating {onlyConsts.size} constants..."

  -- translate elaborated Lean environment to Dedukti
  let (_, {env := dkEnv, ..}) ← (Trans.translateEnv onlyConsts (transDeps := write)).toIO { options := default, fileName := "", fileMap := default } {env} {env}

  -- let write := if let some _ := onlyConsts? then (p.hasFlag "write") else true -- REPORT why does this not work?

  IO.print s!"{PURPLE}"
  if write then
    printDkEnv dkEnv none

  if p.hasFlag "print" then
    printDkEnv dkEnv $ .some onlyConsts
  IO.print s!"{NOCOLOR}"

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
