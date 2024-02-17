import Dedukti.Trans
import Dedukti.Print
import Cli

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

def printDkEnv (dkEnv : Env) (only? : Option $ Array String) : IO Unit := do
  let printDeps := if let some _ := only? then false else true

  -- print Dedukti environment
  match (ExceptT.run (StateT.run (ReaderT.run (dkEnv.print (deps := printDeps)) {env := dkEnv}) default)) with
    | .error s => throw $ IO.userError s
    | .ok (_, s) =>
      let dkEnvString := "\n\n".intercalate s.out
      if let some only := only? then
        for name in only do
          let maxConstPrint := 400 -- FIXME make "constant"
          let constString := s.printedConsts.find! (fixLeanName name.toName)
          let constString := if constString.length > maxConstPrint then constString.extract ⟨0⟩ ⟨maxConstPrint⟩ ++ "..." else constString
          IO.println $ "\n" ++ constString
      else
        let dkPrelude := "#REQUIRE normalize.\n"
        let dkEnvString := dkPrelude ++ dkEnvString ++ "\n"
        IO.FS.writeFile "dk/out.dk" dkEnvString

def runTransCmd (p : Parsed) : IO UInt32 := do
  let path := ⟨p.positionalArg! "input" |>.value⟩
  let fileName := path.toString
  IO.println s!"\n{BLUE}>> Translation file: {YELLOW}{fileName}{NOCOLOR}"
  let onlyConsts? := p.flag? "only" |>.map fun setPathsFlag => 
    setPathsFlag.as! (Array String)

  IO.println s!"\n{BLUE}>> Elaborating... {YELLOW}\n"
  -- run elaborator on Lean file
  Lean.initSearchPath (← Lean.findSysroot)
  let (leanEnv, success) ← Lean.Elab.runFrontend (← IO.FS.readFile path) default fileName default
  if not success then
    throw $ IO.userError $ "elab failed"

  let mut write := true
  IO.println s!"{NOCOLOR}"
  if let some onlyConsts := onlyConsts? then
    printColor BLUE s!">> Only translating constants: {onlyConsts}..."
    write := (not $ p.hasFlag "print") || p.hasFlag "write"
  else
    printColor BLUE s!">> Translating entire file..."

  let onlyConstsToTrans? := onlyConsts?.map fun onlyConsts => onlyConsts.map (·.toName)
  -- translate elaborated Lean environment to Dedukti
  let (_, {env := dkEnv, ..}) ← ((Trans.translateEnv onlyConstsToTrans? (transDeps := write)).toIO { options := default, fileName := "", fileMap := default } {env := leanEnv} {env := leanEnv}
)

  -- let write := if let some _ := onlyConsts? then (p.hasFlag "write") else true -- REPORT why does this not work?

  IO.print s!"{PURPLE}"
  if write then
    printDkEnv dkEnv none

  if p.hasFlag "print" then
    printDkEnv dkEnv onlyConsts?
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
