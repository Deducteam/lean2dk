import Dedukti.Trans
import Dedukti.Print
import Cli
import Lean.Replay
import Lean4Less.Replay
import Lean4Less.Commands
import Lean4Lean.Commands
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
          let name := fixLeanName name
          let some constString := s.printedConsts.find? name | throw $ IO.userError s!"could not find symbol {name} in translated environment"
          let constString := if constString.length > maxConstPrint then constString.extract ⟨0⟩ ⟨maxConstPrint⟩ ++ "..." else constString
          IO.println $ "\n" ++ constString
      else
        let dkPrelude := "#REQUIRE normalize.\n"
        let dkEnvString := dkPrelude ++ dkEnvString ++ "\n"
        IO.FS.writeFile "dk/out.dk" dkEnvString

unsafe def runTransCmd (p : Parsed) : IO UInt32 := do
  let moduleArg := p.positionalArg! "input" |>.value
  let module := moduleArg.toName
  if module == .anonymous then throw <| IO.userError s!"Could not resolve module: {moduleArg}"
  -- TODO better way to print with colors?
  IO.println s!"\n{BLUE}>> Translation module: {YELLOW}{module}{NOCOLOR}"
  let onlyConsts? := p.flag? "only" |>.map fun setPathsFlag => 
    setPathsFlag.as! (Array String)

  let elim := not $ p.hasFlag "no-elim"

  IO.println s!"\n{BLUE}>> Elaborating... {YELLOW}\n"
  let searchPath? := p.flag? "search-path" |>.map fun sp => 
    sp.as! String
  match searchPath? with
  | .some sp =>
    let path := System.FilePath.mk sp
    Lean.searchPathRef.set [path]
  | _ => Lean.initSearchPath (← Lean.findSysroot)
  Lean4Less.withImportModuleAndPatchDefs module (elabPatch := elim) fun env => do
    let overrides := if elim then Lean4Less.getOverrides env.toKernelEnv else default
    let mut write := true
    IO.println s!"{NOCOLOR}"

    let mut onlyConstsArr := #[]
    if let some _onlyConsts := onlyConsts? then
      write := (not $ p.hasFlag "print") || p.hasFlag "write"
      printColor BLUE s!">> Using CLI-specified constants: {_onlyConsts}..."
      onlyConstsArr := _onlyConsts.map (·.toName)
    else
      printColor BLUE s!">> Using all constants from given module: {module}..."
      let some moduleIdx := Lean.Environment.getModuleIdx? env module | throw $ IO.userError s!"main module {module} not found"
      let moduleConstNames := env.header.moduleData.get! moduleIdx |>.constNames.toList
      onlyConstsArr := ⟨moduleConstNames⟩

    let onlyConstsInit := onlyConstsArr.foldl (init := default) fun acc const =>
      if !const.isImplementationDetail && !const.isCStage then acc.push const else acc

    let getProjFns deps env := do
      let mut projFns := #[]
      for (n, info) in deps do
        if let .inductInfo _ := info then
          if Lean.isStructure env n then
            dbg_trace s!"DBG[8]: Main.lean:88 (after if Lean.isStructureLike env {n} then)"
            let si := Lean.getStructureInfo env n
            dbg_trace s!"DBG[9]: Main.lean:90 (after let si := Lean.getStructureInfo env n)"
            let mut i := 0
            while true do
              if let some pn := si.getProjFn? i then
                let .some pi := env.find? pn | throw $ IO.userError s!"could not find projection function {pn}"
                projFns := projFns.push (pn, pi)
              else break
              i := i + 1
      pure projFns

    let mut onlyConstsDeps ← Lean4Lean.getDepConstsEnv env (onlyConstsInit ++ Lean4Less.patchConsts) overrides
    for (pn, pi) in  ← getProjFns onlyConstsDeps env do
      onlyConstsDeps := onlyConstsDeps.insert pn pi
    let addDecl := if elim then Lean4Less.addDecl (opts := {proofIrrelevance := elim, kLikeReduction := elim, structLikeReduction := elim}) else Lean4Lean.addDecl
    let (kenv, _) ← Lean4Lean.replay addDecl {newConstants := onlyConstsDeps, opts := {proofIrrelevance := not elim, kLikeReduction := not elim, structLikeReduction := not elim}, overrides} (← Lean.mkEmptyEnvironment).toKernelEnv (printProgress := true) (op := "patch")
    let env := Lean4Lean.updateBaseAfterKernelAdd env kenv
    onlyConstsDeps ← Lean4Lean.getDepConstsEnv env onlyConstsInit overrides
    for (pn, pi) in  ← getProjFns onlyConstsDeps env do
      onlyConstsDeps := onlyConstsDeps.insert pn pi

    let onlyConstsDepsNames : Lean.NameSet := onlyConstsDeps.keys.foldl (init := default) fun acc const => acc.insert const
    -- let (onlyConsts, env) ← Lean4Lean.replay env onlyConstsDeps (Lean4Less.addDecl (opts := {proofIrrelevance := true, kLikeReduction := true})) (printErr := true) (overrides := default) (printProgress := true) (initConsts := Lean4Less.patchConsts)

    -- let ignoredConsts := onlyConstsInit.diff onlyConsts
    -- if ignoredConsts.size > 0 then
    --   printColor RED s!"WARNING: Skipping translation of {ignoredConsts.size} constants: {ignoredConsts.toArray}..."

    -- printColor BLUE s!">> Translating {onlyConsts.size} constants: {onlyConsts.toArray}..."
    printColor BLUE s!">> Translating {onlyConstsDeps.size} constants..."

    -- translate elaborated Lean environment to Dedukti
    let (_, {env := dkEnv, ..}) ← (Trans.translateEnv onlyConstsDepsNames (transDeps := write)).toIO { options := default, fileName := "", fileMap := default } {env} {env}

    -- let write := if let some _ := onlyConsts? then (p.hasFlag "write") else true -- REPORT why does this not work?

    IO.print s!"{PURPLE}"
    if write then
      printDkEnv dkEnv none

    if p.hasFlag "print" then
      printDkEnv dkEnv $ .some onlyConstsDepsNames
    IO.print s!"{NOCOLOR}"

    return 0

unsafe def transCmd : Cmd := `[Cli|
  transCmd VIA runTransCmd; ["0.0.1"]
  "Translate from Lean to Dedukti."

  FLAGS:
    s, "search-path" : String; "Set Lean search path directory."
    ne, "no-elim";             "Do not eliminate definitional equalities via Lean4Less translation (e.g. when using -s with a pre-translated library)."
    o, only : Array String;    "Only translate the specified constants and their dependencies."
    p, print;                  "Print translation of specified constants to standard output (relevant only with '-o ...')."
    w, write;                  "Also write translation of specified constants (with dependencies) to file (relevant only with '-p')."

  ARGS:
    input : String; "Input Lean module name (e.g. `Init.Classical`)."

  -- SUBCOMMANDS:
  --   installCmd;
  --   testCmd

  -- The EXTENSIONS section denotes features that
  -- were added as an external extension to the library.
  -- `./Cli/Extensions.lean` provides some commonly useful examples.
  EXTENSIONS:
    author "rish987"
]

unsafe def main (args : List String) : IO UInt32 := do
  transCmd.validate args
