import Lake

open Lake DSL

package Lean2Dk

@[default_target]
lean_exe lean2dk where
  supportInterpreter := true
  root := `Main

lean_lib Dedukti { roots := #[`Dedukti] }
@[default_target]
lean_lib fixtures { globs := #[Glob.submodules `fixtures] }

require lean4less from git "https://github.com/rish987/lean4less"
-- require lean4less from "/home/rvaishna/projects/lean4less/"

-- require mathlib from git
--   "https://github.com/leanprover-community/mathlib4" @ "v4.18.0-rc1"

require Cli from git
  "https://github.com/leanprover/lean4-cli" @ "v4.18.0-rc1"

inductive L' where
| im (a b : L') : L'
| m (a b : L') : L'
| z : L'
| s : L' -> L'
| p : String -> L' -> L'
| inst : L' -> L'
#check L'.rec

-- require lean4lean from "/home/rvaishna/projects/lean4lean/"

require lean4lean from git
  "https://github.com/rish987/Lean4Lean" @ "lean4less"

def runCmd' (cmd : String) : ScriptM $ IO.Process.Output := do
  let cmd := cmd.splitOn " "
  if h : cmd ≠ [] then
    let (cmd, args) := match h' : cmd with
      | cmd :: args => (cmd, ⟨args⟩)
      | []          => absurd h' (h' ▸ h)
    IO.Process.output {
      cmd  := cmd
      args := args
    }
  else pure {exitCode := 0, stdout := "", stderr := ""}

abbrev RED        := "\x1b[31m"
abbrev BLUE       := "\x1b[0;34m"
abbrev LIGHT_BLUE := "\x1b[1;34m"
abbrev LIGHT_GRAY := "\x1b[1;36m"
abbrev GREEN      := "\x1b[0;32m"
abbrev NOCOLOR    := "\x1b[0m"

def printCmd (cmd : String) : ScriptM PUnit := do
  let {stderr, stdout, ..} ← runCmd' cmd
  IO.eprint stderr
  IO.print stdout

def runCmd (cmd : String) : ScriptM $ Except String String := do
  let {exitCode, stderr, stdout} ← runCmd' cmd
  if exitCode != 0
    then return .error (stdout ++ "\n" ++ stderr)
    else return .ok (stdout ++ "\n" ++ stderr)

/--
  Run all input commands, erroring if any of them fail,
  and returning their combined output.
-/
def runCmds (cmds : List String) : ScriptM $ Except String String := do
  let mut out := ""
  for cmd in cmds do
    let {exitCode, stderr, stdout} ← runCmd' cmd
    if exitCode != 0
      then return .error (out ++ stdout ++ "\n" ++ stderr)
      else out := out ++ stdout ++ "\n" ++ stderr
  return .ok out

def argsString (args : List String) :=
  s!"{args.foldl (init := "") fun acc arg => acc ++ " " ++ arg}"

def eprintColor (color s : String) := IO.eprintln s!"{color}{s}{NOCOLOR}"
def printColor (color s : String) := IO.println s!"{color}{s}{NOCOLOR}"

-- TODO can call lake exe directly, rather than through runCmd?
script trans_only (args) do
  IO.println "{BLUE}running translation only..."
  match ← runCmds ["lake build fixtures", s!"lake exe lean2dk{argsString args}"] with
  | .error e => eprintColor LIGHT_GRAY e; return 1
  | .ok stdout =>
    printColor NOCOLOR stdout
  return 1

script trans (args) do
  printColor BLUE "running translation + check..."
  match ← runCmds ["lake build fixtures", s!"lake exe lean2dk{argsString args}"] with
  | .error e => eprintColor LIGHT_GRAY e; return 1
  | .ok stdout =>
    printColor NOCOLOR stdout
    match ← runCmd "make check -sC dk" with
    | .error e => eprintColor LIGHT_GRAY e; return 1
    | .ok _ => printColor GREEN "\ntests passed!"; return 0

script test do
  IO.println "running tests..."
  match ← runCmd "make test -sC dk" with
  | .error e => eprintColor LIGHT_GRAY e; return 1
  | .ok out => printColor LIGHT_GRAY out; printColor GREEN "tests passed!"; return 0

script check do
  printColor BLUE s!"running check..."
  match ← runCmd "make check -sC dk" with
  | .error e => eprintColor LIGHT_GRAY e; return 1
  | .ok o =>
    printColor LIGHT_GRAY o
    printColor GREEN "tests passed!"; return 0

open System

partial def getFilePaths (fp : FilePath) (ext : String) (acc : Array FilePath := #[]) :
    IO $ Array FilePath := do
  if ← fp.isDir then
    (← fp.readDir).foldlM (fun acc dir => getFilePaths dir.path ext acc) acc
  else return if fp.extension == some ext then acc.push fp else acc

open Lean (RBTree)

def getAllFiles : ScriptM $ List String := do
  let leanPaths := (← getFilePaths ⟨"Dedukti"⟩ "lean").map toString
  let dkPaths := (← getFilePaths ⟨"dk"⟩ "dk").map toString
  let etcPaths := ["Test.lean"]
  -- let paths : RBTree String compare := RBTree.ofList (leanPaths ++ dkPaths ++ paths).toList -- ordering
  return leanPaths.toList ++ dkPaths.toList ++ etcPaths

script watch (args) do
  let (op, args) :=
    if h : 0 < args.length then
      (args[0]'h, args.tail!)
    else
      ("check", [])
  IO.println s!"watching for file changes to run {op}..."
  while true do
    let cmd := s!"lake run {op}{argsString args}"
    IO.println s!"> {cmd}"
    match ← runCmd s!"{cmd}" with
    | .error e => IO.eprintln e
    | .ok stdout => IO.println stdout
    match ← runCmd s!"inotifywait -qr -e modify -e create -e delete -e move --include (\\.lean|\\.dk) --format %w Dedukti/ dk/ Test.lean Main.lean" with
    | .error _ => pure ()
    | .ok stdout => IO.print s!"file changed in path: {stdout}"
  return 0
