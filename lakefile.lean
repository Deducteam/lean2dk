import Lake

open Lake DSL

package Lean2Dk

@[default_target]
lean_exe lean2dk where
  supportInterpreter := true
  root := `Main

lean_lib Dedukti { roots := #[`Dedukti] }

-- require Cli from git
--   "git@github.com:lurk-lab/Cli.lean.git" @ "ef6f9bcd1738638fca8d319dbee653540d56614e"

require std from git
  "https://github.com/leanprover/std4" @ "ce2db21d86502e00c4761da5ade58a61612de656"

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

def printCmd (cmd : String) : ScriptM PUnit := do
  let {stderr, stdout, ..} ← runCmd' cmd
  IO.eprint stderr
  IO.print stdout

def runCmd (cmd : String) : ScriptM $ Except String String := do
  let {exitCode, stderr, stdout} ← runCmd' cmd
  if exitCode != 0
    then return .error (stdout ++ "\n" ++ stderr)
    else return .ok (stdout ++ "\n" ++ stderr)

script trans do
  IO.println "running translation + check..."
  match ← runCmd "lake exe lean2dk" with
  | .error e => IO.eprintln e; return 1
  | .ok stdout =>
    IO.FS.writeFile "stdout" stdout
    -- printCmd "echo ---------------- out.dk"
    -- printCmd "cat dk/out.dk"
    -- printCmd "echo ----------------"
    match ← runCmd "make check -C dk" with
    | .error e => IO.eprintln e; return 1
    | .ok _ => IO.println "tests passed!"; return 0

script test do
  IO.println "running tests..."
  match ← runCmd "make test -C dk" with
  | .error e => IO.eprintln e; return 1
  | .ok out => IO.println out; IO.println "tests passed!"; return 0

script check do
  IO.println "running check..."
  match ← runCmd "make check -C dk" with
  | .error e => IO.eprintln e; return 1
  | .ok _ => IO.println "check passed!"; return 0

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
  let op :=
  if h : 0 < args.length then
    args[0]'h
  else
    "check"
  IO.println s!"watching for file changes to run {op}..."
  while true do
    match ← runCmd s!"inotifywait -qr -e modify -e create -e delete -e move --include dk --include lean --format %w Dedukti/ dk/" with
    | .error e => IO.eprintln s!"error: {e}"
    | .ok stdout => IO.print s!"file changed in path: {stdout}"

    IO.println s!"> lake run {op}"
    match ← runCmd s!"lake run {op}" with
    | .error e => IO.eprintln e
    | .ok stdout => IO.println stdout
  return 0
