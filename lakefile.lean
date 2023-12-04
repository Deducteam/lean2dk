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
  "git@github.com:leanprover/std4.git" @ "ce2db21d86502e00c4761da5ade58a61612de656"

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
