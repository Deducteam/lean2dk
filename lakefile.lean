import Lake

open Lake DSL

package Lean2Dk

@[default_target]
lean_exe lean2dk where
  supportInterpreter := true
  root := `Main

--lean_lib Lean2Dk { roots := #[`Lean2Dk] }

--require Cli from git
--  "https://github.com/lurk-lab/Cli.lean" @ "ef6f9bcd1738638fca8d319dbee653540d56614e"
--
--require std from git
--  "https://github.com/leanprover/std4/" @ "fde95b16907bf38ea3f310af406868fc6bcf48d1"
