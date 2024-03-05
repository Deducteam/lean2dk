import Lean
open Lean

def fixLeanName (name : Name) : Name := name.toStringWithSep "_" false -- TODO what does the "escape" param do exactly?

namespace Deps
  structure Context where
    env : Environment

  structure State where
    map : HashMap Name ConstantInfo := {}
  abbrev DepsM := ReaderT Context <| StateRefT State IO

  @[inline] def DepsM.run (x : DepsM α) (ctx : Context) (s : State := {}) : MetaM (α × State) :=
    x ctx |>.run s

  @[inline] def DepsM.toIO (x : DepsM α) (ctxCore : Lean.Core.Context) (sCore : Lean.Core.State) (ctx : Context) (s : State := {}) : IO (α × State) := do
  let ((a, s), _, _) ← (x.run ctx s).toIO ctxCore sCore
  pure (a, s)

  partial def namedConstsDeps (names : List Name) : DepsM Unit := do
    for name in names do
      match ((← get).map.find? name) with
      | .none =>
        let some const := (← read).env.find? name | throw $ IO.userError s!"could not find constant \"{name}\" for translation, verify that it exists in the Lean input"
        modify fun s => { s with map := s.map.insert name const }
        let deps := const.getUsedConstantsAsSet
        namedConstsDeps deps.toList
      | .some _ => pure default
end Deps

