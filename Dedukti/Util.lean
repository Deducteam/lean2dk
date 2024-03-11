import Lean
open Lean

def charSubs := [
  -- ("»", "-_"),
  -- ("«", "_-"),
  (":", "_cln_"),
]

def fixLeanNameStr (name : String) : String := charSubs.foldl (init := name) fun acc (orig, sub) => acc.replace orig sub

def fixLeanName' : Name → Name
| .str p s   => .str (fixLeanName' p) $ fixLeanNameStr s
| .num p n   => .num (fixLeanName' p) n
| .anonymous => .anonymous

def fixLeanName (n : Name) : Name :=
  fixLeanName' n |>.toStringWithSep "_" false

partial def Lean.Name.isCStage : Name → Bool
| .str p s   => s.startsWith "_cstage" || p.isCStage
| .num p _   => p.isCStage
| .anonymous => false

def ignoredConstant : Name → Bool
| n => !n.isImplementationDetail && !n.isCStage

namespace Deps
  structure Context where
    env        : Environment

  structure State where
    map : HashMap Name ConstantInfo := {}
  abbrev DepsM := ReaderT Context <| StateRefT State IO

  @[inline] def DepsM.run (x : DepsM α) (ctx : Context) (s : State := {}) : MetaM (α × State) :=
    x ctx |>.run s

  @[inline] def DepsM.toIO (x : DepsM α) (ctxCore : Lean.Core.Context) (sCore : Lean.Core.State) (ctx : Context) (s : State := {}) : IO (α × State) := do
  let ((a, s), _, _) ← (x.run ctx s).toIO ctxCore sCore
  pure (a, s)

  partial def namedConstDeps (name : Name) : DepsM Unit := do
    match ((← get).map.find? name) with
    | .none =>
      let some const := (← read).env.find? name | throw $ IO.userError s!"could not find constant \"{name}\" for translation, verify that it exists in the Lean input"
      modify fun s => { s with map := s.map.insert name const }
      let deps := const.getUsedConstantsAsSet
      for dep in deps do
        if !dep.isImplementationDetail && !dep.isCStage then
          namedConstDeps dep
    | .some _ => pure default
end Deps

