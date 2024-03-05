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

  mutual
    partial def exprDeps (expr : Expr) : DepsM Unit := do
    match expr with
      | .bvar _ => pure default
      | .sort _ => pure default
      | .const name _ =>
        namedConstsDeps [name]
      | .app fnc arg => do
        exprDeps fnc
        exprDeps arg
      | .lam _ type bod _
      | .forallE _ type bod _ =>
        exprDeps type
        exprDeps bod
      | .letE _ type val bod _ => -- TODO recursive lets (with references in type)?
        exprDeps type
        exprDeps val
        exprDeps bod
      | .lit _ => throw $ IO.userError s!"encountered literal"
      | .proj _ _ e => exprDeps e

      | .fvar _ => pure default
      | .mvar ..  => throw $ IO.userError s!"encountered metavar"
      | .mdata _ e => exprDeps e

    partial def constDeps (const : ConstantInfo) : DepsM Unit := do
      exprDeps const.type
      match const with
      | .defnInfo   val
      | .thmInfo    val
      | .opaqueInfo val =>
        exprDeps val.value
      | .inductInfo _
      | .ctorInfo _
      | .quotInfo _
      | .recInfo _
      | .axiomInfo _ =>
        pure default

    partial def namedConstsDeps (names : List Name) : DepsM Unit := do
      for name in names do
        match ((← get).map.find? name) with
        | .none =>
          let some const := (← read).env.find? name | throw $ IO.userError s!"could not find constant \"{name}\" for translation, verify that it exists in the Lean input"
          modify fun s => { s with map := s.map.insert name const }
          constDeps const
        | .some _ => pure default
  end
end Deps

