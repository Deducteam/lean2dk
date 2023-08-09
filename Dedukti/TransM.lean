import Dedukti.Types
open Lean.Meta
open Dedukti

namespace Trans

structure Context where
  noLVarNormalize : Bool := false -- don't perform universe level normalization on variables; used in e.g. recursor rewrite rules
  fvars : Array Lean.Expr := default
  lvlParams  : Std.RBMap Name Nat compare := default
  deriving Inhabited

structure State where
  env        : Env := default
  deriving Inhabited

abbrev TransM := ReaderT Context $ StateT State MetaM

@[inline] def TransM.run (x : TransM α) (ctx : Context := {}) (s : State := {}) : MetaM (α × State) :=
  x ctx |>.run s

@[inline] def TransM.toIO (x : TransM α) (ctxCore : Lean.Core.Context) (sCore : Lean.Core.State) (ctx : Context := {}) (s : State := {}) : IO (α × State) := do
  let ((a, s), _, _) ← (x.run ctx s).toIO ctxCore sCore
  pure (a, s)

def withResetCtx : TransM α → TransM α :=
  withReader fun ctx => { ctx with fvars := #[], lvlParams := default }

def withNoLVarNormalize : TransM α → TransM α :=
  withReader fun ctx => { ctx with noLVarNormalize := true }

def withLvlParams (params : List Name) (m : TransM α) : TransM α := do
  let lvlParams ← params.length.foldM (init := default) fun i curr =>  
    pure $ curr.insert params[i]! i
  withReader (fun ctx => { ctx with
    lvlParams }) m

def withFVars (fvars : Array Lean.Expr) (m : TransM α) : TransM α := do
  let newFvars := (← read).fvars.append fvars
  withReader (fun ctx => { ctx with
    fvars := newFvars }) m

end Trans
