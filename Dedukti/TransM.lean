import Dedukti.Types
import Dedukti.Util
open Lean.Meta
open Dedukti

namespace Trans

structure Context where
  /-- Don't perform universe level normalization on variables; used in e.g. recursor rewrite rules. -/
  noLVarNormalize : Bool := false
  /-- Also translate any constant dependencies when they are encountered. -/
  transDeps : Bool := false
  env : Lean.Environment
  fvars     : Array Lean.Expr := default
  fvarTypes : Std.RBMap Name Expr compare := default
  lvars     : Std.RBMap Name (Nat × Name) compare := default
  lvlParams : Std.RBMap Name Nat compare := default

structure State where
  constName  : Name := default
  /-- Counter for lets encountered in a constant,
  to allow for uniquely naming auxilliary let definitions. -/
  numLets    : Nat := 0
  env        : Env := default
  deriving Inhabited

abbrev TransM := ReaderT Context $ StateT State MetaM

@[inline] def TransM.run (x : TransM α) (ctx : Context) (s : State := {}) : MetaM (α × State) :=
  x ctx |>.run s

@[inline] def TransM.toIO (x : TransM α) (ctxCore : Lean.Core.Context) (sCore : Lean.Core.State) (ctx : Context) (s : State := {}) : IO (α × State) := do
  let ((a, s), _, _) ← (x.run ctx s).toIO ctxCore sCore
  pure (a, s)

def withNewConstant (constName : Name) (m : TransM α) : TransM α := do
  set {(← get) with constName, numLets := 0}
  m

def withResetCtx : TransM α → TransM α :=
  withReader fun ctx => { ctx with fvars := #[], lvlParams := default }

def withNoLVarNormalize : TransM α → TransM α :=
  withReader fun ctx => { ctx with noLVarNormalize := true }

def withTransDeps (transDeps : Bool) : TransM α → TransM α :=
  withReader fun ctx => { ctx with transDeps := transDeps }

-- TODO is there an API function to keep track of levels inside of MetaM?
def withLvlParams (params : List Name) (m : TransM α) : TransM α := do
  let lvlParams ← params.length.foldM (init := default) fun i curr =>  
    pure $ curr.insert params[i]! i
  withReader (fun ctx => { ctx with lvlParams }) m

def withFVars (fvarTypes : Std.RBMap Name Expr compare) (fvars : Array Lean.Expr) (m : TransM α) : TransM α := do
  let newFvars := (← read).fvars.append fvars
  let newFvarTypes := (← read).fvarTypes.mergeWith (fun _ _ t => t) fvarTypes
  withReader (fun ctx => { ctx with fvarTypes := newFvarTypes, fvars := newFvars }) m

def nextLetName : TransM Name := do pure $ fixLeanName $ ((← get).constName).toString ++ "_let" ++ (toString (← get).numLets)

def withLet (varName : Name) (m : TransM α) : TransM α := do
  let newLvars := (← read).lvars.insert varName ((← read).fvars.size, ← nextLetName)
  set {(← get) with numLets := (← get).numLets + 1}
  withReader (fun ctx => { ctx with lvars := newLvars }) m

end Trans
