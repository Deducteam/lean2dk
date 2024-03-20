import Dedukti.Types
import Dedukti.Util
open Lean.Meta
open Dedukti

namespace Trans

structure Context where
  constName  : Name := default
  /-- Don't perform universe level normalization on variables; used in e.g. recursor rewrite rules. -/
  noLVarNormalize : Bool := false
  /-- Also translate any constant dependencies when they are encountered. -/
  transDeps : Bool := false
  /-- Counter for lets encountered in a constant,
  to allow for uniquely naming auxilliary let definitions. -/
  numLets    : Nat := 0
  env : Lean.Environment
  fvars     : Array Lean.Expr := default
  fvarTypes : Std.RBMap Name Expr compare := default
  lvars     : Std.RBMap Name (Nat × Name) compare := default
  lvlParams : Std.RBMap Name Nat compare := default

structure State where
  env        : Env := default
  deriving Inhabited

abbrev TransM := ReaderT Context $ StateT State MetaM

@[inline] def TransM.run (x : TransM α) (ctx : Context) (s : State := {}) : MetaM (α × State) :=
  x ctx |>.run s

@[inline] def TransM.toIO (x : TransM α) (ctxCore : Lean.Core.Context) (sCore : Lean.Core.State) (ctx : Context) (s : State := {}) : IO (α × State) := do
  let ((a, s), _, _) ← (x.run ctx s).toIO ctxCore sCore
  pure (a, s)

-- TODO is it normal to accumulate so many `withX` functions?

def withNewConstant (constName : Name) (m : TransM α) : TransM α := do
  withReader (fun ctx => { ctx with constName, numLets := 0 }) m

def tthrow (msg : String) : TransM α := do -- FIXME is there a way to make this work with the original "throw" function?
throw $ .error default s!"{msg}\nWhile translating: {(← read).constName}"

def withResetCtx : TransM α → TransM α :=
  withReader fun ctx => { ctx with fvars := #[], lvlParams := default, noLVarNormalize := false }

def withNoLVarNormalize : TransM α → TransM α :=
  withReader fun ctx => { ctx with noLVarNormalize := true }

def withTransDeps (transDeps : Bool) : TransM α → TransM α :=
  withReader fun ctx => { ctx with transDeps := transDeps }

def withLvlParams (params : List Name) (m : TransM α) : TransM α := do
  let lvlParams ← params.length.foldM (init := default) fun i curr =>  
    pure $ curr.insert params[i]! i
  withReader (fun ctx => { ctx with lvlParams }) m

def withFVars (fvarTypes : Std.RBMap Name Expr compare) (fvars : Array Lean.Expr) (m : TransM α) : TransM α := do
  let newFvars := (← read).fvars.append fvars
  let newFvarTypes := (← read).fvarTypes.mergeWith (fun _ _ t => t) fvarTypes
  withReader (fun ctx => { ctx with fvarTypes := newFvarTypes, fvars := newFvars }) m

def nextLetName : TransM Name := do pure $ fixLeanName $ ((← read).constName).toString false ++ "_let" ++ (toString (← read).numLets)

def withLet (varName : Name) (m : TransM α) : TransM α := do
  let lvars := (← read).lvars.insert varName ((← read).fvars.size, ← nextLetName)
  let numLets := (← read).numLets + 1
  withReader (fun ctx => { ctx with lvars, numLets}) m

end Trans
