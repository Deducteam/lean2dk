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
  fvarTypes : Lean.RBMap Name Expr compare := default
  lvars     : Lean.RBMap Name (Array Lean.Expr × Name) compare := default
  lvlParams : Array Name := default

structure State where
  env        : Env := default
  names      : Std.HashMap Name Name := default
  cache      : Std.HashMap (Array Name × Bool × Lean.Expr) Expr := default
  deriving Inhabited

abbrev TransM := ReaderT Context $ StateT State MetaM

@[inline] def TransM.run (x : TransM α) (ctx : Context) (s : State := {}) : MetaM (α × State) :=
  x ctx |>.run s

@[inline] def TransM.toIO (x : TransM α) (ctxCore : Lean.Core.Context) (sCore : Lean.Core.State) (ctx : Context) (s : State := {}) : IO (α × State) := do
  let ((a, s), _, _) ← (x.run ctx s).toIO {ctxCore with maxHeartbeats := 0} sCore
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
  withReader (fun ctx => { ctx with lvlParams := .mk params }) m

def withFVars (fvarTypes : Lean.RBMap Name Expr compare) (fvars : Array Lean.Expr) (m : TransM α) : TransM α := do
  let newFvars := (← read).fvars.append fvars
  let newFvarTypes := (← read).fvarTypes.mergeBy (fun _ _ t => t) fvarTypes
  withReader (fun ctx => { ctx with fvarTypes := newFvarTypes, fvars := newFvars }) m

def charSubs := [
  -- ("»", "-_"),
  -- ("«", "_-"),
  (":", "_cln_"),
  ("@", "_at_"),
  -- TODO any other weird chars?
]

def fixLeanNameStr (name : String) : String := charSubs.foldl (init := name) fun acc (orig, sub) => acc.replace orig sub

def fixLeanName' : Name → Name
| .str p s   => .str (fixLeanName' p) $ fixLeanNameStr s
| .num p n   => .num (fixLeanName' p) n
| .anonymous => .anonymous

def fixLeanName (id : Nat) (n : Name) : TransM Name := do
  if let some prevName := (← get).names.get? n then
    return prevName
  let mut ret := fixLeanName' n |>.toStringWithSep "_" false |>.toName
  if ret == .anonymous then -- failed to fix a name (likely due to unicode symbols)
    let numNames := (← get).names.size
    let newName := s!"anon_{numNames}".toName
    ret := newName
  modify fun s => {s with names := s.names.insert n ret}
  pure ret

-- FIXME should count lets in state instead (what if lets are defined in parallel branches of the expression, will we have duplicate names?)
def nextLetName : TransM Name := do fixLeanName 0 $ ((← read).constName).toString false ++ "_let" ++ (toString (← read).numLets) |>.toName

def withLet (varName : Name) (fvars : Array Lean.Expr) (m : TransM α) : TransM α := do
  let lvars := (← read).lvars.insert varName (fvars, ← nextLetName)
  let numLets := (← read).numLets + 1
  withReader (fun ctx => { ctx with lvars, numLets}) m

end Trans
