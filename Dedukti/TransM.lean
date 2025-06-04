import Dedukti.Types
import Dedukti.Util
open Lean.Meta
open Dedukti

namespace Trans

structure Context where
  constName : Name := default
  constNameOrig : Name := default
  modName : Name := default
  /-- Don't perform universe level normalization on variables; used in e.g. recursor rewrite rules. -/
  noLVarNormalize : Bool := false
  /-- Also translate any constant dependencies when they are encountered. -/
  transDeps : Bool := false
  env : Lean.Environment
  orderedModules : Array Name
  consts : Lean.NameSet
  patchConsts : Lean.NameSet
  fvars     : Array Lean.Expr := default
  fvarTypes : Lean.RBMap Name Expr compare := default
  lvars     : Lean.RBMap Name (Array Lean.Expr × Array Name × Name) compare := default
  lvlParams : Array Name := default

structure State where
  env              : Env := default
  names            : Std.HashMap Name Name := default
  constsToModNames : Std.HashMap Name Name := default
  cache       : Std.HashMap (Array Name × Bool × Lean.Expr) Expr := default
  lvlAuxCache : Std.HashMap (Lean.Level × Array (Name × Nat)) Name := default
  numLvlAux   : Nat := 0
  /-- Counter for lets encountered in a constant,
  to allow for uniquely naming auxilliary let definitions. -/
  numLets  : Nat := 0
  numAux   : Nat := 0
  deriving Inhabited

abbrev TransM := ReaderT Context $ StateT State MetaM

@[inline] def TransM.run (x : TransM α) (ctx : Context) (s : State := {}) : MetaM (α × State) :=
  x ctx |>.run s

@[inline] def TransM.toIO (x : TransM α) (ctxCore : Lean.Core.Context) (sCore : Lean.Core.State) (ctx : Context) (s : State := {}) : IO (α × State) := do
  let ((a, s), _, _) ← (x.run ctx s).toIO {ctxCore with maxHeartbeats := 0} sCore
  pure (a, s)

-- TODO is it normal to accumulate so many `withX` functions?
--
def tthrow (msg : String) : TransM α := do -- FIXME is there a way to make this work with the original "throw" function?
throw $ .error default s!"{msg}\nWhile translating: {(← read).constName}"

def addConst (modName constName : Name) (const : Const) : TransM Unit := do
  let s ← get
  let mut newConstModMap := (← get).env.constModMap

  let mut newConstMap :=
    if let some constMap := newConstModMap.find? modName then
      constMap
    else
      default

  newConstMap := newConstMap.insert constName const
  newConstModMap := newConstModMap.insert modName newConstMap

  set { s with env := {s.env with constModMap := newConstModMap}, constsToModNames := s.constsToModNames.insert constName modName }

def addAuxLvl (name : Name) (const : Const) : TransM Unit := do
  modify fun s => { s with env := {s.env with auxLvlMap := s.env.auxLvlMap.insert name const} }

def resetConstMod (constName oldModName newModName: Name) : TransM Unit := do
  let s ← get
  if oldModName == newModName then return

  let some oldConstMap := (← get).env.constModMap.find? oldModName | throw $ .error default "resetConstMod error"
  let some const := oldConstMap.find? constName | throw $ .error default "resetConstMod error"

  let some newConstMap := (← get).env.constModMap.find? newModName | throw $ .error default "resetConstMod error"

  let mut newConstModMap := (← get).env.constModMap
  newConstModMap := newConstModMap.insert oldModName (oldConstMap.erase constName)
  newConstModMap := newConstModMap.insert newModName (newConstMap.insert constName const)

  set { s with env := {s.env with constModMap := newConstModMap}, constsToModNames := s.constsToModNames.insert constName newModName }

def modImports (m1 m2 : Name) : TransM Bool := do
  let some m1Idx := (← read).orderedModules.idxOf? m1 | throw $ .error default "modImports error"
  let some m2Idx := (← read).orderedModules.idxOf? m2 | throw $ .error default "modImports error"
  return m2Idx < m1Idx
  -- return (← read).env.allImportedModuleNames.contains

def maybeSwapMod (constName : Name) : TransM Unit := do
  let currMod := (← read).modName
  let some oldModName := (← get).constsToModNames.get? constName | throw $ .error default "maybeSwapMod error"
  if ← modImports oldModName currMod then
    resetConstMod constName oldModName currMod

def getModName (constName : Name) : TransM Name := do
  let env := (← read).env
  if (← read).patchConsts.contains constName then
    pure `Init.PatchPrelude
  else if let .some modIdx := env.const2ModIdx.get? constName then
    pure env.header.moduleNames[modIdx]!
  else
    tthrow s!"could not find module for '{constName}'"

def getConstMap (constName : Name) : TransM (Lean.RBMap Name Const compare) := do
  let mut newConstModMap := (← get).env.constModMap

  let mut newConstMap :=
    if let some constMap := newConstModMap.find? (← getModName constName) then
      constMap
    else
      default

  pure newConstMap

def charSubs := [
  -- ("»", "-_"),
  -- ("«", "_-"),
  ("_", "__"), -- needed to not conflict with replacement of `.` namespace separators
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

def withNewConstant (constNameOrig : Name) (m : TransM α) : TransM α := do
  let modName ← getModName constNameOrig
  let constName ← fixLeanName 2 constNameOrig
  let origNumLets := (← get).numLets
  modify fun s => {s with numLets := 0}
  let ret ← withReader (fun ctx => { ctx with constName, constNameOrig, modName }) m
  modify fun s => {s with numLets := origNumLets}
  pure ret

def withResetCtx : TransM α → TransM α :=
  withReader fun ctx => { ctx with fvars := #[], lvlParams := default, noLVarNormalize := false }

def withNoLVarNormalize : TransM α → TransM α :=
  withReader fun ctx => { ctx with noLVarNormalize := true }

def withTransDeps (transDeps : Bool) : TransM α → TransM α :=
  withReader fun ctx => { ctx with transDeps := transDeps }

def withLvlParams (n : Nat) (params : List Name) (m : TransM α) : TransM α := do
  let ret ← withReader (fun ctx => { ctx with lvlParams := .mk params }) m
  pure ret

def withFVars (fvarTypes : Lean.RBMap Name Expr compare) (fvars : Array Lean.Expr) (m : TransM α) : TransM α := do
  let newFvars := (← read).fvars.append fvars
  let newFvarTypes := (← read).fvarTypes.mergeBy (fun _ _ t => t) fvarTypes
  withReader (fun ctx => { ctx with fvarTypes := newFvarTypes, fvars := newFvars }) m

def nextAuxName : TransM Name := do fixLeanName 0 $ ((← read).constName).toString false ++ "_let" ++ (toString (← get).numLets) |>.toName

def newAuxLvlName : TransM Name := do
  let ret ← fixLeanName 0 $ "l" ++ (toString (← get).numLvlAux) |>.toName
  modify fun s => {s with numLvlAux := s.numLvlAux + 1}
  pure ret


-- def mkAuxConst (modName p : Name) (expr : Expr) : TransM Unit := do
--   let s ← get
--   let mut newConstModMap := (← get).env.constModMap
--
--   let mut newConstMap :=
--     if let some constMap := newConstModMap.find? modName then
--       constMap
--     else
--       default
--
--   let auxName := 
--   let numAux := (← get).numAux + 1
--   modify fun s => {s with numAux}
--
--   let constName ← nextAuxName
--   newConstMap := newConstMap.insert constName const
--   newConstModMap := newConstModMap.insert modName newConstMap
--
--   set { s with env := {s.env with constModMap := newConstModMap} }

def nextLetName : TransM Name := do fixLeanName 0 $ ((← read).constName).toString false ++ "_let" ++ (toString (← get).numLets) |>.toName

def withLet (varName : Name) (fvars : Array Lean.Expr) (lvls : Array Name) (m : TransM α) : TransM α := do
  let lvars := (← read).lvars.insert varName (fvars, lvls, ← nextLetName)
  let numLets := (← get).numLets + 1
  modify fun s => {s with numLets}
  withReader (fun ctx => { ctx with lvars }) m

end Trans
