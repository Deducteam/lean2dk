import Lean
import Std.Data.RBMap

deriving instance Repr for Lean.ConstantVal

deriving instance Repr for Lean.AxiomVal

deriving instance Repr for Lean.ReducibilityHints
deriving instance Repr for Lean.DefinitionVal

deriving instance Repr for Lean.TheoremVal

deriving instance Repr for Lean.OpaqueVal

deriving instance Repr for Lean.QuotKind
deriving instance Repr for Lean.QuotVal

deriving instance Repr for Lean.InductiveVal

deriving instance Repr for Lean.ConstructorVal

deriving instance Repr for Lean.RecursorRule
deriving instance Repr for Lean.RecursorVal

deriving instance Repr for Lean.ConstantInfo

notation "Name" => Lean.Name

mutual
  inductive DkRule where
    | mk (vars : Nat) (lhs : DkExpr) (rhs : DkExpr)

  inductive DkConst where
    | static (name : Name) (type : DkExpr) 
    | definable (name : Name) (type : DkExpr) (rules : List DkRule)

  inductive DkExpr
    | var (idx : Nat) 
    | const (name : Name)
    | app (fn : DkExpr) (arg : DkExpr)
    | lam (bod : DkExpr)
    | pi (dom : DkExpr) (img : DkExpr)
    | type
end

def DkConst.name : DkConst → Name
  | .static (name : Name) .. => name 
  | .definable (name : Name) .. => name

instance : Ord Name where
  compare := Lean.Name.quickCmp

structure DkEnv where
  constMap : Std.RBMap Name DkConst compare
  deriving Inhabited

structure TransCtx where
  lvl : Nat := 0
  deriving Inhabited

structure TransState where
  env : DkEnv := default
  deriving Inhabited

abbrev TransM := ReaderT TransCtx $ StateT TransState $ Id

def withResetTransMLevel : TransM α → TransM α :=
  withReader fun ctx => { ctx with lvl := 0 }

def withNewTransMLevel : TransM α → TransM α :=
  withReader fun ctx => { ctx with
    lvl := ctx.lvl + 1 }

def withSetTransMLevel (lvl : Nat) : TransM α → TransM α :=
  withReader fun ctx => { ctx with lvl }

def exprToDk : Lean.Expr → TransM DkExpr
  | .bvar idx => sorry
  | .sort lvl => sorry
  | .const name lvls => pure $ .const name -- FIXME lvls?
  | .app fnc arg => do pure $ .app (← exprToDk fnc) (← exprToDk fnc)
  | .lam name typ bod _ => sorry
  | .forallE name dom img _ => sorry
  | .letE name typ exp bod _ => sorry
  | .lit lit => sorry
  | .proj _ idx exp => sorry
  | .fvar ..  => sorry
  | .mvar ..  => sorry
  | .mdata .. => sorry

def constToDk : Lean.ConstantInfo → TransM DkConst
  | .axiomInfo    (val : Lean.AxiomVal) => pure $ .static val.name (.const `AXIOM.FIXME) -- FIXME
  | .defnInfo     (val : Lean.DefinitionVal) => do
    pure $ .definable val.name (← exprToDk val.type) [.mk 0 (.const val.name) (← exprToDk val.value)]
  | .thmInfo      (val : Lean.TheoremVal) => pure $ .static val.name (.const `THM.FIXME) -- FIXME
  | .opaqueInfo   (val : Lean.OpaqueVal) => pure $ .static val.name (.const `OPAQUE.FIXME) -- FIXME
  | .quotInfo     (val : Lean.QuotVal) => pure $ .static val.name (.const `QUOT.FIXME) -- FIXME
  | .inductInfo   (val : Lean.InductiveVal) => pure $ .static val.name .type -- FIXME type should depend on inductive sort?
  | .ctorInfo     (val : Lean.ConstructorVal) => pure $ .static val.name (.const `CTOR.FIXME) -- FIXME
  | .recInfo      (val : Lean.RecursorVal) => pure $ .static val.name (.const `REC.FIXME) -- FIXME

def envToDk (env : Lean.Environment) : TransM Unit := do
  env.constants.forM (fun _ const => do
    match (← get).env.constMap.find? const.name with
    | none => do
      let constDk ← constToDk const
      modify fun s => { s with env := {s.env with constMap := s.env.constMap.insert const.name constDk} }
    | some _ => sorry
  )

structure PrintCtx where
  env : DkEnv
  lvl : Nat := 0
  deriving Inhabited
  
structure PrintState where
  printedConsts : Lean.HashSet Name := default
  out           : List String := []
  deriving Inhabited

abbrev PrintM := ReaderT PrintCtx $ StateT PrintState $ ExceptT String Id

def withResetPrintMLevel : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with lvl := 0 }

def withNewPrintMLevel : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with
    lvl := ctx.lvl + 1 }

def withSetPrintMLevel (lvl : Nat) : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with lvl }

mutual
  partial def dkRulePrint (rule : DkRule) : PrintM String := do
    match rule with
    | .mk (vars : Nat) (lhs : DkExpr) (rhs : DkExpr) =>
      let mut varsStrings := []
      for i in [0:vars] do
        varsStrings := varsStrings ++ [s!"x{i}"]
      let varsString := ", ".intercalate varsStrings
      withSetPrintMLevel vars do
        pure s!"[{varsString}] {← dkExprPrint lhs} --> {← dkExprPrint rhs}."

  partial def dkExprPrint' (expr : DkExpr) : PrintM (String × Bool) := do
    match expr with
    | .var (idx : Nat) => pure (s!"x{(← read).lvl - (idx + 1)}", false)
    | .const (name : Name) =>
      if ! ((← get).printedConsts.contains name) then
        -- print this constant first to make sure the DAG of constant dependencies
        -- is correctly linearized upon printing the .dk file
        let some const := (← read).env.constMap.find? name | throw "could not find referenced constant \"{name}\""
        dkConstPrint const
      pure (toString name, false)
    | .app (fn : DkExpr) (arg : DkExpr) =>
      let (fnExprString, needsParens) ← dkExprPrint' fn
      let fnString := if needsParens then s!"({fnExprString})" else fnExprString
      pure (s!"{fnString} {← dkExprPrint arg}", false)
    | .lam (bod : DkExpr) => pure (s!"x{(← read).lvl} => {← withNewPrintMLevel $ dkExprPrint bod}", true)
    | .pi (dom : DkExpr) (img : DkExpr) => pure (s!"x{(← read).lvl}:{← dkExprPrint dom} -> {← withNewPrintMLevel $ dkExprPrint img}", true)
    | .type => pure ("Type", false)

  partial def dkExprPrint (expr : DkExpr) : PrintM String := do pure (← dkExprPrint' expr).1

  partial def dkConstPrint (const : DkConst) : PrintM PUnit := withResetPrintMLevel do
    let constString ← match const with
      | .static (name : Name) (type : DkExpr) => do pure s!"{name} : {← dkExprPrint type}."
      | .definable (name : Name) (type : DkExpr) (rules : List DkRule) => do
        let decl := s!"def {name} : {← dkExprPrint type}."
        let rules := "\n".intercalate (← rules.mapM dkRulePrint)
        pure s!"{decl}\n{rules}"

    modify fun s => { s with printedConsts := s.printedConsts.insert const.name, out := s.out ++ [constString] }
end
    

def dkEnvPrint (env : DkEnv) : PrintM PUnit := do
  env.constMap.forM (fun _ const => dkConstPrint const)

def main (args : List String) : IO UInt32 := do
  let path := ⟨"Test.lean"⟩
  let (leanEnv, success) ← Lean.Elab.runFrontend (← IO.FS.readFile path) default path.toString default
  if not success then
    throw $ IO.userError $ "elab failed"

  IO.println s!"number of constants: {leanEnv.constants.size}"
  leanEnv.constants.forM (fun _ const => do
    IO.println s!"definition: {repr const}"
  )

  let (_, {env := dkEnv}) := (StateT.run (ReaderT.run (envToDk leanEnv) default) default)

  let dkEnvString ← match (ExceptT.run (StateT.run (ReaderT.run (dkEnvPrint dkEnv) {env := dkEnv}) default)) with
    | .error s => throw $ IO.userError s
    | .ok (_, s) => pure $ "\n\n".intercalate s.out

  IO.FS.writeFile "out.dk" dkEnvString 

  return 0
