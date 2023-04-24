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
    | lam (vars : Nat) (bod : DkExpr)
    | pi (dom : DkExpr) (img : DkExpr)
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

def exprToDk : Lean.Expr → TransM DkExpr
  | .bvar idx => sorry
  | .sort lvl => sorry
  | .const name lvls => sorry
  | .app fnc arg => sorry
  | .lam name typ bod _ => sorry
  | .forallE name dom img _ => sorry
  | .letE name typ exp bod _ => sorry
  | .lit lit => sorry
  | .proj _ idx exp => sorry
  | .fvar ..  => sorry
  | .mvar ..  => sorry
  | .mdata .. => sorry

def constToDk : Lean.ConstantInfo → TransM DkConst
  | .axiomInfo    (val : Lean.AxiomVal) => sorry
  | .defnInfo     (val : Lean.DefinitionVal) => sorry
  | .thmInfo      (val : Lean.TheoremVal) => sorry
  | .opaqueInfo   (val : Lean.OpaqueVal) => sorry
  | .quotInfo     (val : Lean.QuotVal) => sorry
  | .inductInfo   (val : Lean.InductiveVal) => sorry
  | .ctorInfo     (val : Lean.ConstructorVal) => sorry
  | .recInfo      (val : Lean.RecursorVal) => sorry

def envToDk (env : Lean.Environment) : TransM Unit := do
  env.constants.forM (fun _ const => do
    match (← get).env.constMap.find? const.name with
    | none => do
      let constDk ← constToDk const
      modify fun s => { s with env := {s.env with constMap := s.env.constMap.insert const.name constDk} }
    | some _ => sorry
  )

structure PrintCtx where
  lvl : Nat := 0
  deriving Inhabited
  
structure PrintState where
  printedConsts : Lean.HashSet Name := default
  out           : List String := []
  deriving Inhabited

abbrev PrintM := ReaderT PrintCtx $ StateT PrintState $ Id

mutual
  def dkRulePrint (rule : DkRule) : PrintM String := do
    match rule with
    | .mk (vars : Nat) (lhs : DkExpr) (rhs : DkExpr) => sorry

  def dkExprPrint (expr : DkExpr) : PrintM String := do
    match expr with
    | .var (idx : Nat) => sorry
    | .const (name : Name) => sorry
    | .app (fn : DkExpr) (arg : DkExpr) => sorry
    | .lam (vars : Nat) (bod : DkExpr) => sorry
    | .pi (dom : DkExpr) (img : DkExpr) => sorry

  def dkConstPrint (const : DkConst) : PrintM PUnit := do
    let constString ← match const with
      | .static (name : Name) (type : DkExpr) => sorry
      | .definable (name : Name) (type : DkExpr) (rules : List DkRule) => sorry

    modify fun s => { s with printedConsts := s.printedConsts.insert const.name, out := s.out ++ constString }
end

def dkEnvPrint (env : DkEnv) : PrintM PUnit := do
  env.constMap.forM (fun _ const => dkConstPrint const)

--instance : ToString DkRule where toString
--  | .mk (vars : Nat) (lhs : DkExpr) (rhs : DkExpr) => sorry
--
--instance : ToString DkConst where toString
--  | .static (name : Name) (type : DkExpr)  => sorry
--  | .definable (name : Name) (type : DkExpr) (rules : List DkRule) => sorry
--
--instance : ToString DkExpr where toString
--  | .var (idx : Nat) => sorry
--  | .const (name : Name) => toString name
--  | .app (fn : DkExpr) (arg : DkExpr) => sorry
--  | .lam (vars : Nat) (bod : DkExpr) => sorry
--  | .pi (dom : DkExpr) (img : DkExpr) => sorry

instance : ToString DkEnv where toString env :=
  match (StateT.run (ReaderT.run (dkEnvPrint env) default) default) with
  | (_, s) => "\n".intercalate s.out

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
  IO.FS.writeFile "out.dk" (toString dkEnv) 

  return 0
