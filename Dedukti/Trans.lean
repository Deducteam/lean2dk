import Dedukti.Types

open Dedukti

structure TransCtx where
  lvl : Nat := 0
  deriving Inhabited

structure TransState where
  env : Env := default
  deriving Inhabited

abbrev TransM := ReaderT TransCtx $ StateT TransState $ Id

def withResetTransMLevel : TransM α → TransM α :=
  withReader fun ctx => { ctx with lvl := 0 }

def withNewTransMLevel : TransM α → TransM α :=
  withReader fun ctx => { ctx with
    lvl := ctx.lvl + 1 }

def withSetTransMLevel (lvl : Nat) : TransM α → TransM α :=
  withReader fun ctx => { ctx with lvl }

def dkPrelude : List Const := -- TODO rename things to avoid naming conflicts with stdlib
[
  .static `Set .type,
  .static `El (.pi (.const `Set) (.type))
]

def transExpr : Lean.Expr → TransM Expr
  | .bvar idx => pure $ .var idx
  | .sort lvl => pure $ .const `Set -- FIXME
  | .const name lvls => pure $ .const name -- FIXME lvls?
  | .app fnc arg => do pure $ .app (← transExpr fnc) (← transExpr arg)
  | .lam name typ bod _ => do pure $ .lam (← withNewTransMLevel $ transExpr bod) -- FIXME typ?
  | .forallE name dom img _ => do pure $ .pi (← transExpr dom) (← withNewTransMLevel $ transExpr img)
  | .letE name typ exp bod _ => pure $ .fixme "LETE.FIXME" -- FIXME
  | .lit lit => pure $ .fixme "LIT.FIXME" -- FIXME
  | .proj _ idx exp => pure $ .fixme "PROJ.FIXME" -- FIXME
  | .fvar ..  => pure $ .fixme "FVAR.FIXME" -- FIXME
  | .mvar ..  => pure $ .fixme "MVAR.FIXME" -- FIXME
  | .mdata .. => pure $ .fixme "MDATA.FIXME" -- FIXME

def transConst : Lean.ConstantInfo → TransM Const -- FIXME universe levels?
  | .axiomInfo    (val : Lean.AxiomVal) => pure $ .static val.name (.fixme "AXIOM.FIXME") -- FIXME
  | .defnInfo     (val : Lean.DefinitionVal) => do
    pure $ .definable val.name (← transExpr val.type) [.mk 0 (.const val.name) (← transExpr val.value)]
  | .thmInfo      (val : Lean.TheoremVal) => pure $ .static val.name (.fixme "THM.FIXME") -- FIXME
  | .opaqueInfo   (val : Lean.OpaqueVal) => pure $ .static val.name (.fixme "OPAQUE.FIXME") -- FIXME
  | .quotInfo     (val : Lean.QuotVal) => pure $ .static val.name (.fixme "QUOT.FIXME") -- FIXME
  | .inductInfo   (val : Lean.InductiveVal) => pure $ .static val.name .type -- FIXME type should depend on inductive sort?
  | .ctorInfo     (val : Lean.ConstructorVal) => do pure $ .static val.name (← transExpr val.type)
  | .recInfo      (val : Lean.RecursorVal) => do pure $ .static val.name (← transExpr val.type)

def transEnv (env : Lean.Environment) : TransM Unit := do
  for const in dkPrelude do
    modify fun s => { s with env := {s.env with constMap := s.env.constMap.insert const.name const} }
  env.constants.forM (fun _ const => do
    match (← get).env.constMap.find? const.name with
    | none => do
      let constDk ← transConst const
      modify fun s => { s with env := {s.env with constMap := s.env.constMap.insert const.name constDk} }
    | some _ => sorry
  )
