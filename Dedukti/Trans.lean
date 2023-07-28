import Dedukti.Types

open Dedukti
open Encoding
open Lean.Meta

-- TODO Trans namespace

structure TransCtx where
  fvars : Array Lean.Expr := default
  lvlParams  : Std.RBMap Name Nat compare := default
  deriving Inhabited

structure TransState where
  env        : Env := default
  deriving Inhabited

inductive Exception where
  | error             : String → Exception
  | unsupportedSyntax : Exception

abbrev TransM := ReaderT TransCtx $ StateT TransState MetaM

@[inline] def TransM.run (x : TransM α) (ctx : TransCtx := {}) (s : TransState := {}) : MetaM (α × TransState) :=
  x ctx |>.run s

@[inline] def TransM.toIO (x : TransM α) (ctxCore : Lean.Core.Context) (sCore : Lean.Core.State) (ctx : TransCtx := {}) (s : TransState := {}) : IO (α × TransState) := do
  let ((a, s), _, _) ← (x.run ctx s).toIO ctxCore sCore
  pure (a, s)

def withResetCtx : TransM α → TransM α := -- TODO reset lvlParams?
  withReader fun ctx => { ctx with fvars := #[], lvlParams := default }

def withLvlParams (params : List Name) (m : TransM α) : TransM α := do
  let lvlParams ← params.length.foldM (init := default) fun i curr =>  
    pure $ curr.insert params[i]! i
  withReader (fun ctx => { ctx with
    lvlParams }) m

def withFVars (fvars : Array Lean.Expr) (m : TransM α) : TransM α := do
  let newFvars := (← read).fvars.append fvars
  withReader (fun ctx => { ctx with
    fvars := newFvars }) m

def dkPrelude : List Const := -- TODO rename things to avoid naming conflicts with stdlib
[
  .static `Lvl  .type,
  .static `Nat  .type,
  .static `z    (.const `Lvl),
  .static `s    (.pi (.const `Lvl) (.const `Lvl)),
  .static `max  (.piN [ (.const `Lvl), (.const `Lvl) ] (.const `Lvl)),
  .static `imax (.piN [ (.const `Lvl), (.const `Lvl) ] (.const `Lvl)),
  .static `var  (.piN [ (.const `Nat) ] (.const `Lvl)),
  .static `Univ (.pi (.const `Lvl) (.type)),
  .static `El   (.piN [(.const `Lvl), (.app (.const `Univ) (.var 0))] (.type)),
  .static `Pi   (.piN [
                    (.const `Lvl), -- s1
                    (.const `Lvl), -- s2
                    (.const `Lvl), -- s3
                    (.app (.const `Univ) (.var 2)),
                    (.pi (.appN (.const `El) [(.var 0)]) (.app (.const `Univ) (.var 3)))
                  ]
                  (.app (.const `Univ) (.var 2))
                )
]

def transLevel' : Lean.Level → TransM Level
  | .zero       => pure .z
  | .succ l     => do pure $ .s (← transLevel' l)
  | .max l1 l2  => do pure $ .max (← transLevel' l1) (← transLevel' l2)
  | .imax l1 l2 => do pure $ .imax (← transLevel' l1) (← transLevel' l2)
  | .param p    => do 
                     let some i := (← read).lvlParams.find? p
                      | throw $ .error default s!"unknown universe parameter {p} encountered"
                     pure $ .var i 
  | .mvar _     => throw $ .error default "unexpected universe metavariable encountered"

def transLevel (l : Lean.Level) : TransM Expr := do pure (← transLevel' l).toExpr

def exprToLevel (expr : Lean.Expr) : TransM Level := do
  match expr with
    | .sort l => pure $ ← transLevel' l
    | _ => pure sorry
    
  def abstract (e : Lean.Expr) : TransM Lean.Expr := do
    e.abstractM (← read).fvars

mutual
  partial def transExprType (e : Lean.Expr) : TransM Expr := do
    pure $ .app (.const `El) (← transExpr e)

  partial def transExpr : Lean.Expr → TransM Expr
    | .bvar _ => throw $ .error default "unexpected bound variable encountered"
    | .sort lvl => do pure $ .app (.const `Univ) (← transLevel lvl) -- FIXME
    | .const name lvls => do pure $ (.appN (.const name) (← lvls.mapM transLevel))
    | .app fnc arg => do pure $ .app (← transExpr fnc) (← transExpr arg)
    | e@(.lam ..) => lambdaTelescope e fun domVars bod => do
                                domVars.foldrM (init := (← withFVars domVars $ transExpr bod)) fun _ (curr) => do
                                  pure (.lam curr)
    | e@(.forallE ..) => forallTelescope e fun domVars img => do
                                let (ret, _) ← domVars.size.foldRevM (init := (← withFVars domVars $ transExpr img, ← exprToLevel $ ← inferType img)) fun i (curr, s2) => do
                                  let domVar := domVars[i]!
                                  let dom ← inferType domVar
                                  let s1 ← exprToLevel $ ← inferType dom -- FIXME are we sure that this will be a .sort (as opposed to something that reduces to .sort)? if not, it may contain fvars
                                  let s3 := Level.imax s1 s2
                                  --(.pi (.appN (.const `El) [(.var 0)]) (.app (.const `Univ) (.var 3)))
                                  let ret := (.appN (.const `Pi) [s1.toExpr, s2.toExpr, s3.toExpr, ← withFVars domVars[:i] $ transExpr dom, (.lam curr)])
                                  pure (ret, s3)
                                pure ret
    | .letE name typ exp bod _ => pure $ .fixme "LETE.FIXME" -- FIXME
    | .lit lit => do pure $ .fixme "LIT.FIXME" -- FIXME
    | .proj _ idx exp => pure $ .fixme "PROJ.FIXME" -- FIXME
    | e@(.fvar ..) => do 
                    let some i := (← read).fvars.indexOf? e | throw $ .error default s!"encountered unknown free variable {e}"
                    pure $ .var ((← read).fvars.size - 1 - i)
    | .mvar ..  => pure $ .fixme "MVAR.FIXME" -- FIXME
    | .mdata .. => pure $ .fixme "MDATA.FIXME" -- FIXME
end

def transConst (cnst : Lean.ConstantInfo) : TransM Const := withLvlParams cnst.levelParams do match cnst with
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
