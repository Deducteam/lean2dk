import Dedukti.Types
import Dedukti.Encoding
import Dedukti.Util

open Dedukti
open Trans
open Encoding
open Lean.Meta

namespace Trans

def fromLevel' : Lean.Level → TransM Level
  | .zero       => pure .z
  | .succ l     => do pure $ .s (← fromLevel' l)
  | .max l1 l2  => do pure $ .max (← fromLevel' l1) (← fromLevel' l2)
  | .imax l1 l2 => do pure $ .imax (← fromLevel' l1) (← fromLevel' l2)
  | .param p    => do
     let some i := (← read).lvlParams.find? p
      | throw $ .error default s!"unknown universe parameter {p} encountered"
     pure $ .var i
     -- TODO deep encoding
     -- let some i := (← read).lvlParams.find? p
     --  | throw $ .error default s!"unknown universe parameter {p} encountered"
     -- pure $ .var i 

  | .mvar _     => throw $ .error default "unexpected universe metavariable encountered"

def fromLevel (l : Lean.Level) : TransM Expr := do (← fromLevel' l).toExpr

def levelFromExpr (expr : Lean.Expr) : TransM Level := do
  match expr with
    | .sort l => pure $ ← fromLevel' l
    | _ => throw $ .error default s!"expected sort but encountered {expr.ctorName}"
    
def levelFromInferredType (e : Lean.Expr) : TransM Level := do
  levelFromExpr $ ← inferType e -- FIXME are we sure that this will be a .sort (as opposed to something that reduces to .sort)? if not, it may contain fvars

partial def fromExpr : Lean.Expr → TransM Expr
  | .bvar _ => throw $ .error default "unexpected bound variable encountered"
  | .sort lvl => do pure $ .app (.const `enc.Sort) (← fromLevel lvl) -- FIXME
  | .const name lvls => do pure $ (.appN (.const $ fixLeanName name) (← lvls.mapM fromLevel))
  | .app fnc arg => do pure $ .app (← fromExpr fnc) (← fromExpr arg)
  | e@(.lam ..) => lambdaTelescope e fun domVars bod => do
                              domVars.foldrM (init := (← withFVars domVars $ fromExpr bod)) fun _ (curr) => do
                                pure (.lam curr)
  | e@(.forallE ..) => forallTelescope e fun domVars img => do
                              let (ret, _) ← domVars.size.foldRevM (init := (← withFVars domVars $ fromExpr img, ← levelFromExpr $ ← inferType img)) fun i (curr, s2) => do
                                let domVar := domVars[i]!
                                let dom ← inferType domVar
                                let s1 ← levelFromInferredType dom -- FIXME are we sure that this will be a .sort (as opposed to something that reduces to .sort)? if not, it may contain fvars
                                let s3 := Level.imax s1 s2
                                --(.pi (.appN (.const `El) [(.var 0)]) (.app (.const `Univ) (.var 3)))
                                let ret ← withFVars domVars[:i] do 
                                  pure (.appN (.const `enc.Pi) [← s1.toExpr, ← s2.toExpr, ← s3.toExpr, ← fromExpr dom, (.lam curr)])
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

partial def fromExprAsType (e : Lean.Expr) : TransM Expr := do
  pure $ .appN (.const `enc.El) [← (← levelFromInferredType e).toExpr, (← fromExpr e)]

def constFromConstantInfo (cnst : Lean.ConstantInfo) : TransM Const := withLvlParams cnst.levelParams do
  let name := fixLeanName cnst.name
  let type ← fromExprAsType cnst.type
  let type := cnst.levelParams.foldr (init := type) fun _ curr => .pi (.const `lvl.Lvl) curr
  match cnst with
  | .axiomInfo    (val : Lean.AxiomVal) => pure $ .static name (.fixme "AXIOM.FIXME") -- FIXME
  | .defnInfo     (val : Lean.DefinitionVal)
  | .thmInfo      (val : Lean.TheoremVal) => do
    let value ← fromExpr val.value
    let value := cnst.levelParams.foldr (init := value) fun _ curr => .lam curr
    pure $ .definable name type [.mk 0 (.const name) value]
  | .opaqueInfo   (val : Lean.OpaqueVal) => pure $ .static name (.fixme "OPAQUE.FIXME") -- FIXME
  | .quotInfo     (val : Lean.QuotVal) => pure $ .static name (.fixme "QUOT.FIXME") -- FIXME
  | .inductInfo   (val : Lean.InductiveVal) => pure $ .static name type
  | .ctorInfo     (val : Lean.ConstructorVal) => do pure $ .static name type
  | .recInfo      (val : Lean.RecursorVal) => do pure $ .static name type

def translateEnv (env : Lean.Environment) : TransM Unit := do
  env.constants.forM (fun _ cinfo => do
    let const ← constFromConstantInfo cinfo
    modify fun s => { s with env := {s.env with constMap := s.env.constMap.insert (fixLeanName cinfo.name) const} }
  )

end Trans
