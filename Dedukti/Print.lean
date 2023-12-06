import Dedukti.Types

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

namespace Dedukti

def preludeConstNames : Lean.HashSet Name := -- TODO rename things to avoid naming conflicts with stdlib
[
  `lvl.Lvl,
  `lvl.z,
  `lvl.s,

  `nat.Nat,
  `nat.z,
  `nat.s,

  `lvl.max,
  `lvl.imax,
  `normalize.var,

  `enc.Univ,
  `enc.Sort,
  `enc.El,
  `enc.Pi
].foldl (init := default) fun curr n => curr.insert n


structure PrintCtx where
  env : Env
  printDeps := true
  lvl : Nat := 0
  deriving Inhabited
  
structure PrintState where
  printedConsts : Std.RBMap Name String compare := default
  out           : List String := []
  deriving Inhabited

abbrev PrintM := ReaderT PrintCtx $ StateT PrintState $ ExceptT String Id

def withResetPrintMLevel : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with lvl := 0 }

def withPrintDeps (printDeps : Bool) : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with printDeps }

def withNewPrintMLevel : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with
    lvl := ctx.lvl + 1 }

def withSetPrintMLevel (lvl : Nat) : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with lvl }

def dkExprNeedsFnParens : Expr → Bool
  | .var .. => false
  | .const .. => false
  | .fixme .. => true
  | .app .. => false
  | .lam .. => true
  | .pi .. => true -- should never happen but whatever
  | .type => false
  | .kind => false

def dkExprNeedsArgParens : Expr → Bool
  | .var .. => false
  | .const .. => false
  | .fixme .. => true
  | .app .. => true
  | .lam .. => true
  | .pi .. => true
  | .type => false
  | .kind => false

def dkExprNeedsTypeParens : Expr → Bool
  | .var .. => false
  | .const .. => false
  | .fixme .. => true
  | .app .. => true
  | .lam .. => true -- should never happen but whatever
  | .pi .. => true
  | .type => false
  | .kind => false

mutual
  partial def Rule.print (rule : Rule) : PrintM String := do
    match rule with
    | .mk (vars : Nat) (lhs : Expr) (rhs : Expr) =>
      let mut varsStrings := []
      for i in [0:vars] do
        varsStrings := varsStrings ++ [s!"x{i}"]
      let varsString := ", ".intercalate varsStrings
      withSetPrintMLevel vars do
        pure s!"[{varsString}] {← lhs.print} --> {← rhs.print}."

  partial def Expr.print (expr : Expr) : PrintM String := do
    match expr with
    | .var idx => pure s!"x{(← read).lvl - (idx + 1)}"
    | .const name =>
      if (← read).printDeps && !(preludeConstNames.contains name) && !((← get).printedConsts.contains name) then
        -- print this constant first to make sure the DAG of constant dependencies
        -- is correctly linearized upon printing the .dk file
        let some const := (← read).env.constMap.find? name | throw s!"could not find referenced constant \"{name}\""
        const.print
      pure $ toString name
    | .fixme msg => pure s!"Type (;{msg};)"
    | .app fn arg =>
      let fnExprString ← fn.print
      let fnString := if (dkExprNeedsFnParens fn) then s!"({fnExprString})" else fnExprString
      let argExprString ← arg.print
      let argString := if (dkExprNeedsArgParens arg) then s!"({argExprString})" else argExprString
      pure s!"{fnString} {argString}"
    | .lam bod => pure s!"x{(← read).lvl} => {← withNewPrintMLevel $ bod.print}"
    | .pi dom img =>
      let domExprString ← dom.print
      let domString := if dkExprNeedsTypeParens dom then s!"({domExprString})" else domExprString
      pure s!"x{(← read).lvl}:{domString} -> {← withNewPrintMLevel $ img.print}"
    | .type => pure "Type"
    | .kind => pure "Kind"

  partial def Const.print (const : Const) : PrintM PUnit := withResetPrintMLevel do
    if ((← get).printedConsts.contains const.name) then return

    -- dbg_trace s!"printing: {const.name}"
    -- immediately mark this constant as printed to avoid infinite loops
    modify fun s => { s with printedConsts := s.printedConsts.insert const.name ""}

    let constString ← match const with
      | .static (name : Name) (type : Expr) => do pure s!"{name} : {← type.print}."
      | .definable (name : Name) (type : Expr) (rules : List Rule) => do
        -- if name == `test then
        --   dbg_trace s!"printing expression {name}: {repr type}"
        let decl := s!"def {name} : {← type.print}."
        let rules := "\n".intercalate (← rules.mapM (·.print))
        pure s!"{decl}\n{rules}"

    modify fun s => { s with out := s.out ++ [constString], printedConsts := s.printedConsts.insert const.name constString}
    -- dbg_trace s!"\tprinted: {const.name}"

end
    
-- if `name` is specified, only print that constant (without printing dependencies)
def Env.print (env : Env) (deps : Bool := true) : PrintM PUnit := do
  withPrintDeps deps $ env.constMap.forM (fun _ const =>
    --dbg_trace s!"printing: {const.name}"
    const.print)

end Dedukti
