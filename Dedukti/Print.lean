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
  `normalize.maxS,

  `enc.Univ,
  `enc.Sort,
  `enc.El,
  `enc.Pi
].foldl (init := default) fun curr n => curr.insert n


structure PrintCtx where
  env : Env
  printDeps := true
  lvl : Nat := 0
  /--
    Names of constants whose types are waiting to be printed;
    any rewrite rules that reference these constants should have their printing delayed.
  -/
  pendingTypes : Std.RBSet Name compare := default
  /--
    If currently printing a rule, set to the name of the constant this rule comes from;
    any referenced pending types will be kept track of to delay printing this rule until after they are all printed.
  -/
  printingRule : Option Name := none
  deriving Inhabited
  
structure PrintState where
  printedConsts   : Std.RBMap Name String compare := default
  /--
    Keeps track of whether any of the rules corresponding to a constant referenced any pending types;
    if so, printing of these rules is delayed until after those types have been printed.
    TODO: is it necessary to do this per-rule, instead of per-definable-constant?
  -/
  refPendingTypes : Std.RBMap Name (Std.RBSet Name compare) compare := default
  /--
    Rules that are waiting to be printed as soon as all of their pending types are printed.
  -/
  pendingRules           : Std.RBMap Name (List String) compare := default
  out             : List String := []
  deriving Inhabited

abbrev PrintM := ReaderT PrintCtx $ StateT PrintState $ ExceptT String Id

def withResetPrintMLevel : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with lvl := 0, printingRule := none }

/--
  Registers `refPendingTypeConst` as a pending type referenced by the rules of `ruleConst`.
-/
def addRefPendingTypeInRule (ruleConst refPendingTypeConst : Name) : PrintM Unit := do
  if ruleConst != refPendingTypeConst then
    dbg_trace s!"registering {ruleConst} as depending on {refPendingTypeConst}"
  let refSet := match (← get).refPendingTypes.find? ruleConst with
    | .none => default
    | .some s => s

  modify fun s => { s with refPendingTypes := s.refPendingTypes.insert ruleConst (refSet.insert refPendingTypeConst) }

/--
  Unregisters `refPendingTypeConst` as a pending type referenced by any rules.
  To be called after a pending type has been printed.
  Returns a list of rule strings that are newly ready to be printed.
-/
def removeRefPendingType (refPendingTypeConst : Name) : PrintM $ List String := do
  let mut rulesToPrint := []
  for (ruleConst, rules) in (← get).pendingRules do
    let refSet := match (← get).refPendingTypes.find? ruleConst with
      | .none => default
      | .some s => s

    let refSet := refSet.erase fun n => compare n refPendingTypeConst

    if refSet.size == 0 then
      rulesToPrint := rulesToPrint ++ rules

      modify fun s => { s with refPendingTypes := s.refPendingTypes.erase ruleConst, pendingRules := s.pendingRules.erase ruleConst } -- NOTE: in-place modification OK here?
    else
      modify fun s => { s with refPendingTypes := s.refPendingTypes.insert ruleConst refSet }
  pure rulesToPrint

def withPrintingRule (n : Name) : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with printingRule := some n }

def withPrintDeps (printDeps : Bool) : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with printDeps }

def withPendingType (n : Name) : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with pendingTypes := ctx.pendingTypes.insert n }

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
      if (← read).pendingTypes.contains name then
        if let some ruleConst := (← read).printingRule then -- FIXME possible to combine with above conditional?
          -- if we encounter a pending type while printing a rule, register this rule as pending on the printing of this constant's type
          addRefPendingTypeInRule ruleConst name
      else if (← get).pendingRules.contains name then
        pure default
        -- if let some typeConst := (← read).printingType then
        --   addRefTypeInType ruleConst name
        --   sorry
      else
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

    match const with
      | .static (name : Name) (type : Expr) => do
        -- dbg_trace s!"printing static constant: {name}"
        let constString := s!"{name} : {← type.print}."
        modify fun s => { s with out := s.out ++ [constString], printedConsts := s.printedConsts.insert const.name constString}
        -- dbg_trace s!"done printing static constant: {name}"
      | .definable (name : Name) (type : Expr) (rules : List Rule) => do
        -- dbg_trace s!"printing: {name}"
        let declString := s!"def {name} : {← withPendingType name type.print}."
        -- dbg_trace s!"done printing type: {name}"
        modify fun s => { s with out := s.out ++ [declString], pendingRules := s.pendingRules.insert name [] }
        addRefPendingTypeInRule name name

        withPrintingRule name do 
          for rule in rules do
            let ruleString ← rule.print
            modify fun s => { s with pendingRules := s.pendingRules.insert name $ s.pendingRules.find! name ++ [ruleString]}

        let origRulesString := "\n".intercalate ((← get).pendingRules.find! name)

        let rulesToPrint ← removeRefPendingType name

        modify fun s => { s with out := s.out ++ rulesToPrint, printedConsts := s.printedConsts.insert const.name s!"{declString}\n{origRulesString}"}
        -- dbg_trace s!"done printing: {name}"
end
    
-- if `name` is specified, only print that constant (without printing dependencies)
def Env.print (env : Env) (deps : Bool := true) : PrintM PUnit := do
  withPrintDeps deps $ env.constMap.forM (fun _ const =>
    --dbg_trace s!"printing: {const.name}"
    const.print)

end Dedukti
