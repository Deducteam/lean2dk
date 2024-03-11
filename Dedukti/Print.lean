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
  /--
    Set to the name of a constant if we are currently printing its type.
  -/
  printingType : Option Name := none
  deriving Inhabited
  
structure PrintState where
  printedConsts   : Std.RBMap Name String compare := default
  /--
    Keeps track of whether any of the rules corresponding to a constant referenced any pending types;
    if so, printing of these rules is delayed until after those types have been printed.
    TODO: is it necessary to do this per-rule, instead of per-definable-constant?
  -/
  rulePendingTypesRefs : Std.RBMap Name (Std.RBSet Name compare) compare := default
  /--
    Stores the names of other unprinted constants referenced by a constant's rewrite rules.
  -/
  ruleTypesRefs : Std.RBMap Name (Std.RBSet Name compare) compare := default
  /--
    Stores the names of other unprinted constants referenced by a constant's type.
    If there are any such constants, printing of this constant's rules will be delayed until
    after all of these referenced constants have had their rules printed.
  -/
  typeTypesRefs : Std.RBMap Name (Std.RBSet Name compare) compare := default
  /--
    Rules that are waiting to be printed as soon as all of their pending types are printed.
  -/
  pendingRules           : Std.RBMap Name (List String) compare := default
  out             : List String := []
  deriving Inhabited

abbrev PrintM := ReaderT PrintCtx $ StateT PrintState $ ExceptT String Id

def withResetPrintMLevel : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with lvl := 0, printingRule := none, printingType := none }

/--
  Registers `refTypeConst` as a type referenced by the rules of `ruleConst`.
-/
def addRefTypeInRule (ruleConst refTypeConst : Name) : PrintM Unit := do
  -- if ruleConst != refTypeConst then
  --   dbg_trace s!"registering {ruleConst} as depending on {refTypeConst} in its rule"
  let refSet := match (← get).ruleTypesRefs.find? ruleConst with
    | .none => default
    | .some s => s

  modify fun s => { s with ruleTypesRefs := s.ruleTypesRefs.insert ruleConst (refSet.insert refTypeConst) }

/--
  Registers `refPendingTypeConst` as a pending type referenced by the rules of `ruleConst`.
-/
def addRefPendingTypeInRule (ruleConst refPendingTypeConst : Name) : PrintM Unit := do
  -- if ruleConst != refPendingTypeConst then
  --   dbg_trace s!"registering {ruleConst} as depending on {refPendingTypeConst} in its rule"
  let refSet := match (← get).rulePendingTypesRefs.find? ruleConst with
    | .none => default
    | .some s => s

  modify fun s => { s with rulePendingTypesRefs := s.rulePendingTypesRefs.insert ruleConst (refSet.insert refPendingTypeConst) }

/--
  Registers `refTypeConst` as a type referenced by the type of `typeConst`.
-/
def addRefTypeInType (typeConst refTypeConst : Name) : PrintM Unit := do
  -- if typeConst != refTypeConst then
    -- dbg_trace s!"registering {typeConst} as depending on {refTypeConst} in its type"
  let refSet := match (← get).typeTypesRefs.find? typeConst with
    | .none => default
    | .some s => s

  modify fun s => { s with typeTypesRefs := s.typeTypesRefs.insert typeConst (refSet.insert refTypeConst) }

def eraseFromValues (map : Std.RBMap Name (Std.RBSet Name compare) compare) (name : Name) : Std.RBMap Name (Std.RBSet Name compare) compare :=
  map.foldl (init := default) fun newMap thisName set => 
    let newSet := set.erase fun n => compare name n
    if newSet.size == 0 then
      newMap
    else
      newMap.insert thisName newSet

def updateTypePrinted (const : Name) : PrintM Unit := do
  modify fun s => { s with ruleTypesRefs := eraseFromValues s.ruleTypesRefs const}
  modify fun s => { s with rulePendingTypesRefs := eraseFromValues s.rulePendingTypesRefs const}

def updateRulesPrinted (const : Name) : PrintM Unit := do
  modify fun s => { s with typeTypesRefs := eraseFromValues s.typeTypesRefs const}

partial def getPrintableRules : PrintM $ List String := do
  let mut rulesToPrint := []
  for (ruleConst, rules) in (← get).pendingRules do
    if (← get).pendingRules.find? ruleConst |>.isSome then -- TODO necessary because of in-place modification?
      let anyRulePendingTypesRefs := (← get).rulePendingTypesRefs.find? ruleConst |>.isSome

      let anyRuleTypesRefs := (← get).ruleTypesRefs.find? ruleConst |>.isSome

      let anyTypeRefs := (← get).typeTypesRefs.find? ruleConst |>.isSome

      -- dbg_trace s!" {!anyRulePendingTypesRefs} && {!anyRuleTypesRefs} && {(← get).ruleTypesRefs.find? ruleConst |>.getD default |>.toList}, {ruleConst}"

      if !anyRulePendingTypesRefs && !anyRuleTypesRefs && !anyTypeRefs then
        updateRulesPrinted ruleConst
        modify fun s => { s with pendingRules := s.pendingRules.erase ruleConst} -- TODO in-place modification OK here?
        -- dbg_trace s!"OK to print rules for {ruleConst}"
        rulesToPrint := rulesToPrint ++ rules ++ (← getPrintableRules)
        let origRulesString := "\n".intercalate rules

        modify fun s => { s with printedConsts := s.printedConsts.insert ruleConst s!"TODO get decl\n{origRulesString}"}

  pure rulesToPrint

def withPrintingRule (n : Name) : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with printingRule := some n }

def withPrintDeps (printDeps : Bool) : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with printDeps }

def withPendingType (n : Name) : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with pendingTypes := ctx.pendingTypes.insert n, printingType := some n }

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
      if !((← get).printedConsts.contains name) && !(preludeConstNames.contains name) then
        if let some typeConst := (← read).printingType then
            -- if we encounter an unprinted type while printing a constant's type, register this constant's rules as pending on the printing of this type's rules
            addRefTypeInType typeConst name
        if (← read).pendingTypes.contains name then
          if let some ruleConst := (← read).printingRule then -- FIXME possible to combine with above conditional?
            -- if we encounter a pending type while printing a rule, register this rule as pending on the printing of this constant's type
            addRefPendingTypeInRule ruleConst name
        else
          if (← read).printDeps && !(← get).pendingRules.contains name then
            if let some ruleConst := (← read).printingRule then
              -- any unprinted non-pending types encountered while printing a rule must have their printing delayed until we have registered these rules as pending
              addRefTypeInRule ruleConst name
              -- dbg_trace s!"rule-referenced consts of {ruleConst}: {(← get).ruleTypesRefs.find! ruleConst |>.toList}"
            else
              -- print this constant first to make sure the DAG of constant dependencies
              -- is correctly linearized upon printing the .dk file
              let some const := (← read).env.constMap.find? name | throw s!"could not find referenced constant \"{name}\""
              const.print
      pure $ name.toString false
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

        updateTypePrinted name
        updateRulesPrinted name
        let rulesToPrint ← getPrintableRules
        modify fun s => { s with out := s.out ++ rulesToPrint}

        -- dbg_trace s!"done printing static constant: {name}"
      | .definable (name : Name) (type : Expr) (rules : List Rule) => do
        -- dbg_trace s!"printing: {name}"
        -- modify fun s => { s with pendingRules := s.pendingRules.insert name [] } -- TODO needed?
        let declString := s!"def {name.toString false} : {← withPendingType name type.print}."
        -- dbg_trace s!"done printing type of: {name}"
        modify fun s => { s with out := s.out ++ [declString], pendingRules := s.pendingRules.insert name [] }

        -- dbg_trace s!"adding {rules.length} pending rules for {name}"
        for rule in rules do
          let ruleString ← withPrintingRule name rule.print
          modify fun s => { s with pendingRules := s.pendingRules.insert name $ s.pendingRules.find! name ++ [ruleString]}

        updateTypePrinted name
        let rulesToPrint ← getPrintableRules
        modify fun s => { s with out := s.out ++ rulesToPrint}

        -- print all constants that the rules are dependent on
        let ruleTypesRefs := (← get).ruleTypesRefs.find? name |>.getD default
        for constName in ruleTypesRefs do
          let some const := (← read).env.constMap.find? constName | throw s!"could not find referenced constant \"{constName}\""
          const.print

        -- dbg_trace s!"done printing: {name}"
end
    
-- if `name` is specified, only print that constant (without printing dependencies)
def Env.print (env : Env) (deps : Bool := true) : PrintM PUnit := do
  -- dbg_trace s!"\n\n NEW PRINT"
  withPrintDeps deps $ env.constMap.forM (fun _ const =>
    --dbg_trace s!"printing: {const.name}"
    const.print)

end Dedukti
