import Dedukti.Types
import Dedukti.Util

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
  `lvl.var,
  `lvl.inst,

  `nat.Nat,
  `nat.z,
  `nat.s,

  `lvl.max,
  `lvl.imax,
  `normalize.maxS,

  `enc.Univ,
  `enc.Sort,
  `enc.El,
  `enc.Pi
].foldl (init := default) fun curr n => curr.insert n


structure PrintCtx where
  constMap : Lean.RBMap Name Const compare
  constsToModNames : Lean.RBMap Name Name compare
  printDeps := true
  inLhs := false
  lvl : Nat := 0
  fvarsToBvars : Std.HashMap Name Name := default
  /--
    Names of constants whose types are waiting to be printed;
    any rewrite rules that reference these constants should have their printing delayed.
  -/
  pendingTypes : Std.HashSet Name := default
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
  printedConsts : Lean.RBMap Name String compare := default
  printedTypes : Lean.RBMap Name String compare := default
  /--
    Keeps track of whether any of the rules corresponding to a constant referenced any pending types;
    if so, printing of these rules is delayed until after those types have been printed.
    TODO: is it necessary to do this per-rule, instead of per-definable-constant?
  -/
  rulePendingTypesRefs : Lean.RBMap Name (Std.HashSet Name) compare := default
  /--
    Stores the names of other unprinted constants referenced by a constant's rewrite rules.
  -/
  ruleTypesRefs : Lean.RBMap Name (Std.HashSet Name) compare := default
  ruleTypesRhsRefs : Lean.RBMap Name (Std.HashSet Name) compare := default
  /--
    Stores the names of other unprinted constants referenced by a constant's type.
    If there are any such constants, printing of this constant's rules will be delayed until
    after all of these referenced constants have had their rules printed.
  -/
  typeTypesRefs : Lean.RBMap Name (Std.HashSet Name) compare := default
  /--
    Rules that are waiting to be printed as soon as all of their pending types are printed.
  -/
  pendingRules : Lean.RBMap Name (List String) compare := default
  out : List String := []
  cache : Std.HashMap Expr String := default
  deriving Inhabited

abbrev PrintM := ReaderT PrintCtx $ StateT PrintState $ ExceptT String Id

def withResetPrintMLevel : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with lvl := 0, printingRule := none, printingType := none, fvarsToBvars := default }

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
  
def addRefTypeInRuleRhs (ruleConst refTypeConst : Name) : PrintM Unit := do
  -- if ruleConst != refTypeConst then
  --   dbg_trace s!"registering {ruleConst} as depending on {refTypeConst} in its rule"
  let refSet := match (← get).ruleTypesRhsRefs.find? ruleConst with
    | .none => default
    | .some s => s

  modify fun s => { s with ruleTypesRhsRefs := s.ruleTypesRhsRefs.insert ruleConst (refSet.insert refTypeConst) }

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

def eraseFromValues (map : Lean.RBMap Name (Std.HashSet Name) compare) (name : Name) : Lean.RBMap Name (Std.HashSet Name) compare :=
  map.fold (init := default) fun newMap thisName set => 
    let newSet := set.erase name
    if newSet.size == 0 then
      newMap
    else
      newMap.insert thisName newSet

def updateTypePrinted (const : Name) : PrintM Unit := do
  modify fun s => { s with rulePendingTypesRefs := eraseFromValues s.rulePendingTypesRefs const}
  modify fun s => { s with ruleTypesRefs := eraseFromValues s.ruleTypesRefs const}

#check Subtype.property
#check Subtype.val

/--
  The rules for this constant have been printed, so we can remove this dependency from
  rules that may depend on it in their types or values.

-/
def updateRulesPrinted (const : Name) : PrintM Unit := do
  modify fun s => { s with typeTypesRefs := eraseFromValues s.typeTypesRefs const}
  modify fun s => { s with ruleTypesRhsRefs := eraseFromValues s.ruleTypesRhsRefs const}

def setConstPrinted (name : Name) (str : String) : PrintM PUnit := do
  modify fun s => { s with printedConsts := s.printedConsts.insert name str }
  let size := (← get).printedConsts.size
  if size % 50 == 0 then
    dbg_trace s!"{size}/{(← read).constMap.size} constants printed"

partial def getPrintableRules (dbg := false) : PrintM $ List String := do
  let mut rulesToPrint := []
  for (ruleConst, rules) in (← get).pendingRules do
    if (← get).pendingRules.find? ruleConst |>.isSome then -- TODO necessary because of in-place modification?
      let theRulePendingTypesRefs := (← get).rulePendingTypesRefs
      let anyRulePendingTypesRefs := theRulePendingTypesRefs.find? ruleConst |>.isSome

      let theRuleTypesRefs := (← get).ruleTypesRefs.find? ruleConst
      let anyRuleTypesRefs := theRuleTypesRefs |>.isSome

      let theTypesRefs := (← get).typeTypesRefs.find? ruleConst
      let anyTypesRefs := theTypesRefs |>.isSome

      let theRuleTypesRhsRefs := (← get).ruleTypesRhsRefs.find? ruleConst
      let anyRuleTypesRhsRefs := theRuleTypesRhsRefs |>.isSome

      if dbg then
        -- dbg_trace s!"{ruleConst}: {!anyRulePendingTypesRefs} && {theTypesRefs.map (·.toList)} && {!anyRuleTypesRefs} && {!anyRuleTypesRhsRefs}"
        dbg_trace s!"{ruleConst}: {!anyRulePendingTypesRefs} && {theTypesRefs.map (·.toList)} && {!anyRuleTypesRefs} && {(← get).ruleTypesRhsRefs.find? ruleConst |>.getD default |>.toList}"
        dbg_trace s!"DBG[9]: Print.lean:202 {(← get).printedTypes.find! ruleConst}"
        -- dbg_trace s!" {!anyRulePendingTypesRefs} && {!anyRuleTypesRefs} && {(← get).ruleTypesRefs.find? ruleConst |>.getD default |>.toList}, {ruleConst}"

      if !anyRulePendingTypesRefs && !anyRuleTypesRefs && !anyTypesRefs && !anyRuleTypesRhsRefs then
        updateRulesPrinted ruleConst
        modify fun s => { s with pendingRules := s.pendingRules.erase ruleConst} -- TODO in-place modification OK here?
        -- dbg_trace s!"OK to print rules for {ruleConst}"
        rulesToPrint := rulesToPrint ++ rules ++ (← getPrintableRules)
        let origRulesString := "\n".intercalate rules

        setConstPrinted ruleConst s!"TODO get decl\n{origRulesString}"

  pure rulesToPrint

def withPrintingRule (n : Name) : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with printingRule := some n }

def withPrintDeps (printDeps : Bool) : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with printDeps }

def withInLhs (inLhs : Bool) : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with inLhs }

def withPendingType (n : Name) : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with pendingTypes := ctx.pendingTypes.insert n, printingType := some n }

def withNewPrintMLevel (fvarName : Name) (f : PrintM α) : PrintM α := do
  withReader (fun ctx => { ctx with
    lvl := ctx.lvl + 1,
    fvarsToBvars := ctx.fvarsToBvars.insert fvarName s!"x{ctx.lvl}".toName
  }) do
    let ret ← f
    pure ret

def withSetPrintMLevel (lvl : Nat) (fvarsToBvars : Std.HashMap Name Name) : PrintM α → PrintM α :=
  withReader fun ctx => { ctx with lvl, fvarsToBvars }

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

def maybeQuote (name : Name) : String :=
  let nameString := name.toString false
  let shouldQuote := nameString.any (fun c => c.toNat > 255)
  if shouldQuote then s!"\{|{nameString}|}" else nameString

mutual
  partial def Rule.print (rule : Rule) : PrintM String := do
    match rule with
    | .mk (vars : List Name) (lhs : Expr) (rhs : Expr) =>
      let mut varsStrings := []
      let mut newFvarsToBvars := (← read).fvarsToBvars
      for i in [0:vars.length] do
        varsStrings := varsStrings ++ [s!"x{i}"]
        newFvarsToBvars := newFvarsToBvars.insert vars[i]! s!"x{i}".toName
      let varsString := ", ".intercalate varsStrings
      withSetPrintMLevel vars.length newFvarsToBvars do
        pure s!"[{varsString}] {← withInLhs true lhs.print} --> {← rhs.print}."

  partial def Expr.print (expr : Expr) : PrintM String := do
    -- if let some e := (← get).cache.get? expr then
    --   return e
    -- let e ← expr.print'
    -- modify fun s => {s with cache := s.cache.insert expr e}
    -- pure e
    expr.print'

  partial def Expr.print' (expr : Expr) : PrintM String := do
    match expr with
    | .var n =>
      let some bn := (← read).fvarsToBvars.get? n | throw s!"could not find bound variable corresponding to free variable {n}, {(← read).printingType}, {(← read).printingRule}"
      pure bn.toString
    | .const name =>
      if ((← read).constMap.find? name).isSome && !((← get).printedConsts.contains name) && !(preludeConstNames.contains name) then
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
              if not (← read).inLhs then
                addRefTypeInRuleRhs ruleConst name
              -- dbg_trace s!"rule-referenced consts of {ruleConst}: {(← get).ruleTypesRefs.find! ruleConst |>.toList}"
            else
              -- print this constant first to make sure the DAG of constant dependencies
              -- is correctly linearized upon printing the .dk file
              let some const := (← read).constMap.find? name | throw s!"could not find referenced constant \"{name}\" (1), {(← read).constMap.toList.map (·.1)}"
              const.print
      let prefix? ← do
        if ((← read).constMap.find? name).isNone && !(preludeConstNames.contains name) then
          let modName ←
            if let .some modName := (← read).constsToModNames.find? name then
              pure modName
            else
              throw s!"could not find module prefix for constant {name}"
          pure $ .some modName.toString
        else pure none
      if let some pref := prefix? then
        pure $ pref ++ "." ++ maybeQuote name
      else
        pure $ maybeQuote name
    | .fixme msg => pure s!"Type (;{msg};)"
    | .app fn arg =>
      let fnExprString ← fn.print
      let fnString := if (dkExprNeedsFnParens fn) then s!"({fnExprString})" else fnExprString
      let argExprString ← arg.print
      let argString := if (dkExprNeedsArgParens arg) then s!"({argExprString})" else argExprString
      pure s!"{fnString} {argString}"
    | .lam n bod typ =>
      let bodStr ← withNewPrintMLevel n do bod.print
      let ret := s!"x{(← read).lvl} : {← typ.print} => {bodStr}"
      pure ret
    | .pi n dom img =>
      let domExprString ← dom.print
      let imgString ← withNewPrintMLevel n do img.print
      let domString := if dkExprNeedsTypeParens dom then s!"({domExprString})" else domExprString
      pure s!"x{(← read).lvl}:{domString} -> {imgString}"
    | .type => pure "Type"
    | .kind => pure "Kind"


  partial def Const.print (const : Const) : PrintM PUnit := withResetPrintMLevel $ withInLhs false do
    if ((← get).printedConsts.contains const.name) then return

    -- dbg_trace s!"printing: {const.name}"

    match const with
      | .static (name : Name) (type : Expr) => do
        -- dbg_trace s!"printing static constant: {name}"
        let constString := s!"{maybeQuote name} : {← type.print}."
        modify fun s => { s with out := s.out ++ [constString], printedTypes := s.printedTypes.insert const.name constString}
        setConstPrinted const.name constString

        updateTypePrinted name
        updateRulesPrinted name
        let rulesToPrint ← getPrintableRules
        modify fun s => { s with out := s.out ++ rulesToPrint}

        -- dbg_trace s!"done printing static constant: {name}"
      | .definable (name : Name) (type : Expr) (rules : List Rule) => do
        -- dbg_trace s!"printing: {name}"
        -- modify fun s => { s with pendingRules := s.pendingRules.insert name [] } -- TODO needed?
        if not ((← get).printedTypes.contains name) then
          let declString := s!"def {maybeQuote name} : {← withPendingType name type.print}."
          -- dbg_trace s!"done printing type of: {name}"
          modify fun s => { s with out := s.out ++ [declString], pendingRules := s.pendingRules.insert name [], printedTypes := s.printedTypes.insert const.name declString}

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
          let some const := (← read).constMap.find? constName | pure () -- throw s!"could not find referenced constant \"{constName}\" (2)"
          const.print

        -- dbg_trace s!"done printing: {name}"
end
    
-- if `name` is specified, only print that constant (without printing dependencies)
def print (constMap : Lean.RBMap Name Const compare) (modName : Name) (deps : Bool := true) : PrintM PUnit := do
  -- dbg_trace s!"\n\n NEW PRINT"
  withPrintDeps deps $ constMap.forM (fun _ const => do
    -- if not ((← get).printedConsts.contains const.name) then
    --   dbg_trace s!"printing: {const.name}"
    const.print)

  if (← get).pendingRules.size > 0 then
    -- for (name, _) in (← get).pendingRules do
    --   dbg_trace s!"DBG[14]: Print.lean:397 {name}"
    let rulesToPrint ← getPrintableRules true
    dbg_trace s!"DBG[15]: Print.lean:398: rulesToPrint={rulesToPrint.length}"
    throw s!"error: {(← get).pendingRules.size} pending rules for {(← get).pendingRules.toList.map (·.1)} remain unprinted for module {modName}"

end Dedukti
