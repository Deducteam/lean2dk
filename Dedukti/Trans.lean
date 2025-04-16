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
     let some i := (← read).lvlParams.idxOf? p
      | tthrow s!"unknown universe parameter {p} encountered"
     -- dbg_trace s!"{p}: {i}"
     pure $ .var p i
  | .mvar _     => tthrow "unexpected universe metavariable encountered"

def fromLevel (l : Lean.Level) : TransM Expr := do (← fromLevel' l).toExpr

def levelFromExpr (expr : Lean.Expr) : TransM Level := do
  match expr with
    | .sort l => pure $ ← fromLevel' l
    | _ => tthrow s!"expected sort but encountered {expr.ctorName} -- {expr.dbgToString}"
    
def levelFromInferredType (e : Lean.Expr) : TransM Level := do
  levelFromExpr $ ← reduceAll $ ← inferType e

def dupParams (origParams : Array Lean.Expr) : TransM (Array (Name × Lean.BinderInfo × (Array Lean.Expr → TransM Lean.Expr))) := 
  origParams.foldlM (init := #[]) fun x param => do
    let paramType ← inferType param
    pure $ x.append #[(default, default, fun prevParams => pure $ paramType.replaceFVars origParams[:prevParams.size] prevParams)] -- FIXME do I need to generate unique names here? e.g. param.fvarId!.name ++ `New

/-- Gets the `StructureInfo` if `structName` has been declared as a structure to the elaborator. -/
def getStructureInfo? (env : Lean.Environment) (structName : Name) : TransM (Option Lean.StructureInfo) :=
  match env.const2ModIdx[structName]? with
  | some modIdx => pure $ Lean.structureExt.getModuleEntries env modIdx |>.binSearch { structName } Lean.StructureInfo.lt
  | none        => tthrow s!"structure not found: {structName}"

def natZero : Lean.Expr := .const ``Nat.zero []
def natSucc : Lean.Expr := .const ``Nat.succ []

def natLitToConstructor : Nat → Lean.Expr
  | 0 => natZero
  | n+1 => .app natSucc (natLitToConstructor n)

mutual
  partial def mkProjFn (induct : Name) (us : List Lean.Level) (params : Array Lean.Expr) (i : Nat) (major : Lean.Expr) : TransM Expr := do
    match ← getStructureInfo? (← read).env induct with
    | none => pure $ .fixme "PROJ.FIXME"
    | some info => match info.getProjFn? i with
      | none => tthrow "projection function not found 2"
      | some projFn => fromExpr $ Lean.mkApp (Lean.mkAppN (Lean.mkConst projFn us) params) major

  partial def fromExpr (e : Lean.Expr) : TransM Expr := do
    let lvls := (← read).lvlParams
    let noLVarNormalize := (← read).noLVarNormalize
    let tup := (lvls, noLVarNormalize, e)
    if let some e' := (← get).cache.get? tup then
      return e'
    let e' ← fromExpr' e
    modify fun s => {s with cache := s.cache.insert tup e'}
    pure e'
    -- fromExpr' e

  partial def fromExpr' : Lean.Expr → TransM Expr
    | .bvar _ => tthrow "unexpected bound variable encountered"
    | .sort lvl => do pure $ .app (.const `enc.Sort) (← fromLevel lvl) -- FIXME
    | .const name lvls => do
      if (← read).transDeps then
        transNamedConst name
      -- dbg_trace s!"translating const {name} with levels: {lvls} --> {repr $ ← lvls.mapM fromLevel}"
      pure $ (.appN (.const $ ← fixLeanName 1 name) (← lvls.mapM fun lvl => do
          let l ← fromLevel' lvl
          (l.inst).toExpr
        ))
    | e@(.app (.lam _ _ _ _) _) => do
      pure (← fromExpr $ ← Lean.Core.betaReduce e) -- immediately reduce beta-redexes, as unannotated lambdas are not allowed in Dedukti (FIXME can use full reduction once subsingleton elimination has been implemented)
    | .app fnc arg => do
      pure $ .app (← fromExpr fnc) (← fromExpr arg)
    | e@(.lam ..) => lambdaTelescope e fun domVars bod => do
      let (_, ret) ← domVars.foldrM (init := (1, (← withTypedFVars domVars $ fromExpr bod))) fun v (i, curr) => do
        pure (i + 1, (.lam v.fvarId!.name curr (← withTypedFVars domVars[:domVars.size - i] $ fromExprAsType (← inferType v))))
      pure ret
    | e@(.forallE ..) => forallTelescope e fun domVars img => do
      let (_, ret, _) ← domVars.foldrM (init := (domVars.size - 1, ← withTypedFVars domVars $ fromExpr img, ← levelFromInferredType img)) fun domVar (n, curr, s2) => do
        let dom ← inferType domVar
        let s1 ← levelFromInferredType dom
        let s3 := Level.imax s1 s2
        --(.pi (.appN (.const `El) [(.var 0)]) (.app (.const `Univ) (.var 3)))
        let ret ← withTypedFVars domVars[:n] do -- TODO probably not necessary to do `withTypedFVars` here (can get domain from (← read).fvarTypes, and the sorts shouldn't contain free variables)
          pure (.appN (.const `enc.Pi) [← s1.toExpr, ← s2.toExpr, ← s3.toExpr, ← fromExpr dom, (.lam domVar.fvarId!.name curr (← fromExprAsType dom))])
        pure (n - 1, ret, s3)
      pure ret
    | .letE name T val bod _ => -- TODO recursive lets (with references in type)?
      withLetDecl name T val fun x => do
        -- if (← read).constName == `Array.insertIdx.loop.eq_def then
        --   dbg_trace s!"DBG[1]: {x}"
        let bod := bod.instantiate1 x
        let dbg := (← read).constName == (← fixLeanName 0 `Array.swap)
        -- if dbg then
        --   dbg_trace s!"DBG[1]: {(← read).numLets}, {(← read).fvars}\n{val}"
        let mut (_, (usedFVars : Lean.NameSet)) ← (← read).fvars.foldrM (init := (#[], default)) fun fvar (doms, acc) => do
          if val.containsFVar fvar.fvarId! || doms.any (·.containsFVar fvar.fvarId!) then
            -- if dbg then
            --   dbg_trace s!"DBG[4]: Trans.lean:109 {fvar}, {(← inferType fvar)}"
            let doms := doms.push (← inferType fvar)
            let acc := acc.insert fvar.fvarId!.name
            return (doms, acc)
          pure (doms, acc)

        for (lvar, (fvarDeps, _)) in (← read).lvars do
          if val.containsFVar (.mk lvar) then
            for fvar in fvarDeps do
              usedFVars := usedFVars.insert fvar.fvarId!.name

        let fvars := (← read).fvars.toList.filter (usedFVars.contains ·.fvarId!.name)
        -- if dbg then
        --   dbg_trace s!"DBG[5]: Trans.lean:116: fvars={fvars}"
        let typ ← fvars.foldrM (init := ← fromExprAsType T) fun fvar acc => do
          let name := fvar.fvarId!.name
          let some dom ← do pure $ (← read).fvarTypes.find? name | tthrow s!"could not find type of free variable"
          pure $ .pi name dom acc
        let typ := (← read).lvlParams.foldr (init := typ) fun n curr => .pi n (.const `lvl.Lvl) curr

        let val ← fromExpr val
        let letName ← nextLetName
        let vars := (← read).lvlParams ++ fvars.map (·.fvarId!.name)

        let mut levels := []
        for param in (← read).lvlParams do
          levels := [.var param] ++ levels
        let lhs := (.appN (.const letName) (levels ++ (← fvars.mapM (fun fvar => fromExpr fvar))))
        -- if dbg then
        --   dbg_trace s!"DBG[6]: Trans.lean:131: lhs={repr val}"

        -- dbg_trace s!"{name} ({letName}): {typ.dbgToString}"

        let const := .definable letName typ [.mk vars.toList lhs val]
        modify fun s => { s with env := {s.env with constMap := s.env.constMap.insert letName const} }
        withLet (x.fvarId!.name) fvars.toArray $ fromExpr bod
    | .lit (.strVal s) => do pure $ .fixme "STRLIT.FIXME" -- FIXME
    | .lit (.natVal n) => do
      if n < 10 then
        fromExpr $ natLitToConstructor n
      else
        pure $ .fixme s!"NATLIT.{n}.FIXME" -- FIXME
    | .proj n i s => do
      let sType' ← inferType s
      let sType ← whnf sType'
      let typeCtor := sType.getAppFn
      let .const I lvls := typeCtor | unreachable!
      let .some (.inductInfo iInfo) := (← read).env.find? I | unreachable!
      let params := sType.getAppArgs[:iInfo.numParams]
      mkProjFn n lvls params i s
    | e@(.fvar id) => do 
      match (← read).fvars.contains e with
      | true => pure $ .var id.name
      | false =>
        match (← read).lvars.find? id.name with
        | some (fvars, constName) => do
          let letVarApp ← (← read).lvlParams.foldlM (init := (.const constName))
            fun app n => do pure $ .app app $ .var n
          fvars.foldlM (init := letVarApp)
            fun app n => do pure $ .app app $ .var n.fvarId!.name
        | _ => tthrow s!"encountered unknown free variable {e}"
    | .mvar ..  => pure $ .fixme "MVAR.FIXME" -- FIXME
    | .mdata _ e => fromExpr e

  partial def fromExprAsType (e : Lean.Expr) : TransM Expr := do
    pure $ .appN (.const `enc.El) [← (← levelFromInferredType e).toExpr, (← fromExpr e)]

  partial def withTypedFVars {α : Type} (fvars : Array Lean.Expr) (m : TransM α) : TransM α := do
    let (fvarTypes, fvars) ← fvars.foldlM (init := (default, #[])) fun (fvarTypes, fvars) fvar => do
      let xDecl ← getFVarLocalDecl fvar
      let leanType ← match xDecl with
      | .cdecl (type := t) .. => pure t
      | _ => tthrow s!"encountered unexpected let variable in list of free variables"
      let type ← withFVars fvarTypes fvars $ fromExprAsType leanType -- TODO thunk this?
      pure (fvarTypes.insert fvar.fvarId!.name type, fvars.push fvar)
    withFVars fvarTypes fvars m

  partial def constFromConstantInfo (env : Lean.Environment) (cnst : Lean.ConstantInfo) : TransM Const := do
  withNewConstant (← fixLeanName 2 cnst.name) $ withResetCtx $ withLvlParams cnst.levelParams do
    let name := (← read).constName
    let type ← fromExprAsType cnst.type
    let type := (← read).lvlParams.foldr (init := type) fun n curr => .pi n (.const `lvl.Lvl) curr
    match cnst with
    | .axiomInfo    (_ : Lean.AxiomVal) => pure $ .static name type
    | .defnInfo     (val : Lean.DefinitionVal)
    | .thmInfo      (val : Lean.TheoremVal) => do
      if ← Lean.isProjectionFn val.name then
        -- dbg_trace s!"projection function detected: {val.name}"
        -- make projection rule
        let some projInfo ← Lean.getProjectionFnInfo? val.name | tthrow s!"impossible case"
        let ctor ← match env.find? projInfo.ctorName with
          | some c => pure c
          | _ => tthrow s!"impossible case"
        forallTelescope cnst.type fun params _ => do
          forallTelescope ctor.type fun ctorParams _ => do
            let params := params[:projInfo.numParams] -- FIXME how to instead restrict telescope above?
            let lvls := cnst.levelParams.map (Lean.Level.param ·)
            let ctorAppLean := Lean.mkAppN (.const ctor.name lvls) (ctorParams)
            let lhsLean := Lean.mkAppN (.const name lvls) (params ++ #[ctorAppLean])
            let rhsLean := ctorParams[params.size + projInfo.i]!

            -- maxS required for e.g. Subtype.property projection rewrite rule
            let (lhs, rhs) ← withNoLVarNormalize $ withTypedFVars (params ++ ctorParams) $ do pure (← fromExpr lhsLean, ← fromExpr rhsLean)

            pure $ .definable name type [.mk (cnst.levelParams.toArray ++ params.toArray.map (·.fvarId!.name) ++ ctorParams.map (·.fvarId!.name)).toList lhs rhs]
      else
        let value ← fromExpr val.value
        -- let value ← fromExpr $ ← reduceAll val.value -- FIXME use this version (mainly to shorten output code) once implemented subsingleton elimination (for the moment e.g. Unit.recOn is problematic)
        let value := (← read).lvlParams.foldr (init := value) fun n curr => .lam n curr (.const `lvl.Lvl)
        pure $ .definable name type [.mk [] (.const name) value]
    | .opaqueInfo   (_ : Lean.OpaqueVal) => pure $ .static name (.fixme "OPAQUE.FIXME") -- FIXME
    | .quotInfo     (val : Lean.QuotVal) =>
      match val.kind with
        | .type    -- `Quot`
        | .ctor => -- `Quot.mk`
          pure $ .static name type
        | .ind     -- `Quot.ind`
        | .lift => -- `Quot.lift`
          forallTelescope cnst.type fun domVars _ => do
            let lvls := cnst.levelParams.map (Lean.Level.param ·)
            withLocalDecls (← dupParams domVars[:domVars.size - 1]) λ params => do
              withLocalDecls (← dupParams domVars[:2]) λ instParams => do
                withLocalDecl default default (← inferType domVars[0]!) λ instArg => do
                  let ctorAppLean := Lean.mkAppN (.const `Quot.mk [lvls[0]!]) (instParams ++ [instArg])
                  let lhsLean := Lean.mkAppN (.const name lvls) (params ++ [ctorAppLean])
                  let fnArg := params[3]!
                  let rhsLean := Lean.mkApp fnArg instArg
                  let vars := cnst.levelParams ++ params.toList.map (·.fvarId!.name) ++ instParams.toList.map (·.fvarId!.name) ++ [instArg.fvarId!.name]
                  let (lhs, rhs) ← withTypedFVars (params ++ instParams ++ [instArg]) $ withNoLVarNormalize $ do pure (← fromExpr lhsLean, ← fromExpr rhsLean)
                  pure $ .definable name type [.mk vars lhs rhs]
    | .inductInfo   (_ : Lean.InductiveVal) => pure $ .static name type
    | .ctorInfo     (val : Lean.ConstructorVal) => do
      if Lean.isStructure env val.induct then
        forallTelescope cnst.type fun params outType => do
          withLocalDecl default default outType fun outVar => do
            let params := params[:params.size - val.numFields] -- will replace fields with projection applications
            let lvls := cnst.levelParams.map (Lean.Level.param ·)
            let some info := Lean.getStructureInfo? env val.induct | tthrow "impossible case"
            let projApps? ← info.fieldNames.mapM fun i => do
              match Lean.getProjFnForField? env val.induct i with
              | .some projFn => do
                if not ((← read).env.contains projFn) then
                  pure none
                else
                  pure $ .some $ Lean.mkAppN (.const projFn lvls) (params ++ #[outVar])
              | .none => tthrow "impossible case"
            if projApps?.any (·.isNone) then
              pure $ .static name type
            else
              let projApps := projApps?.map (·.get!)

              let lhsLean := Lean.mkAppN (.const name lvls) (params ++ projApps)
              let rhsLean := outVar
              let (lhs, rhs) ← withNoLVarNormalize $ withTypedFVars (params ++ #[outVar]) $ do pure (← fromExpr lhsLean, ← fromExpr rhsLean)
              -- dbg_trace s!"found struct: {ctor.name}"
              pure $ .definable name type [.mk ([outVar.fvarId!.name] ++ cnst.levelParams ++ params.toArray.toList.map (·.fvarId!.name)) lhs rhs] -- TODO make injective
      else
        pure $ .static name type
    | .recInfo      (val : Lean.RecursorVal) => do
      let lvls := cnst.levelParams.map (Lean.Level.param ·) |>.toArray
      let rules ← val.rules.foldlM (init := []) fun acc r => do
        -- dbg_trace s!"\nrule for ctor {r.ctor} ({r.nfields} fields, k = {val.k}, numParams = {val.numParams}, numIndices = {val.numIndices}): {r.rhs}\n"
        lambdaTelescope r.rhs fun domVars bod => do
          -- let some ctor := env.find? r.ctor | tthrow s!"could not find constructor {r.ctor}?!"

          let outType ← inferType bod
          -- -- sanity check
          -- if outType.getAppFn != motiveArg then tthrow s!"output type is not motive application" 
          let outArgs := outType.getAppArgs
          let idxArgsOrig := if outArgs.size > 1 then outArgs[:outArgs.size - 1].toArray else #[]
          let ctorAppOrig := outArgs[outArgs.size - 1]!
          -- let idxVars := idxArgsOrig.foldl (init := #[]) fun acc arg =>
          --   if arg.isFVar then acc ++ #[arg] else acc


          -- let numCtorLvls := ctor.levelParams.length
          -- let ctorLvlOffset := cnst.levelParams.length - ctor.levelParams.length-- if large-eliminating, first param is output sort

          withLocalDecls (← dupParams idxArgsOrig) λ newIdxVars => do -- use fresh parameter/index variables to avoid non-left-linearity
            withLocalDecls (← dupParams domVars[:val.numParams]) λ newParamVars => do -- FIXME better way than double-nesting?
              -- let idxArgsLean ← idxArgsOrig.mapM fun arg => reduce $ arg.replaceFVars idxVars newIdxVars -- reconstruct index arguments; must reduce because they appear on the LHS of the rewrite rule
              let ctorAppLean := ctorAppOrig.replaceFVars domVars[:val.numParams] newParamVars
              let lhsLean := Lean.mkAppN (.const name lvls.toList) $ domVars[:domVars.size - r.nfields] ++ newIdxVars ++ #[ctorAppLean]
              -- dbg_trace s!"{(← read).lvlParams.size}, {(← read).fvars.size}, {lhsLean}"

              let (lhs, rhs) ← withTypedFVars (domVars ++ newIdxVars ++ newParamVars) $ withNoLVarNormalize $ do pure (← fromExpr lhsLean, ← fromExpr bod)

              let vars := cnst.levelParams.toArray ++ domVars.map (·.fvarId!.name) ++ newParamVars.map (·.fvarId!.name) ++ newIdxVars.map (·.fvarId!.name)
              pure $ .mk vars.toList lhs rhs :: acc

      pure $ .definable name type rules

  partial def transConst (cinfo : Lean.ConstantInfo) : TransM Unit := do
    -- pre-mark as translated in order to prevent infinite looping with transDeps == true
    let name ← fixLeanName 3 cinfo.name
    modify fun s => { s with env := {s.env with constMap := s.env.constMap.insert name default} }
    let const ← constFromConstantInfo (← read).env cinfo
    let s ← get
    let s := { s with env := {s.env with constMap := s.env.constMap.insert (← fixLeanName 4 cinfo.name) const} }
    set s -- FIXME why can't use modify here?

  partial def transNamedConst (const : Name) : TransM Unit := do
    match (← get).env.constMap.find? (← fixLeanName 5 const) with -- only translate if not already translated
    | some _ => pure ()
    | none =>
      match (← read).env.constants.find? const with
      | some cinfo => if !cinfo.name.isImplementationDetail /- && !cinfo.name.isCStage -/ then -- FIXME
        transConst cinfo
      | none => tthrow s!"could not find constant \"{const}\" for translation, verify that it exists in the Lean input"

end

def translateEnv (consts : Lean.NameSet) (transDeps : Bool := false) : TransM Unit := do
  for const in consts do
    withTransDeps transDeps $ transNamedConst const

end Trans
