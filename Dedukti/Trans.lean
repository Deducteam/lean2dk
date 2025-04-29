import Dedukti.Types
import Dedukti.Encoding
import Dedukti.Util

-- fromExpr 22

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

def _root_.Lean.Expr.containsLvlParam (e : Lean.Expr) (l : Name) : Bool :=
  e.instantiateLevelParams [l] [.zero] == e

def natLitToConstructor : Nat → Lean.Expr
  | 0 => natZero
  | n+1 => .app natSucc (natLitToConstructor n)

mutual
  partial def mkProjFn (induct : Name) (us : List Lean.Level) (params : Array Lean.Expr) (i : Nat) (major : Lean.Expr) : TransM Expr := do
    match ← getStructureInfo? (← read).env induct with
    | none => pure $ .fixme "PROJ.FIXME"
    | some info => match info.getProjFn? i with
      | none => tthrow "projection function not found 2"
      | some projFn => fromExpr 0 $ Lean.mkApp (Lean.mkAppN (Lean.mkConst projFn us) params) major

  partial def fromExpr (n : Nat) (e : Lean.Expr) : TransM Expr := do
    -- dbg_trace s!"DBG[10]: Trans.lean:60 (after partial def fromExpr {n}, {e}"
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
      pure (← fromExpr 1 $ ← Lean.Core.betaReduce e) -- immediately reduce beta-redexes, as unannotated lambdas are not allowed in Dedukti (FIXME can use full reduction once subsingleton elimination has been implemented)
    | .app fnc arg => do
      pure $ .app (← fromExpr 2 fnc) (← fromExpr 3 arg)
    | e@(.lam ..) => lambdaTelescope e fun domVars bod => do
      let (_, ret) ← domVars.foldrM (init := (1, (← withTypedFVars domVars $ fromExpr 4 bod))) fun v (i, curr) => do
        pure (i + 1, (.lam v.fvarId!.name curr (← withTypedFVars domVars[:domVars.size - i] $ fromExprAsType (← inferType v))))
      pure ret
    | e@(.forallE ..) => forallTelescope e fun domVars img => do
      let (_, ret, _) ← domVars.foldrM (init := (domVars.size - 1, ← withTypedFVars domVars $ fromExpr 5 img, ← levelFromInferredType img)) fun domVar (n, curr, s2) => do
        let dom ← inferType domVar
        let s1 ← levelFromInferredType dom
        let s3 := Level.imax s1 s2
        --(.pi (.appN (.const `El) [(.var 0)]) (.app (.const `Univ) (.var 3)))
        let ret ← withTypedFVars domVars[:n] do -- TODO probably not necessary to do `withTypedFVars` here (can get domain from (← read).fvarTypes, and the sorts shouldn't contain free variables)
          pure (.appN (.const `enc.Pi) [← s1.toExpr, ← s2.toExpr, ← s3.toExpr, ← fromExpr 6 dom, (.lam domVar.fvarId!.name curr (← fromExprAsType dom))])
        pure (n - 1, ret, s3)
      pure ret
    | .letE name T val bod _ =>
      withLetDecl name T val fun x => do
        let TType ← inferType T
        let bod := bod.instantiate1 x

        let checkContains' (doms : Array Lean.Expr) (f : Lean.Expr → Bool) : Bool := 
          f val || f T || f TType || doms.any (f ·)
        -- let dbg := (← read).constName == (← fixLeanName 0 `Array.swap)
        let mut (doms, (usedFVars : Lean.NameSet)) ← (← read).fvars.foldrM (init := (#[], default)) fun fvar (doms, acc) => do
          if checkContains' doms (·.containsFVar fvar.fvarId!) then
            let doms := doms.push (← inferType fvar)
            let acc := acc.insert fvar.fvarId!.name
            return (doms, acc)
          pure (doms, acc)

        let checkContains (f : Lean.Expr → Bool) : Bool := 
          checkContains' doms f

        for (lvar, (fvarDeps, _)) in (← read).lvars do
          if checkContains (·.containsFVar (.mk lvar)) then
            for fvar in fvarDeps do
              usedFVars := usedFVars.insert fvar.fvarId!.name

        let fvars := (← read).fvars.toList.filter (usedFVars.contains ·.fvarId!.name)
        -- if dbg then
        --   dbg_trace s!"DBG[5]: Trans.lean:116: fvars={fvars}"
        let mut usedLvlParams : Lean.NameSet := default
        for lvlParam in (← read).lvlParams do
          if checkContains (·.containsLvlParam lvlParam) then
            usedLvlParams := usedLvlParams.insert lvlParam

        let lvlParams := (← read).lvlParams.toList.filter (usedLvlParams.contains ·)

        let const ← withLvlParams lvlParams do
          let TTrans ← fromExprAsType T
          let typ ← fvars.foldrM (init := TTrans) fun fvar acc => do
            let name := fvar.fvarId!.name
            -- if (← read).constName == `Classical.em then
            let domTrans ← fromExprAsType (← inferType fvar)
            -- let some dom ← do pure $ (← read).fvarTypes.find? name | tthrow s!"could not find type of free variable"
            pure $ .pi name domTrans acc

          let typ := lvlParams.foldr (init := typ) fun n curr => .pi n (.const `lvl.Lvl) curr

          let valTrans ← fromExpr 7 val
          let letName ← nextLetName
          let vars := lvlParams ++ fvars.map (·.fvarId!.name)

          let mut levels := []
          for param in lvlParams do
            levels := levels ++ [.var param]
          let lhs := (.appN (.const letName) (levels ++ (← fvars.mapM (fun fvar => fromExpr 8 fvar))))
          -- if dbg then
          --   dbg_trace s!"DBG[6]: Trans.lean:131: lhs={repr val}"

          -- dbg_trace s!"{name} ({letName}): {typ.dbgToString}"

          pure $ Const.definable letName typ [.mk vars lhs valTrans]
        addConst (← read).modName const.name const

        withLet (x.fvarId!.name) fvars.toArray lvlParams.toArray $ fromExpr 9 bod
    | .lit (.strVal s) => do pure $ .fixme "STRLIT.FIXME" -- FIXME
    | .lit (.natVal n) => do
      if n < 10 then
        fromExpr 10 $ natLitToConstructor n
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
        | some (fvars, lvlParams, constName) => do
          let lvls ← lvlParams.toList.mapM fun param => do
            let l ← fromLevel' (.param param)
            (l.inst).toExpr

          let letVarApp := .appN (.const constName) lvls
            -- fun app n => do
            --   dbg_trace s!"DBG[14]: Trans.lean:188 {constName}, {n}"
            --   pure $ .app app $ .var n -- TODO FIXME properly translate universe levels
          fvars.foldlM (init := letVarApp)
            fun app n => do pure $ .app app $ .var n.fvarId!.name
        | _ => tthrow s!"encountered unknown free variable {e}"
    | .mvar ..  => pure $ .fixme "MVAR.FIXME" -- FIXME
    | .mdata _ e => fromExpr 11 e

  partial def fromExprAsType (e : Lean.Expr) : TransM Expr := do
    pure $ .appN (.const `enc.El) [← (← levelFromInferredType e).toExpr, (← fromExpr 12 e)]

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
  withNewConstant cnst.name $ withResetCtx $ withLvlParams cnst.levelParams do
    let name := (← read).constName
    let nameOrig := (← read).constNameOrig
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
            let lhsLean := Lean.mkAppN (.const nameOrig lvls) (params ++ #[ctorAppLean])
            let rhsLean := ctorParams[params.size + projInfo.i]!

            -- maxS required for e.g. Subtype.property projection rewrite rule
            let (lhs, rhs) ← withNoLVarNormalize $ withTypedFVars (params ++ ctorParams) $ do pure (← fromExpr 13 lhsLean, ← fromExpr 14 rhsLean)

            pure $ .definable name type [.mk (cnst.levelParams.toArray ++ params.toArray.map (·.fvarId!.name) ++ ctorParams.map (·.fvarId!.name)).toList lhs rhs]
      else
        let value ← fromExpr 15 val.value
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
                  let lhsLean := Lean.mkAppN (.const nameOrig lvls) (params ++ [ctorAppLean])
                  let fnArg := params[3]!
                  let rhsLean := Lean.mkApp fnArg instArg
                  let vars := cnst.levelParams ++ params.toList.map (·.fvarId!.name) ++ instParams.toList.map (·.fvarId!.name) ++ [instArg.fvarId!.name]
                  let (lhs, rhs) ← withTypedFVars (params ++ instParams ++ [instArg]) $ withNoLVarNormalize $ do pure (← fromExpr 16 lhsLean, ← fromExpr 17 rhsLean)
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

              let lhsLean := Lean.mkAppN (.const nameOrig lvls) (params ++ projApps)
              let rhsLean := outVar
              let (lhs, rhs) ← withNoLVarNormalize $ withTypedFVars (params ++ #[outVar]) $ do pure (← fromExpr 18 lhsLean, ← fromExpr 19 rhsLean)
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
              let lhsLean := Lean.mkAppN (.const nameOrig lvls.toList) $ domVars[:domVars.size - r.nfields] ++ newIdxVars ++ #[ctorAppLean]
              -- dbg_trace s!"{(← read).lvlParams.size}, {(← read).fvars.size}, {lhsLean}"

              let (lhs, rhs) ← withTypedFVars (domVars ++ newIdxVars ++ newParamVars) $ withNoLVarNormalize $ do pure (← fromExpr 20 lhsLean, ← fromExpr 21 bod)

              let vars := cnst.levelParams.toArray ++ domVars.map (·.fvarId!.name) ++ newParamVars.map (·.fvarId!.name) ++ newIdxVars.map (·.fvarId!.name)
              pure $ .mk vars.toList lhs rhs :: acc

      pure $ .definable name type rules

  partial def transConst (cinfo : Lean.ConstantInfo) : TransM Unit := do
    -- pre-mark as translated in order to prevent infinite looping with transDeps == true
    let name ← fixLeanName 3 cinfo.name
    let modName ← getModName cinfo.name

    let mut numConsts := 0
    for (_, constMap) in (← get).env.constModMap do
      numConsts := numConsts + constMap.size
    if numConsts > 0 && numConsts % 1000 == 0 then
      dbg_trace s!"{numConsts}/{(← read).consts.size} constants translated"

    addConst modName name default
    let const ← constFromConstantInfo (← read).env cinfo
    -- let s ← get
    addConst modName name const
    -- set s -- FIXME why can't use modify here?

  partial def transNamedConst (const : Name) : TransM Unit := do
    match (← getConstMap const).find? (← fixLeanName 5 const) with -- only translate if not already translated
    | some _ => pure ()
    | none =>
      match (← read).env.constants.find? const with
      | some cinfo => if !cinfo.name.isImplementationDetail /- && !cinfo.name.isCStage -/ then -- FIXME
        transConst cinfo
      | none => tthrow s!"could not find constant \"{const}\" for translation, verify that it exists in the Lean input"

end

def translateEnv (transDeps : Bool := false) : TransM Unit := do
  for const in (← read).consts do
    withTransDeps transDeps $ transNamedConst const

end Trans
