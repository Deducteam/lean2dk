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
      | tthrow s!"unknown universe parameter {p} encountered"
     -- dbg_trace s!"{p}: {i}"
     pure $ .var i
     -- TODO deep encoding
     -- let some i := (← read).lvlParams.find? p
     --  | tthrow s!"unknown universe parameter {p} encountered"
     -- pure $ .var i 

  | .mvar _     => tthrow "unexpected universe metavariable encountered"

def fromLevel (l : Lean.Level) : TransM Expr := do (← fromLevel' l).toExpr

def levelFromExpr (expr : Lean.Expr) : TransM Level := do
  match expr with
    | .sort l => pure $ ← fromLevel' l
    | _ => tthrow s!"expected sort but encountered {expr.ctorName} -- {expr.dbgToString}"
    
def levelFromInferredType (e : Lean.Expr) : TransM Level := do
  levelFromExpr $ ← inferType e -- FIXME are we sure that this will be a .sort (as opposed to something that reduces to .sort)? if not, it may contain fvars

mutual
  partial def fromExpr : Lean.Expr → TransM Expr
    | .bvar _ => tthrow "unexpected bound variable encountered"
    | .sort lvl => do pure $ .app (.const `enc.Sort) (← fromLevel lvl) -- FIXME
    | .const name lvls => do
      if (← read).transDeps then
        transNamedConst name
      -- dbg_trace s!"translating const {name} with levels: {lvls} --> {repr $ ← lvls.mapM fromLevel}"
      pure $ (.appN (.const $ fixLeanName name) (← lvls.mapM fromLevel))
    | .app fnc arg => do pure $ .app (← fromExpr fnc) (← fromExpr arg)
    | e@(.lam ..) => lambdaTelescope e fun domVars bod => do
                                domVars.foldrM (init := (← withTypedFVars domVars $ fromExpr bod)) fun _ (curr) => do
                                  pure (.lam curr)
    | e@(.forallE ..) => forallTelescope e fun domVars img => do
                                let (ret, _) ← domVars.size.foldRevM (init := (← withTypedFVars domVars $ fromExpr img, ← levelFromExpr $ ← inferType img)) fun i (curr, s2) => do
                                  let domVar := domVars[i]!
                                  let dom ← inferType domVar
                                  let s1 ← levelFromInferredType dom -- FIXME are we sure that this will be a .sort (as opposed to something that reduces to .sort)? if not, it may contain fvars
                                  let s3 := Level.imax s1 s2
                                  --(.pi (.appN (.const `El) [(.var 0)]) (.app (.const `Univ) (.var 3)))
                                  let ret ← withTypedFVars domVars[:i] do -- TODO probably not necessary to do `withTypedFVars` here (can get domain from (← read).fvarTypes, and the sorts shouldn't contain free variables)
                                    pure (.appN (.const `enc.Pi) [← s1.toExpr, ← s2.toExpr, ← s3.toExpr, ← fromExpr dom, (.lam curr)])
                                  pure (ret, s3)
                                pure ret
    | .letE name typ val bod _ =>
      withLetDecl name typ val fun x => do
        let bod := bod.instantiate1 x

        let type ← (← read).fvars.foldrM (init := ← fromExprAsType typ) fun fvar acc => do
          let name := fvar.fvarId!.name
          let some dom ← do pure $ (← read).fvarTypes.find? name | tthrow s!"could not find type of free variable"
          pure $ .pi dom acc

        let val ← fromExpr val
        let letName ← nextLetName
        let fvars :=  (← read).fvars.toList
        let const := .definable letName type [.mk fvars.length (.appN (.const letName) (← fvars.mapM (fun fvar => fromExpr fvar))) val]
        modify fun s => { s with env := {s.env with constMap := s.env.constMap.insert letName const} }
        withLet (x.fvarId!.name) $ fromExpr bod
    | .lit lit => do pure $ .fixme "LIT.FIXME" -- FIXME
    | .proj _ idx exp => pure $ .fixme "PROJ.FIXME" -- FIXME
    | e@(.fvar id) => do 
                    match (← read).fvars.indexOf? e with
                    | some i => pure $ .var ((← read).fvars.size - 1 - i)
                    | _ =>
                      match (← read).lvars.find? id.name with
                      | some (nFvars, constName) =>
                        List.range nFvars |>.foldlM (init := (.const constName))
                          fun app i => do pure $ .app app $ .var $ (← read).fvars.size - 1 - i
                      | _ => tthrow s!"encountered unknown free variable {e}"
    | .mvar ..  => pure $ .fixme "MVAR.FIXME" -- FIXME
    | .mdata .. => pure $ .fixme "MDATA.FIXME" -- FIXME

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

  partial def constFromConstantInfo (env : Lean.Environment) (cnst : Lean.ConstantInfo) : TransM Const :=
  withNewConstant (fixLeanName cnst.name) $ withResetCtx $ withLvlParams cnst.levelParams do
    let name := (← read).constName
    let type ← fromExprAsType cnst.type
    let type := cnst.levelParams.foldr (init := type) fun _ curr => .pi (.const `lvl.Lvl) curr
    match cnst with
    | .axiomInfo    (val : Lean.AxiomVal) => pure $ .static name (.fixme "AXIOM.FIXME") -- FIXME
    | .defnInfo     (val : Lean.DefinitionVal)
    | .thmInfo      (val : Lean.TheoremVal) => do
      if ← Lean.isProjectionFn val.name then
        -- dbg_trace s!"projection function detected: {val.name}"
        let some projInfo ← Lean.getProjectionFnInfo? val.name | tthrow s!"impossible case"
        let numFields ← match env.find? projInfo.ctorName with
          | some (.ctorInfo { numFields := n, .. }) => pure n
          | _ => tthrow s!"impossible case"
        let numParams := projInfo.numParams
        let numLevels := cnst.levelParams.length -- FIXME non-left-linear universes (needed for now for Dedukti typechecker)
        let projAppPartial := (numLevels + numParams).foldRev (init := .const name) fun i app => .app app $ .var (i + numFields + numParams)
        let ctorApp := numLevels.foldRev (init := .const (fixLeanName projInfo.ctorName)) fun i app => .app app $ .var (i + numFields + numParams + numParams)
        let ctorApp := (numParams + numFields).foldRev (init := ctorApp) fun i app => .app app $ .var i
        if (← read).transDeps then
          transNamedConst projInfo.ctorName

        pure $ .definable name type [.mk (numLevels + numParams * 2 + numFields) (.app projAppPartial ctorApp) $ .var (numFields - projInfo.i - 1)]
      else
        let value ← fromExpr val.value
        let value := cnst.levelParams.foldr (init := value) fun _ curr => .lam curr
        pure $ .definable name type [.mk 0 (.const name) value]
    | .opaqueInfo   (val : Lean.OpaqueVal) => pure $ .static name (.fixme "OPAQUE.FIXME") -- FIXME
    | .quotInfo     (val : Lean.QuotVal) => pure $ .static name (.fixme "QUOT.FIXME") -- FIXME
    | .inductInfo   (val : Lean.InductiveVal) => pure $ .static name type
    | .ctorInfo     (val : Lean.ConstructorVal) => do
      if Lean.isStructure env val.induct then
        -- dbg_trace s!"found struct: {val.induct} with ctor: {name}"
        let ctor := Lean.getStructureCtor env val.induct
        let some info := Lean.getStructureInfo? env val.induct | tthrow "impossible case"

        let projFns ← info.fieldNames.mapM fun i =>
          match Lean.getProjFnForField? env val.induct i with
          | .some projFn => do
            if (← read).transDeps then
              transNamedConst projFn

            pure $ .const $ fixLeanName projFn
          | .none => tthrow "impossible case"

        let numLevels := val.levelParams.length
        let numParams := val.numParams -- FIXME non-left-linear universes (needed for now for Dedukti typechecker)
        let numVars := numLevels + numParams + numParams + 1 -- TODO don't have to worry about indices, right?

        -- make eta rule
        let ctorWithUnivs := numLevels.foldRev (init := .const name) fun i acc => .app acc (.var (i + numParams + numParams + 1))
        let ctorApp := val.numParams.foldRev (init := ctorWithUnivs) fun i acc => .app acc (.var (i + numParams + 1))

        let lhs := projFns.foldl (init := ctorApp)
          fun acc fn =>
            let prjApp := numLevels.foldRev (init := fn) fun i acc => .app acc (.var (i + numParams + numParams + 1))
            let prjApp := numParams.foldRev (init := prjApp) fun i acc => .app acc (.var (i + 1))
            .app acc (.app prjApp (.var 0))

        let rhs := .var 0

        -- dbg_trace s!"found struct: {ctor.name}"
        pure $ .definable name type [.mk numVars lhs rhs] -- TODO make injective
      else
        pure $ .static name type
    | .recInfo      (val : Lean.RecursorVal) => do
      let lvls := cnst.levelParams.map (Lean.Level.param ·) |>.toArray
      let rules ← val.rules.foldlM (init := []) fun acc r => do
        -- IO.print s!"\nrule for ctor {r.ctor} ({r.nfields} fields, k = {val.k}, numParams = {val.numParams}, numIndices = {val.numIndices}): {r.rhs}\n"
        lambdaTelescope r.rhs fun domVars bod => do
          -- let some ctor := env.find? r.ctor | tthrow s!"could not find constructor {r.ctor}?!"

          let outType ← inferType bod
          -- -- sanity check
          -- if outType.getAppFn != motiveArg then tthrow s!"output type is not motive application" 
          let outArgs := outType.getAppArgs
          let idxArgsOrig := if outArgs.size > 1 then outArgs[:outArgs.size - 1].toArray else #[]
          let ctorAppOrig := outArgs[outArgs.size - 1]!
          let idxVars := idxArgsOrig.foldl (init := #[]) fun acc arg =>
            if arg.isFVar then acc ++ #[arg] else acc


          -- let numCtorLvls := ctor.levelParams.length
          -- let ctorLvlOffset := cnst.levelParams.length - ctor.levelParams.length-- if large-eliminating, first param is output sort

          let dupParams (origParams : Array Lean.Expr) := origParams.foldlM (init := #[]) fun x param => do
            let paramType ← inferType param
            pure $ x.append #[(default, default, fun prevParams => pure $ paramType.replaceFVars origParams[:prevParams.size] prevParams)] -- FIXME do I need to generate unique names here? e.g. param.fvarId!.name ++ `New

          withLocalDecls (← dupParams idxArgsOrig) λ newIdxVars => do -- use fresh parameter/index variables to avoid non-left-linearity
            withLocalDecls (← dupParams domVars[:val.numParams]) λ newParamVars => do -- FIXME better way than double-nesting?
              -- let idxArgsLean ← idxArgsOrig.mapM fun arg => reduce $ arg.replaceFVars idxVars newIdxVars -- reconstruct index arguments; must reduce because they appear on the LHS of the rewrite rule
              let ctorAppLean := ctorAppOrig.replaceFVars domVars[:val.numParams] newParamVars
              let lhsLean := Lean.mkAppN (.const name lvls.toList) $ domVars[:domVars.size - r.nfields] ++ newIdxVars ++ #[ctorAppLean]
              -- dbg_trace s!"{(← read).lvlParams.size}, {(← read).fvars.size}, {lhsLean}"

              let (lhs, rhs) ← withTypedFVars (domVars ++ newIdxVars ++ newParamVars) $ withNoLVarNormalize $ do pure (← fromExpr lhsLean, ← fromExpr bod)

              let numVars := cnst.levelParams.length + domVars.size + newParamVars.size + newIdxVars.size
              pure $ .mk numVars lhs rhs :: acc

      pure $ .definable name type rules

  partial def transConst (cinfo : Lean.ConstantInfo) : TransM Unit := do
    -- pre-mark as translated in order to prevent infinite looping with transDeps == true
    modify fun s => { s with env := {s.env with constMap := s.env.constMap.insert (fixLeanName cinfo.name) default} }
    let const ← constFromConstantInfo (← read).env cinfo
    let s ← get
    let s := { s with env := {s.env with constMap := s.env.constMap.insert (fixLeanName cinfo.name) const} }
    set s -- FIXME why can't use modify here?

  partial def transNamedConst (const : Name) : TransM Unit := do
      match (← get).env.constMap.find? (fixLeanName const) with -- only translate if not already translated
      | some _ => pure ()
      | none =>
        match (← read).env.constants.find? const with
        | some cinfo => transConst cinfo
        | none => tthrow s!"could not find constant \"{const}\" for translation, verify that it exists in the Lean input"

end

def translateEnv (consts? : Option $ Array Name := none) (transDeps : Bool := false) : TransM Unit := do
  match consts? with
  | some consts =>
    for const in consts do
      withTransDeps transDeps $ transNamedConst const
  | none =>
    (← read).env.constants.forM (fun _ cinfo => do
      if !cinfo.name.isInternal then
        transConst cinfo
  )

end Trans
