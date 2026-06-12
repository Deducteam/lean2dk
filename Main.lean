import Dedukti.Trans
import Dedukti.Print
import Cli
import Lean.Replay
import Lean4Less.Replay
import Lean4Less.Commands
import Lean4Less.TypeChecker
import Lean4Lean.Commands
import Dedukti.Util

open Dedukti

abbrev RED        := "\x1b[31m"
abbrev YELLOW     := "\x1b[1;33m"
abbrev BLUE       := "\x1b[0;34m"
abbrev LIGHT_BLUE := "\x1b[1;34m"
abbrev LIGHT_GRAY := "\x1b[1;36m"
abbrev GREEN      := "\x1b[0;32m"
abbrev PURPLE     := "\x1b[0;35m"
abbrev NOCOLOR    := "\x1b[0m"

def eprintColor (color s : String) := IO.eprintln s!"{color}{s}{NOCOLOR}"
def printColor (color s : String) := IO.println s!"{color}{s}{NOCOLOR}"

/-- Nat operations whose Dedukti reduction on a bignum operand is infeasible (Dedukti has no
    native arithmetic; it would unfold to a unary `Nat.succ` chain). `Nat.decEq`/`BEq.beq` are
    included because `Lean4Less.reduceNat` does *not* intercept them — so the dynamic
    `natPrimOpStubThreshold` check during patching never fires on e.g. `BEq.beq … fixedVar fixedVar`
    (lean4less stays lazy and never forces it), yet Dedukti's conversion checker would. -/
def natBigOpHeads : Lean.NameSet :=
  [``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.mod, ``Nat.div, ``Nat.gcd,
   ``Nat.beq, ``Nat.ble, ``Nat.decEq, ``instDecidableEqNat, ``BEq.beq]
  |>.foldl (·.insert ·) (Lean.NameSet.empty)

/-- Collect closed (no loose bvars / fvars) arguments that appear directly under a
    `natBigOpHeads` head anywhere in `e`. -/
partial def collectNatBigOpArgs (e : Lean.Expr) : Array Lean.Expr := Id.run do
  let mut acc : Array Lean.Expr := #[]
  match e.getAppFn with
  | .const n _ =>
    if natBigOpHeads.contains n then
      for a in e.getAppArgs do
        if !a.hasLooseBVars && !a.hasFVar then acc := acc.push a
  | _ => pure ()
  match e with
  | .app .. =>
    for a in e.getAppArgs do acc := acc ++ collectNatBigOpArgs a
  | .lam _ d b _ | .forallE _ d b _ => acc := acc ++ collectNatBigOpArgs d ++ collectNatBigOpArgs b
  | .letE _ t v b _ => acc := acc ++ collectNatBigOpArgs t ++ collectNatBigOpArgs v ++ collectNatBigOpArgs b
  | .mdata _ b => acc := acc ++ collectNatBigOpArgs b
  | .proj _ _ b => acc := acc ++ collectNatBigOpArgs b
  | _ => pure ()
  return acc

open Lean Lean.Meta in
/-- `true` if some `natBigOpHeads` application in `e` has an operand that evaluates (at `.all`
    transparency, matching Dedukti which ignores reducibility annotations) to a `Nat` literal
    exceeding `threshold`. -/
def hasLargeNatBigOp (e : Lean.Expr) (threshold : Nat) : MetaM Bool := do
  for a in collectNatBigOpArgs e do
    -- fast path: already a literal
    if let some v := a.rawNatLit? then
      if v > threshold then return true
      else continue
    unless a.isConst || a.isApp do continue
    let w? ← try pure (some (← withTransparency .all (whnf a))) catch _ => pure none
    if let some w := w? then
      if let some v := w.rawNatLit? then
        if v > threshold then return true
  return false

open Lean Lean.Meta in
/-- Static scan over `consts`: flag any constant whose value (or, failing that, type) applies a
    `Nat` operation to a bignum operand. Returns the names to value-stub. We always value-stub
    (keep the real type, drop the body): the infeasible reduction is only forced when *checking a
    body* against the type, so dropping the body suffices, and value-stubs don't taint users
    (their proofs reference the kept type as a postulate). -/
def scanLargeNatBigOps (consts : Lean.NameSet) (env : Lean.Environment) (threshold : Nat) :
    MetaM Lean.NameSet := do
  let mut valueAdd : Lean.NameSet := default
  for c in consts do
    let some ci := env.find? c | continue
    let inValue ← match ci.value? with
      | some v => hasLargeNatBigOp v threshold
      | none => pure false
    if inValue then
      valueAdd := valueAdd.insert c
    else if ← hasLargeNatBigOp ci.type threshold then
      valueAdd := valueAdd.insert c
  return valueAdd

/-- lean2dk does not translate `String` literals (it emits a `STRLIT.FIXME` placeholder, see
    `Trans.lean`), so any constant whose body contains one is ill-typed in Dedukti. These are
    incidental error/panic helpers (`mkPanicMessageWithDecl`, `List.get!Internal`, …). Detect
    and value-stub them (the type — a function over `String` — is fine; only the body with the
    literal is dropped). -/
partial def exprHasStrLit (e : Lean.Expr) : Bool :=
  (e.find? fun s => match s with | .lit (.strVal _) => true | _ => false).isSome

def scanStrLitConsts (consts : Lean.NameSet) (env : Lean.Environment) : Lean.NameSet := Id.run do
  let mut valueAdd : Lean.NameSet := default
  for c in consts do
    let some ci := env.find? c | continue
    if (match ci.value? with | some v => exprHasStrLit v | none => false) then
      valueAdd := valueAdd.insert c
  return valueAdd

structure ForEachModuleState where
  moduleNameSet : Std.HashSet Name := {}
  count := 0

-- def throwAlreadyImported (s : ImportState) (const2ModIdx : Std.HashMap Name ModuleIdx) (modIdx : Nat) (cname : Name) : IO α := do
--   let modName := s.moduleNames[modIdx]!
--   let constModName := s.moduleNames[const2ModIdx[cname]!.toNat]!
--   throw <| IO.userError s!"import {modName} failed, environment already contains '{cname}' from {constModName}"

abbrev ForEachModuleM := StateRefT ForEachModuleState IO

@[inline] nonrec def ForEachModuleM.run (x : ForEachModuleM α) (s : ForEachModuleState := {}) : IO α := do
  pure (← x.run s).1

open Lean in
partial def getLeafModules (imports : Array Import) : ForEachModuleM $ Array (Name × ModuleData) := do
  let mut leafs := #[]
  for i in imports do
    if i.runtimeOnly || (← get).moduleNameSet.contains i.module then
      continue
    let mFile ← findOLean i.module
    unless (← mFile.pathExists) do
      throw <| IO.userError s!"object file '{mFile}' of module {i.module} does not exist"
    let (mod, _) ← readModuleData mFile
    let modLeafs ← getLeafModules mod.imports
    if modLeafs.size == 0 then
      modify fun s => { s with moduleNameSet := s.moduleNameSet.insert i.module }
      leafs := leafs.push (i.module, mod)
    leafs := leafs ++ modLeafs
  pure leafs

open Lean in
partial def getOrderedModules (env : Environment) : ForEachModuleM (Array Name) := do
  let imports := env.imports
  let mut ret := #[]
  while true do
    let leafs ← getLeafModules imports
    if leafs.size == 0 then break
    ret := ret ++ leafs.map (·.1)
  pure ret

open Cli

def printDkEnv (constMap : Lean.RBMap Name Const compare) (constsToModNames : Lean.RBMap Name Name compare) (only? : Option $ Lean.NameSet) (outFile : System.FilePath) (modName : Name) (nameMap : Std.HashMap Name Name) : IO Unit := do
  let printDeps := if let some _ := only? then false else true

  -- print Dedukti environment
  match (ExceptT.run (StateT.run (ReaderT.run (print constMap (deps := printDeps) modName) {constMap, constsToModNames}) default)) with
    | .error s => throw $ IO.userError s
    | .ok (_, s) =>
      let dkEnvString := "\n\n".intercalate s.out
      if let some only := only? then
        for name in only do
          let maxConstPrint := 400 -- FIXME make "constant"
          let name := nameMap.get! name
          let some constString := s.printedConsts.find? name | throw $ IO.userError s!"could not find symbol {name} in translated environment"
          let constString := if constString.length > maxConstPrint then constString.extract ⟨0⟩ ⟨maxConstPrint⟩ ++ "..." else constString
          IO.println $ "\n" ++ constString
      else
        let dkPrelude := "#REQUIRE normalize.\n"
        let dkEnvString := dkPrelude ++ dkEnvString ++ "\n"
        IO.FS.writeFile outFile dkEnvString

abbrev auxLvlModName := `AuxLvls

unsafe def runTransCmd (p : Parsed) : IO UInt32 := do
  let moduleArg := p.positionalArg! "input" |>.value
  let module := moduleArg.toName
  if module == .anonymous then throw <| IO.userError s!"Could not resolve module: {moduleArg}"
  -- TODO better way to print with colors?
  IO.println s!"\n{BLUE}>> Translation module: {YELLOW}{module}{NOCOLOR}"
  let onlyConsts? := p.flag? "only" |>.map fun setPathsFlag => 
    setPathsFlag.as! (Array String)

  let elim := not $ p.hasFlag "no-elim"
  let all := p.hasFlag "all"

  IO.println s!"\n{BLUE}>> Elaborating... {YELLOW}\n"
  let searchPath? := p.flag? "search-path" |>.map fun sp => 
    sp.as! String
  match searchPath? with
  | .some sp =>
    let path := System.FilePath.mk sp
    Lean.searchPathRef.set [path]
  | _ => Lean.initSearchPath (← Lean.findSysroot)
  Lean4Less.withImportModuleAndPatchDefs module (elabPatch := elim) fun env => do
    let overrides := if elim then Lean4Less.getOverrides env.toKernelEnv else default
    let mut write := true
    IO.println s!"{NOCOLOR}"

    let mut onlyConstsArr := #[]
    if let some _onlyConsts := onlyConsts? then
      write := (not $ p.hasFlag "print") || p.hasFlag "write"
      printColor BLUE s!">> Using CLI-specified constants: {_onlyConsts}..."
      onlyConstsArr := _onlyConsts.map (·.toName)
    else if not all then
      printColor BLUE s!">> Using all constants from given module: {module}..."
      let some moduleIdx := Lean.Environment.getModuleIdx? env module | throw $ IO.userError s!"main module {module} not found"
      let moduleConstNames := env.header.moduleData.get! moduleIdx |>.constNames.toList
      onlyConstsArr := ⟨moduleConstNames⟩
    else 
      let constNames := env.constants.toList.map (·.1)
      onlyConstsArr := ⟨constNames⟩

    let mut onlyConstsInit := onlyConstsArr.foldl (init := default) fun acc const =>
      if !const.isImplementationDetail && !const.isCStage then acc.push const else acc

    let getProjFns deps env := do
      let mut projFns := #[]
      for (n, info) in deps do
        if let .inductInfo _ := info then
          if Lean.isStructure env n then
            let si := Lean.getStructureInfo env n
            let mut i := 0
            while true do
              if let some pn := si.getProjFn? i then
                let .some pi := env.find? pn | throw $ IO.userError s!"could not find projection function {pn}"
                projFns := projFns.push (pn, pi)
              else break
              i := i + 1
      pure projFns

    let mut patchConstsDeps := ← if elim then Lean4Lean.getDepConstsEnv env (Lean4Less.patchConsts) overrides else pure default
    for (pn, pi) in  ← getProjFns patchConstsDeps env do
      patchConstsDeps := patchConstsDeps.insert pn pi

    let mut patchConsts := default
    for (pn, _) in patchConstsDeps do
      patchConsts := patchConsts.insert pn

    let mut onlyConstsDeps' ← Lean4Lean.getDepConstsEnv env (onlyConstsInit) overrides
    onlyConstsInit := #[]
    let mut onlyConstsDeps := default
    for (n, ci) in onlyConstsDeps' do
      if not (patchConstsDeps.contains n) then
        if !ci.isUnsafe && !ci.isPartial then
          onlyConstsDeps := onlyConstsDeps.insert n ci
          onlyConstsInit := onlyConstsInit.push n

    for (pn, pi) in  ← getProjFns onlyConstsDeps env do
      onlyConstsDeps := onlyConstsDeps.insert pn pi
    
    -- Base sets of constants whose kernel check hit an infeasible primitive `Nat` op
    -- (see `Lean4Less.natPrimOpStubThreshold`): `valueStubBase` if the op was in the body/value
    -- (type is fine), `typeStubBase` if it was in the type (the type itself is unusable).
    let mut valueStubBase : Lean.NameSet := default
    let mut typeStubBase : Lean.NameSet := default
    let env ← do
      if elim then
        let addDecl := if elim then Lean4Less.addDecl (opts := {proofIrrelevance := elim, kLikeReduction := elim}) else Lean4Lean.addDecl

        let (kenv, _, vs, ts) ← Lean4Lean.replay addDecl {newConstants := patchConstsDeps, opts := {proofIrrelevance := not elim, kLikeReduction := not elim}, overrides} (← Lean.mkEmptyEnvironment).toKernelEnv (printProgress := true) (op := "patch")
        let env := Lean4Lean.updateBaseAfterKernelAdd env kenv
        -- threading the stub sets so the second replay accumulates stubs from the first
        let (kenv, _, vs, ts) ← Lean4Lean.replay addDecl {newConstants := onlyConstsDeps, opts := {proofIrrelevance := not elim, kLikeReduction := not elim}, overrides} kenv (printProgress := true) (op := "patch") (valueStubbed := vs) (typeStubbed := ts)
        let env := Lean4Lean.updateBaseAfterKernelAdd env kenv
        valueStubBase := vs
        typeStubBase := ts
        onlyConstsDeps ← Lean4Lean.getDepConstsEnv env onlyConstsInit overrides
        for (pn, pi) in  ← getProjFns onlyConstsDeps env do
          onlyConstsDeps := onlyConstsDeps.insert pn pi

        -- L4L_RECHECK: re-typecheck the *patched* dep-closure with plain lean4lean
        -- (timing via L4L_TIME_ALL, cache toggle via L4L_NO_CACHE). This measures how
        -- much the kernel's memoization accounts for its speed on the patched terms that
        -- Dedukti chokes on. Reuses Lean4Lean.replay so prim-op stubs are skipped.
        if (← IO.getEnv "L4L_RECHECK").isSome then
          IO.println ">> L4L_RECHECK: re-typechecking patched dep-closure with plain lean4lean"
          let _ ← Lean4Lean.replay Lean4Lean.addDecl {newConstants := onlyConstsDeps, opts := {proofIrrelevance := false, kLikeReduction := false}, overrides} (← Lean.mkEmptyEnvironment).toKernelEnv (printProgress := false) (op := "typecheck") (valueStubbed := vs) (typeStubbed := ts)

        pure env
      else
        pure env

    let constsNames : Lean.NameSet := onlyConstsDeps.keys.foldl (init := default) fun acc const => acc.insert const |>.union $ patchConstsDeps.keys.foldl (init := default) fun acc const => acc.insert const

    -- Static scan for bignum `Nat` operations the dynamic patch-time check misses. The
    -- `natPrimOpStubThreshold` throw only fires when lean4less *forces* a `reduceNat`-intercepted
    -- op (`Nat.add`/`mul`/`beq`/…) to a bignum literal. It misses `Nat.decEq`/`BEq.beq` (not
    -- intercepted by `reduceNat`) and, more fundamentally, any op lean4less never forces because
    -- it stays lazy (e.g. `BEq.beq … Nat.Linear.fixedVar fixedVar`, fixedVar = 10^8, in
    -- `denote.toPoly.go`). Dedukti's conversion *would* force the unary reduction and diverge, so
    -- we value-stub the enclosing constant here.
    if elim then
      let coreCtx : Lean.Core.Context := { fileName := "<largeNatScan>", fileMap := default, options := default }
      let coreState : Lean.Core.State := { env }
      let (vsScan, _) ← (Lean.Meta.MetaM.run'
        (scanLargeNatBigOps constsNames env Lean4Less.TypeChecker.Inner.natPrimOpStubThreshold)).toIO coreCtx coreState
      let newOnes := vsScan.fold (fun acc c => if valueStubBase.contains c || typeStubBase.contains c then acc else acc.insert c) (Lean.NameSet.empty)
      if newOnes.size > 0 then
        printColor YELLOW s!">> Static scan flagged {newOnes.size} additional constant(s) with bignum Nat operations (value-stubbing)"
        valueStubBase := valueStubBase.union newOnes

      -- String literals are untranslated (STRLIT.FIXME); value-stub constants using them.
      let strLitConsts := scanStrLitConsts constsNames env
      let newStr := strLitConsts.fold (fun acc c => if valueStubBase.contains c || typeStubBase.contains c then acc else acc.insert c) (Lean.NameSet.empty)
      if newStr.size > 0 then
        printColor YELLOW s!">> Static scan flagged {newStr.size} constant(s) using String literals (value-stubbing)"
        valueStubBase := valueStubBase.union newStr

    -- Force-stub: constants listed in `dk/force_stub.txt` (one Lean name per line; blank
    -- lines and `--`/`#` comments ignored) are value-stubbed. For constants whose Dedukti
    -- check is intractable for reasons the static bignum scan can't see -- e.g.
    -- `Nat.Linear.ExprCnstr.denote_toNormPoly`, whose translated structure-eta-recursor normal
    -- form is exponentially large (finite, but not feasibly checkable; see docs). Value-stub
    -- (real type kept, body dropped) is sound for these `omega`/linear-arith internals.
    let forceStubPath : System.FilePath := ((← IO.Process.getCurrentDir).join "dk").join "force_stub.txt"
    if ← forceStubPath.pathExists then
      let contents ← IO.FS.readFile forceStubPath
      let mut forced : Lean.NameSet := default
      for line in contents.splitOn "\n" do
        let s := line.trim
        unless s.isEmpty || s.startsWith "--" || s.startsWith "#" do
          forced := forced.insert s.toName
      let newForced := forced.fold (fun acc c => if valueStubBase.contains c || typeStubBase.contains c then acc else acc.insert c) Lean.NameSet.empty
      if newForced.size > 0 then
        printColor YELLOW s!">> Force-stubbing {newForced.size} constant(s) from dk/force_stub.txt (value-stub)"
        valueStubBase := valueStubBase.union newForced

    -- Cascade the stubbing over the dependency DAG (in Lean-name space):
    --  * a constant whose *type* references a type-stubbed constant must itself be type-stubbed;
    --  * a constant whose *value* references a type-stubbed constant must be value-stubbed.
    -- (Value-stubs keep their real type and do not propagate; only type-stubs taint users.)
    let usedIn (e? : Option Lean.Expr) : Lean.NameSet :=
      match e? with
      | some e => e.getUsedConstants.foldl (·.insert ·) default
      | none => default
    -- A value-stubbed function `f` no longer reduces, so its auto-generated equation /
    -- unfolding lemmas (`f.eq_1`, `f.eq_def`, `f._eq_1`, `f._sunfold`, `f._unfold`, …),
    -- whose proofs are `rfl`, would fail to typecheck in Dedukti (the `rfl` needs `f` to
    -- reduce). Value-stub them too.
    let isEqnLemmaSuffix (s : String) : Bool :=
      s.startsWith "eq_" || s.startsWith "_eq_" || s == "eq_def" || s == "_sunfold" || s == "_unfold"
    let mut typeStub := typeStubBase
    let mut valueStub := valueStubBase
    let mut changed := true
    while changed do
      changed := false
      for c in constsNames do
        let some ci := env.find? c | continue
        if !typeStub.contains c && (usedIn (some ci.type)).any (typeStub.contains ·) then
          typeStub := typeStub.insert c; changed := true
        else if !typeStub.contains c && !valueStub.contains c && (usedIn ci.value?).any (typeStub.contains ·) then
          valueStub := valueStub.insert c; changed := true
        else if !typeStub.contains c && !valueStub.contains c
            && (match c with | .str parent last => valueStub.contains parent && isEqnLemmaSuffix last | _ => false) then
          valueStub := valueStub.insert c; changed := true
    -- type-stubbed constants are not value-stubbed (type-stub subsumes)
    valueStub := valueStub.fold (fun acc c => if typeStub.contains c then acc else acc.insert c) default
    if valueStub.size > 0 || typeStub.size > 0 then
      printColor YELLOW s!">> Stubbing {valueStub.size} value + {typeStub.size} type constant(s) requiring infeasible primitive Nat computation"
    -- let (onlyConsts, env) ← Lean4Lean.replay env onlyConstsDeps (Lean4Less.addDecl (opts := {proofIrrelevance := true, kLikeReduction := true})) (printErr := true) (overrides := default) (printProgress := true) (initConsts := Lean4Less.patchConsts)

    -- let ignoredConsts := onlyConstsInit.diff onlyConsts
    -- if ignoredConsts.size > 0 then
    --   printColor RED s!"WARNING: Skipping translation of {ignoredConsts.size} constants: {ignoredConsts.toArray}..."

    -- printColor BLUE s!">> Translating {onlyConsts.size} constants: {onlyConsts.toArray}..."
    printColor BLUE s!">> Translating {onlyConstsDeps.size} constants..."

    -- translate elaborated Lean environment to Dedukti
    let (_, {env := dkEnv, names := nameMap, ..}) ← (Trans.translateEnv (transDeps := write)).toIO { options := default, fileName := "", fileMap := default } {env} {env, patchConsts, consts := constsNames, valueStubConsts := valueStub, typeStubConsts := typeStub, orderedModules := ← getOrderedModules env |>.run}

    -- let write := if let some _ := onlyConsts? then (p.hasFlag "write") else true -- REPORT why does this not work?

    let mut constsToModNames := default
    let fixModName n :=
      n |>.toStringWithSep "_" false |>.toName
    for (mod, constMap) in dkEnv.constModMap do
      for (constName, _) in constMap do
        constsToModNames := constsToModNames.insert constName (fixModName mod)

    for (auxLvlName, _) in dkEnv.auxLvlMap do
      constsToModNames := constsToModNames.insert auxLvlName auxLvlModName

    IO.print s!"{PURPLE}"
    let outDir := ((← IO.Process.getCurrentDir).join "dk" |>.join "out")
    if (← outDir.pathExists) then
      IO.FS.removeDirAll outDir
    IO.FS.createDirAll outDir
    if write then
      let printMod mod constMap := do
        dbg_trace s!"printing module: {mod} ({constMap.size} constants)"
        let outFile := (outDir.join ↑((fixModName mod).toString ++ ".dk"))
        printDkEnv constMap constsToModNames none outFile mod nameMap

      printMod auxLvlModName dkEnv.auxLvlMap
      for (mod, constMap) in dkEnv.constModMap do
        printMod mod constMap

      -- Record the stubbed constants (could not be faithfully checked in Dedukti because they
      -- require primitive Nat computation) for the user to review.
      if valueStub.size > 0 || typeStub.size > 0 then
        let mut report := "-- Constants stubbed by lean2dk: their kernel check requires primitive Nat\n-- computation (Lean4Less.natPrimOpStubThreshold) that Dedukti cannot perform.\n"
        report := report ++ s!"\n-- type-stubbed ({typeStub.size}): declared with an opaque type (`name : Type.`), no body\n"
        for c in typeStub do report := report ++ s!"{c}\n"
        report := report ++ s!"\n-- value-stubbed ({valueStub.size}): real type kept, rewrite rule/value dropped\n"
        for c in valueStub do report := report ++ s!"{c}\n"
        IO.FS.writeFile (outDir.join "STUBBED.txt") report
        printColor YELLOW s!">> Wrote stubbed-constant report to dk/out/STUBBED.txt"

    -- if p.hasFlag "print" then
    --   printDkEnv dkEnv $ .some (onlyConstsArr.foldl (init := default) fun acc c => acc.insert c)
    IO.print s!"{NOCOLOR}"

    return 0

unsafe def transCmd : Cmd := `[Cli|
  transCmd VIA runTransCmd; ["0.0.1"]
  "Translate from Lean to Dedukti."

  FLAGS:
    s, "search-path" : String; "Set Lean search path directory."
    ne, "no-elim";             "Do not eliminate definitional equalities via Lean4Less translation (e.g. when using -s with a pre-translated library)."
    a, "all";                  "Also translate all constants from the dependencies of the specified module (not just the ones appearing in the module itself)"
    o, only : Array String;    "Only translate the specified constants and their dependencies."
    p, print;                  "Print translation of specified constants to standard output (relevant only with '-o ...')."
    w, write;                  "Also write translation of specified constants (with dependencies) to file (relevant only with '-p')."

  ARGS:
    input : String; "Input Lean module name (e.g. `Init.Classical`)."

  -- SUBCOMMANDS:
  --   installCmd;
  --   testCmd

  -- The EXTENSIONS section denotes features that
  -- were added as an external extension to the library.
  -- `./Cli/Extensions.lean` provides some commonly useful examples.
  EXTENSIONS:
    author "rish987"
]

unsafe def main (args : List String) : IO UInt32 := do
  transCmd.validate args
