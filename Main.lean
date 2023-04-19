import Lean

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

def main (args : List String) : IO UInt32 := do
  let path := ⟨"Test.lean"⟩
  let (leanEnv, success) ← Lean.Elab.runFrontend (← IO.FS.readFile path) default path.toString default
  if not success then
    throw $ IO.userError $ "elab failed"
  IO.println s!"number of constants: {leanEnv.constants.size}"
  let some testDef := leanEnv.find? `test | throw $ IO.userError $ "failed to find definition"
  IO.println s!"test definition: {repr testDef}"
  --pure
  return 0
