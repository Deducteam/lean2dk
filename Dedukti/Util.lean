import Lean
open Lean

def fixLeanName (name : Name) : Name := name.toStringWithSep "_" false -- TODO what does the "escape" param do exactly?
