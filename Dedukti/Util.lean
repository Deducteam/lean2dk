import Lean
open Lean

def charSubs := [
  -- ("»", "-_"),
  -- ("«", "_-"),
  (":", "_cln_"),
  ("@", "_at_"),
  -- TODO any other weird chars?
]

def fixLeanNameStr (name : String) : String := charSubs.foldl (init := name) fun acc (orig, sub) => acc.replace orig sub

def fixLeanName' : Name → Name
| .str p s   => .str (fixLeanName' p) $ fixLeanNameStr s
| .num p n   => .num (fixLeanName' p) n
| .anonymous => .anonymous

def fixLeanName (id : Nat) (n : Name) : Name := Id.run $ do
  let ret ← fixLeanName' n |>.toStringWithSep "_" false |>.toName
  if ret == Name.anonymous then
    dbg_trace s!"WARNING ({id}): Could not translate name '{n}'"
  pure ret
