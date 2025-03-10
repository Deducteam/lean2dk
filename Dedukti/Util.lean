import Lean
open Lean

def charSubs := [
  -- ("»", "-_"),
  -- ("«", "_-"),
  (":", "_cln_"),
  -- TODO any other weird chars?
]

def fixLeanNameStr (name : String) : String := charSubs.foldl (init := name) fun acc (orig, sub) => acc.replace orig sub

def fixLeanName' : Name → Name
| .str p s   => .str (fixLeanName' p) $ fixLeanNameStr s
| .num p n   => .num (fixLeanName' p) n
| .anonymous => .anonymous

def fixLeanName (n : Name) : Name :=
  fixLeanName' n |>.toStringWithSep "_" false |>.toName
