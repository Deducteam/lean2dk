import Lean
import Std.Data.RBMap

notation "Name" => Lean.Name

instance : Ord Name where
  compare := Lean.Name.quickCmp

namespace Dedukti

mutual
  inductive Rule where
    | mk (vars : Nat) (lhs : Expr) (rhs : Expr)

  inductive Const where
    | static (name : Name) (type : Expr) 
    | definable (name : Name) (type : Expr) (rules : List Rule)
    deriving Repr

  inductive Expr
    | var (idx : Nat) 
    | const (name : Name)
    | fixme (msg : String)
    | app (fn : Expr) (arg : Expr)
    | lam (bod : Expr)
    | pi (dom : Expr) (img : Expr)
    | type
    | kind
    deriving Repr
end

structure Env where
  constMap : Std.RBMap Name Const compare
  deriving Inhabited

def Const.name : Const → Name
  | .static (name : Name) .. => name 
  | .definable (name : Name) .. => name

end Dedukti
