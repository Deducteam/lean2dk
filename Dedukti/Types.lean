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
    deriving Repr, Inhabited
end

namespace Const

  def name : Const → Name
    | .static (name : Name) .. => name 
    | .definable (name : Name) .. => name

end Const

namespace Expr

def piN (params : List Expr) (img : Expr) : Expr :=
  params.foldr (fun dom e => .pi dom e) img

def appN (head : Expr) (params : List Expr) : Expr :=
  params.foldl (fun e arg => .app e arg) head

end Expr

structure Env where
  constMap : Std.RBMap Name Const compare
  deriving Inhabited

end Dedukti
