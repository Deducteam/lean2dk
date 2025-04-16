import Lean
import Lean.Data.RBMap

notation "Name" => Lean.Name

instance : Ord Name where
  compare := Lean.Name.quickCmp

namespace Dedukti

mutual
  inductive Expr
    | var (name : Name) 
    | const (name : Name)
    | fixme (msg : String)
    | app (fn : Expr) (arg : Expr)
    | lam (n : Name) (bod typ : Expr)
    | pi (n : Name) (dom : Expr) (img : Expr)
    | type
    | kind
    deriving Repr, Inhabited, BEq, Hashable

  inductive Rule where
    | mk (vars : List Name) (lhs : Expr) (rhs : Expr)
    deriving Repr, Inhabited

  inductive Const where
    | static (name : Name) (type : Expr) 
    | definable (name : Name) (type : Expr) (rules : List Rule)
    deriving Repr, Inhabited
end

namespace Const

  def name : Const → Name
    | .static (name : Name) .. => name 
    | .definable (name : Name) .. => name

end Const

namespace Expr

def piN (params : List (Name × Expr)) (img : Expr) : Expr :=
  params.foldr (fun (n, dom) e => .pi n dom e) img

def appN (head : Expr) (params : List Expr) : Expr :=
  params.foldl (fun e arg => .app e arg) head

end Expr

structure Env where
  constModMap : Lean.RBMap Name (Lean.RBMap Name Const compare) compare
  deriving Inhabited

end Dedukti
