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

namespace Expr

def piN (params : List Expr) (img : Expr) : Expr :=
  params.foldr (fun dom e => .pi dom e) img

def appN (head : Expr) (params : List Expr) : Expr :=
  params.foldl (fun e arg => .app e arg) head

end Expr

structure Env where
  constMap : Std.RBMap Name Const compare
  deriving Inhabited

def Const.name : Const → Name
  | .static (name : Name) .. => name 
  | .definable (name : Name) .. => name

end Dedukti

namespace Encoding

  def natToExpr : Nat → Dedukti.Expr
    | .zero => .const `nat.z
    | .succ n => (.app (.const `nat.s) (natToExpr n))

  inductive Level
    | z      : Level
    | s      : Level → Level
    | max    : Level → Level → Level
    | imax   : Level → Level → Level
    | var    : Nat → Level

end Encoding
