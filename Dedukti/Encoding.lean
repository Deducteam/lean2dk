import Dedukti.Types
import Dedukti.TransM

namespace Encoding

  def natToExpr : Nat → Dedukti.Expr
    | .zero => .const `nat.z
    | .succ n => (.app (.const `nat.s) (natToExpr n))

  inductive Level
    | z      : Level
    | s      : Level → Level
    | max    : Level → Level → Level
    | imax   : Level → Level → Level
    | var    : Name → Nat → Level
    | inst   : Level → Level
    | aux    : Name → Array Name → Level

  namespace Level
    def natToExpr : Nat → Dedukti.Expr 
    | 0 => .const `nat.z
    | n + 1 => .app (.const `nat.s) (natToExpr n)

    partial def toExpr : Level → Trans.TransM Dedukti.Expr
      | .z          => pure $ .const `lvl.z
      | .s l        => do pure $ .app (.const `lvl.s ) (← toExpr l)
      | .max l1 l2  => do pure $ .appN (.const `lvl.max ) [(← toExpr l1), (← toExpr l2)]
      | .imax l1 l2 => do pure $ .appN (.const `lvl.imax ) [(← toExpr l1), (← toExpr l2)]
      | .var n i => do 
        let var := .var n
        -- let var := .var (((← read).lvlParams.size - n) + (← read).fvars.size - 1)
        if (← read).noLVarNormalize then 
          pure $ .app (.const `normalize.maxS) var
        else
          pure $ .appN (.const `lvl.var) [natToExpr i, var]
      | .inst l    => do pure $ .app (.const `lvl.inst) (← toExpr l)
      | .aux n ls    => do pure $ .appN (.const n) (ls.map (fun p => .var p)).toList
      -- | var n      => .app (.const `lvl.var ) (natToExpr n) -- TODO deep encoding

  end Level

end Encoding
