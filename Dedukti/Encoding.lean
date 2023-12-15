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
    | var    : Nat → Level

  namespace Level

    def toExpr : Level → Trans.TransM Dedukti.Expr
      | .z          => pure $ .const `lvl.z
      | .s l        => do pure $ .app (.const `lvl.s ) (← toExpr l)
      | .max l1 l2  => do pure $ .appN (.const `lvl.max ) [(← toExpr l1), (← toExpr l2)]
      | .imax l1 l2 => do pure $ .appN (.const `lvl.imax ) [(← toExpr l1), (← toExpr l2)]
      | .var n      => do 
        let var := .var (((← read).lvlParams.size - n) + (← read).fvars.size - 1)
        if (← read).noLVarNormalize then 
          pure $ .app (.const `normalize.maxS ) var
        else
          pure $ .app (.const `normalize.var ) var
      -- | var n      => .app (.const `lvl.var ) (natToExpr n) -- TODO deep encoding

  end Level

end Encoding
