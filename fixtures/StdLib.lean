import Init
universe u
theorem em (p : Prop) : p ∨ ¬p := Classical.em p
set_option pp.all true
-- #print CoeOut.mk
-- #print Quot
-- #print Quot.lift
-- #print funext
-- #reduce semiOutParam (Sort u)
--
-- #print Classical.em
#print Subtype.mk
#print Subtype.val
#print Subtype.property
#print Or.rec

def test1 (s : Subtype P1) : Subtype.mk (Subtype.val s) (Subtype.property s) = s := rfl

def P1 : Bool → Prop
  | .true => True
  | .false => True

def P2 : Bool → Prop
  | .true => True
  | .false => False

def p1 : P1 .true := .intro
def p2 : P2 .true := .intro

#reduce (@Subtype.mk Bool P2 (@Subtype.val Bool P1 (@Subtype.mk Bool P1 Bool.true p1)) (@Subtype.property Bool P1 (@Subtype.mk Bool P1 Bool.true p1)))
#check Subtype.val
#check Subtype.property
