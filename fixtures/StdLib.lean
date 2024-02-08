import Init
universe u
theorem em (p : Prop) : p ∨ ¬p := Classical.em p
set_option pp.all true
-- #print CoeOut.mk
-- #print Quot
-- #print Quot.lift
#print funext
-- #reduce semiOutParam (Sort u)
--
-- #print Classical.em
