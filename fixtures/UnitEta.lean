import Init

-- These typecheck only via unit-eta (`u ≡ v` since PUnit/Unit are unit types):
def fixtureUnitEtaP (u v : PUnit) : u = v := rfl
def fixtureUnitEtaU (u v : Unit) : u = v := rfl
