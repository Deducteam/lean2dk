prelude

inductive True : Prop where
  | intro : True

def test : True → True := λ x : True => x
