prelude

inductive True : Prop where
  | intro : True

def test : True → True := λ x : True => x

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

noncomputable def Nat.add (a : Nat) (b : Nat) : Nat :=
  Nat.rec a (fun _ sum => Nat.succ sum) b

inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a
