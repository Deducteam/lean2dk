prelude

inductive True : Prop where
  | intro : True

def test : True → True := λ x : True => x

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

noncomputable def Nat.add (a : Nat) (b : Nat) : Nat :=
  Nat.rec a (fun _ sum => Nat.succ sum) b

inductive Eq {α : Type} : α → α → Prop where
  | refl {a : α} : Eq a a

theorem addZero (n : Nat) : Eq (Nat.add n Nat.zero) n := Eq.refl
theorem zeroAdd (n : Nat) : Eq (Nat.add Nat.zero n) n := 
  Nat.rec Eq.refl (fun n' ih => @Eq.rec _ (Nat.add Nat.zero n') (fun a _ => Eq (Nat.succ (Nat.add Nat.zero n')) (Nat.succ a)) Eq.refl n' ih) n

inductive Bool : Type where
  | false : Bool
  | true : Bool

/--
Let expression test case; note that you cannot just replace a let expression with a beta-redex,
E.g. the following does not typecheck:
noncomputable def letTest : Prop :=
  (fun x =>
  Eq
  (Bool.rec (motive := fun b => Bool.rec (motive := fun _ => Type) Nat Bool b) Nat.zero Bool.true x)
  Bool.true) Bool.true
-/
noncomputable def letTest : Prop :=
  let x := Bool.true
  Eq
  (Bool.rec (motive := fun b => Bool.rec (motive := fun _ => Type) Nat Bool b) Nat.zero Bool.true x)
  Bool.true
