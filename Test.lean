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
E.g. the following does not typecheck in Lean:
  noncomputable def letTest : Prop :=
    (fun x =>
    Eq
    (Bool.rec (motive := fun b => Bool.rec (motive := fun _ => Type) Nat Bool b) Nat.zero Bool.true x)
    Bool.true
    ) Bool.true
or in Dedukti:
  def letTest : enc.El (lvl.s lvl.z) (enc.Sort lvl.z).
  [] letTest -->
  (x:(enc.El (lvl.s lvl.z) Bool) =>
    Eq Bool
    Bool_true
    (Bool_rec (lvl.s lvl.z)
      (x0 => Bool_rec (lvl.s (lvl.s lvl.z)) (x1 => enc.Sort (lvl.s lvl.z)) Nat Bool x0) Nat_zero Bool_true x))
  Bool_true.
-/
noncomputable def letTest : Prop :=
  let x := Bool.true
  Eq
  Bool.true
  (Bool.rec (motive := fun b => Bool.rec (motive := fun _ => Type) Nat Bool b) Nat.zero Bool.true x)

noncomputable def letTestBinders : Nat → Bool → Prop :=
  fun n b =>
  let x := Nat.succ (Bool.rec Nat.zero n b)
  let y := (Nat.rec (motive := fun n => Nat.rec (motive := fun _ => Type) Bool (fun _ _ => Nat) n) Bool.true (fun _ _ => Nat.zero) x)
  Eq
  y
  (Nat.rec (motive := fun n => Nat.rec (motive := fun _ => Type) Bool (fun _ _ => Nat) n) Bool.true (fun _ _ => Nat.zero) x)

universe u v

def multiUnivTest (T1 : Sort u) (T2 : Sort v) : Sort v := T2

-- structure PLift (α : Sort u) : Type u where
--   up :: down : α
-- #check PLift.rec
