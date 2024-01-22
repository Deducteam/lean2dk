prelude
set_option linter.all false -- prevent runFrontend error messages

universe u v

inductive True : Prop where
  | intro : True

def test : True → True := λ x : True => x

def id {T : Sort u} : T → T := λ x : T => x

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

inductive Unit : Prop where
  | mk : Unit

inductive UnitDep : Nat → Prop where
  | mk : UnitDep Nat.zero

-- generates non-left-linear recursor rule:
-- U.rec.{l} {u : Unit} {motive : U u → Sort l} (mk : motive U.mk) (t : U u) : motive t
-- [l, u, motive, mk] U_rec (normalize.maxS l) u motive mk (U_mk u) --> mk.
inductive U : Unit → Prop where
  | mk : U u

-- generates non-left-linear recursor rule:
-- U.rec.{l} {u : Unit} {motive : U u → Sort l} (mk : motive U.mk) (t : U u) : motive t
-- [l, u, motive, mk] U_rec (normalize.maxS l) u motive mk (U_mk u) --> mk.
inductive UDep : (n : Nat) → UnitDep n → Prop where
  | mk : UDep n u

-- TODO test inductive type family (as opposed to indexed inductive type)
-- inductive U (u : Unit) : Type where
--   | mk : U

inductive Vec : Unit → Type where
  | nil : Vec Unit.mk
  | cons : Vec u → Nat → Vec u

-- #print UDep.rec
-- #print U.rec
-- #print Vec.rec
-- #print Nat.rec

def idtest : Nat := id Nat.zero

noncomputable def Nat.add (a : Nat) (b : Nat) : Nat :=
  Nat.rec a (fun _ sum => Nat.succ sum) b

-- large-eliminating with universe arg
inductive Eq {α : Type u} : α → α → Prop where
  | refl {a : α} : Eq a a

-- TODO large-eliminating with multiple universe args

-- small-eliminating with universe arg
inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p

-- #print Exists.rec

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

structure Point (U V W : Type u) : Type u where
mk :: (x : U) (z : V) (y : W)

def projTest1 : Eq (Point.mk x y z).x x := Eq.refl
def projTest2 : Eq (Point.mk x y z).y z := Eq.refl
def projTest3 : Eq (Point.mk x y z).z y := Eq.refl

def etaTest : Eq p (Point.mk p.x p.z p.y) := Eq.refl

-- def multiUnivTest (T1 : Sort u) (T2 : Sort v) : Sort v := T2

-- structure PLift (α : Sort u) : Type u where
--   up :: down : α
-- #check PLift.rec
