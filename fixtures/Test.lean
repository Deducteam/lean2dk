prelude
set_option linter.all false -- prevent runFrontend error messages

universe u v w

inductive True : Prop where
  | intro : True

def test : True → True := λ x : True => x

def id {T : Sort u} : T → T := λ x : T => x

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

inductive Unit : Type where
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
inductive Eq {α : Sort u} : α → α → Prop where
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

structure Point (U : Type u) (V : Type v) (W : Type w) where
mk :: (x : U) (z : V) (y : W)
#print Point.rec
#print Point.mk

noncomputable def letTestBinders (f : Point A B C → Nat) : Point A B C → Bool → Prop :=
  fun n b =>
  let x := Nat.succ (Bool.rec Nat.zero (f n) b)
  let y := (Nat.rec (motive := fun n => Nat.rec (motive := fun _ => Type) Bool (fun _ _ => Nat) n) Bool.true (fun _ _ => Nat.zero) x)
  Eq
  y
  (Nat.rec (motive := fun n => Nat.rec (motive := fun _ => Type) Bool (fun _ _ => Nat) n) Bool.true (fun _ _ => Nat.zero) x)

def projTest1 : Eq (Point.mk x y z).x x := Eq.refl
def projTest2 : Eq (Point.mk x y z).y z := Eq.refl
def projTest3 : Eq (Point.mk x y z).z y := Eq.refl

def etaTest : Eq p (Point.mk p.x p.z p.y) := Eq.refl

-- -- TODO large- or small-eliminating recursor?
-- set_option bootstrap.inductiveCheckResultingUniverse false in
-- inductive PUnit : Sort u where
--   /-- `PUnit.unit : PUnit` is the canonical element of the unit type. -/
--   | unit : PUnit

-- mutual -- FIXME "feature not implemented" Dedukti error
--   inductive Even : Nat → Type where
--     | even_zero : Even Nat.zero
--     | even_succ : (n : Nat) → Odd n → Even (Nat.succ n)
--
--   inductive Odd : Nat → Type where
--     | odd_succ : (n : Nat) → Even n → Odd (Nat.succ n)
-- end

-- -- needed for nested recursors

inductive List (α : Type u) where
  /-- `[]` is the empty list. -/
  | nil : List α
  /-- If `a : α` and `l : List α`, then `cons a l`, or `a :: l`, is the
  list whose first element is `a` and with `l` as the rest of the list. -/
  | cons (head : α) (tail : List α) : List α

-- --

def one : Nat := Nat.succ (Nat.zero)
def two : Nat := Nat.succ (Nat.succ (Nat.zero))

inductive Tree (α : Type u) where
  | mk : α → List (Tree α) → Tree α

noncomputable def treeSum (t : Tree Nat) : Nat :=
  Tree.rec (fun n _ st => .add n st) Nat.zero (fun _ _ sh st => .add sh st) t

theorem treeSumTest : Eq (treeSum (.mk one (.cons (.mk one .nil) .nil))) two := Eq.refl

-- def nestTest : Eq (Tree.rec (fun a _ n => a + n) 0 (fun _ _ n n' => n + n') (Tree.node 1 (TreeList.cons (Tree.node 1 TreeList.nil) TreeList.nil))) 2 :=  Eq.refl _ -- FIXME add metaprogramming so can write like this
-- noncomputable def nestTest' : Nat := (Tree.rec (fun a _ n => Nat.add a n) Nat.zero (fun _ _ n n' => Nat.add n n') (Tree.node (Nat.succ (Nat.zero)) (TreeList.cons (Tree.node (Nat.succ (Nat.zero)) TreeList.nil) TreeList.nil)))
-- def nestTest : Eq (Tree.rec (fun a _ n => Nat.add a n) Nat.zero (fun _ _ n n' => Nat.add n n') (Tree.node (Nat.succ (Nat.zero)) (TreeList.cons (Tree.node (Nat.succ (Nat.zero)) TreeList.nil) TreeList.nil))) (Nat.succ (Nat.succ (Nat.zero))) :=  Eq.refl

-- Tree.rec.{u_1, u} {α : Type u} {motive_1 : (a : Nat) → Tree a → Sort u_1} {motive_2 : (a : Nat) → TreeList a → Sort u_1}
--   (node : {n : Nat} → (a : α) → (a_1 : TreeList n) → motive_2 n a_1 → motive_1 n (Tree.node a a_1))
--   (nil : motive_2 Nat.zero TreeList.nil)
--   (cons :
--     {n m : Nat} →
--       (a : Tree n) → (a_1 : TreeList m) → motive_1 n a → motive_2 m a_1 → motive_2 (Nat.add m n) (TreeList.cons a a_1))
--   {a✝ : Nat} (t : Tree a✝) : motive_1 a✝ t

-- #print Tree.rec

-- def multiUnivTest (T1 : Sort u) (T2 : Sort v) : Sort v := T2

-- structure PLift (α : Sort u) : Type u where
--   up :: down : α
-- #check PLift.rec
inductive Rec (T : Type w) where
| nil : Rec T
| cons : T → Rec T → Rec T

axiom P : Prop

structure S : Type where
p : P
def structEtaTest (s t : S) : Eq t (S.mk s.p) := Eq.refl

def unitTest (u v : Unit) : Eq u v := Eq.refl
def structRedTest (s : S) : Eq (S.rec (fun _ => Nat.zero) s) Nat.zero := Eq.refl
def f : Sort ((max u v) + 1) := Sort (max u v)

init_quot

def quotLiftTest : Eq (Quot.lift (fun _ => Nat.zero) (fun a b h => Eq.refl) (Quot.mk (fun _ _ => True) (Nat.succ Nat.zero))) Nat.zero := Eq.refl
def quotIndTest : Eq (Quot.ind (β := fun q => True) (fun a => trivial) (Quot.mk (fun _ _ => True) (Nat.succ Nat.zero))) trivial := Eq.refl
