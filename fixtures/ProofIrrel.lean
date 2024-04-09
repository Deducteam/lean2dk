import Lean4Lean.Commands

-- TODO where to introduce this axiom into the environment?
axiom prfIrrel (P : Prop) (p q : P) : p = q
axiom prfIrrelHEq (P Q : Prop) (heq : P = Q) (p : Q) (q : P) : HEq p q

-- general form, to replace term t of type T containing proof subterm p at location l that calls `isDefEqProofIrrel p q` returning true @Eq.mpr T[q@l] T (congrArg (fun x => T[x@l]) (prfIrrel P q p)) t

-- def PITest1 : Test q := Test.mk p
-- def PITest1' : Test q :=
--   @Eq.mpr (Test q) (Test p) (congrArg (fun x => Test x) (prfIrrel P q p)) (Test.mk p)
-- #check_l4l PITest1'
--
-- -- set_option l4l.patch_prfirrel in
-- -- set_option l4l.prfirrel off in
-- theorem PITest11 : Test' q q' := Test'.mk p p'
--
-- -- set_option l4l.prfirrel off in
-- def PITest11' : Test' q q' :=
--   @Eq.mpr (Test' q q') (Test' p p')
--   (congr (f₁ := fun x => Test' q x) (f₂ := fun x => Test' p x)
--     (congr (f₁ := fun x => Test' x) (f₂ := fun x => Test' x) rfl (prfIrrel P q p))
--     (prfIrrel P q' p'))
--   (Test'.mk p p')
-- #check_l4l PITest11'
--
-- -- assert equality of PITest11 and PITest11'
--
-- -- set_option l4l.pp_prfirrel on in
-- -- #print PITest11
-- -- ^ should delaborate to: [Test'.mk p p' : Test' [p/q (PI)] [p'/q' (PI)]]
--
-- def PITest2 : ∀ (_ q : P), Test q := fun p _ => Test.mk p
-- def PITest2' : ∀ (_ q : P), Test q :=
--   fun p q => @Eq.mpr (Test q) (Test p) (congrArg (fun x => Test x) (prfIrrel P q p)) (Test.mk p)
--
theorem congrDepEq {A B : Type u} {U : A → Type v} {V : B → Type v}
  (f : (a : A) → U a) (g : (b : B) → (V b)) (a : A) (b : B)
  (hAB : A = B) (hUV : ∀ a : A, U a = V (Eq.mp hAB a))
  (hAUBV : ((a : A) → U a) = ((b : B) → V b)) (hUaVb : U a = V b)
  (hfg : f = Eq.mpr hAUBV g) (hab : a = Eq.mpr hAB b)
  : f a = Eq.mpr hUaVb (g b) := by
  subst hAB
  have this : U = V := funext hUV
  subst this
  subst hab
  subst hfg
  rfl

theorem lambdaEq {A B : Type u} {U : A → Type v} {V : B → Type v}
  (f : (a : A) → U a) (g : (b : B) → V b)
  (hAB : A = B) (hUV : ∀ a : A, U a = V (Eq.mp hAB a))
  (hAUBV : ((a : A) → U a) = ((b : B) → V b))
  (h : ∀ a : A, f a = Eq.mpr (hUV a) (g (Eq.mp hAB a)))
  : (fun a => f a) = Eq.mpr hAUBV (fun b => g b) := by
  subst hAB
  have this : U = V := funext hUV
  subst this
  exact funext h

theorem forAllEq {A B : Type u} {U : A → Type v} {V : B → Type v}
  (hAB : A = B) (hUV : ∀ a : A, U a = V (Eq.mp hAB a))
  : (∀ a, U a) = (∀ b, V b) := by
  subst hAB
  have this : U = V := funext hUV
  subst this
  rfl

axiom P : Prop
axiom p : P
axiom q : P
axiom r : P
axiom t : P
axiom u : P
axiom r' : P
axiom Q : P → Prop
axiom QTest : (p : P) → (Q p) → Type
axiom Qp : Q p
axiom Qq : Q q

namespace PITest

inductive Test : P → Type
| mk : (p : P) → Test p
inductive Test' : P → P → Type
| mk : (p q : P) → Test' p q
inductive Test'' : P → (P → Type) → Type
| mk : (p : P) → (f : P → Type) → Test'' p f

structure TestStruct where
x : Type

axiom f : Test p → Type
axiom g : Test p → Type → Type
axiom x : f (Test.mk p)
inductive F : Type → Type
| mk : (T : Type) → F T

structure S where
s : P
s' : P

def TestDef : P → Type := fun p => Test p
def TestMkDef : (p : P) → TestDef p := fun p => Test.mk p

-- def fTrue (_ : Test p) : Bool := true
-- inductive fBool : Bool → Type
-- | mk : (b : Bool) → fBool b

-- def PatchTestBoolTrueNested : fBool (fTrue (Test.mk q)) := fBool.mk true
-- #check_l4l PITest.PatchTestBoolTrueNested

axiom depCongr.{u, v}
  {α₁ α₂: Sort u}
  {β₁ : α₁ → Sort v} {β₂ : α₂ → Sort v}
  {f₁ : (a : α₁) → β₁ a} {f₂ : (a : α₂) → β₂ a} 
  {a₁ : α₁} {a₂ : α₂}
  (h₁ : HEq f₁ f₂) (h₂ : HEq a₁ a₂)
  : HEq (f₁ a₁) (f₂ a₂)
axiom congr'.{u, v} {α : Sort u} {β : α → Sort v} {f₁ f₂ : (a : α) → β a} {a₁ a₂ : α} (h₁ : f₁ = f₂) (h₂ : a₁ = a₂) : HEq (f₁ a₁) (f₂ a₂)

theorem PatchTestEtaStruct : S.mk (S.s (S.mk p t)) (S.s' (S.mk r r')) = S.mk q u := rfl
theorem PatchTestEtaStruct' : S.mk (S.s (S.mk p t)) (S.s' (S.mk r r')) = S.mk q u := 
  (congr (f₁ := fun x => S.mk (S.s (S.mk p t)) x) (f₂ := fun x => S.mk q x)
    (congr (f₁ := fun x => S.mk x) (f₂ := fun x => S.mk x) rfl (prfIrrel P p q))
    (prfIrrel P r' u))

-- test for the propositional type having proof-irrelevant parts
theorem PatchTestDepProp (x : QTest q Qq) : QTest p Qp := x
-- theorem PatchTestDepProp : QTest p Qp := 
--   @Eq.mpr (QTest p Qp) (QTest q Qq)
--   (depCongr (f₁ := fun x => QTest p x) (f₂ := fun x => QTest q x)
--     (depCongr (f₁ := fun x => QTest x) (f₂ := fun x => QTest x) HEq.rfl (prfIrrelHEq P P rfl p q))
--     (prfIrrelHEq (Q p) (Q q) sorry Qp Qq))
--   (QTest.mk q Qq)
theorem PatchTestDepProp' (x : QTest q Qq) : QTest p Qp := 
  @Eq.mpr (QTest p Qp) (QTest q Qq)
  (@Eq.ndrec P p (fun q => ∀ (Qq : Q q), QTest p Qp = QTest q Qq) (fun Qq =>
    @Eq.ndrec (Q p) Qp (fun Qq => QTest p Qp = QTest p Qq) rfl Qq (prfIrrel (Q p) Qp Qq)
   ) q (prfIrrel P p q) Qq)
  x
#check_l4l PITest.PatchTestDepProp
#check_l4l PITest.PatchTestDepProp'

#check_l4l PITest.PatchTestEtaStruct
#check_l4l PITest.PatchTestEtaStruct'

theorem PatchTestWhnf : TestDef q := TestMkDef p
#check_l4l PITest.PatchTestWhnf
theorem PatchTestWhnf' : TestDef q :=
  @Eq.mpr (TestDef q) (TestDef p)
  (congr (f₁ := fun x => Test x) (f₂ := fun x => Test x) rfl (prfIrrel P q p))
  (TestMkDef p)
#check_l4l PITest.PatchTestWhnf'

theorem PatchTestNested : F (Test q) := F.mk (Test p)
#check_l4l PITest.PatchTestNested

theorem PatchTestApp : Test' q u := Test'.mk p t
#check_l4l PITest.PatchTestApp

theorem PatchTestApp' : Test' q u :=
  @Eq.mpr (Test' q u) (Test' p t)
  (congr (f₁ := fun x => Test' q x) (f₂ := fun x => Test' p x)
    (congr (f₁ := fun x => Test' x) (f₂ := fun x => Test' x) rfl (prfIrrel P q p))
    (prfIrrel P u t))
  (Test'.mk p t)
#check_l4l PITest.PatchTestApp'

theorem PatchTestLam : Test'' q (fun x => Test' u x) := Test''.mk p (fun y => Test' t y)
#check_l4l PITest.PatchTestLam
-- theorem PatchTestLam' : Test'' q (fun _ => Test' q q') := 
--   @Eq.mpr (Test'' q (fun x => Test' q x)) (Test'' q (fun y => Test' p y))
--   (congr (f₁ := fun x => Test' q x) (f₂ := fun x => Test' p x)
--     (congr (f₁ := fun x => Test' x) (f₂ := fun x => Test' x) rfl (prfIrrel P q p))
--     (prfIrrel P q' p'))
--   (Test''.mk p (fun _ => Test' p p'))

-- test for nested casts within outermost cast
theorem PatchTestLamNested : Test'' q (fun x => f (Test.mk x)) := Test''.mk p (fun y => f (Test.mk y))
#check_l4l PITest.PatchTestLamNested

axiom InferAppArg : f (Test.mk q) -- isDefEq-calling base-case
#check_l4l PITest.InferAppArg
axiom InferAppArg' : F (f (Test.mk q)) -- non-base-case version
#check_l4l PITest.InferAppArg

axiom InferAppFun : (g (Test.mk q)) Sort
#check_l4l PITest.InferAppFun

-- TODO InferAppArg and InferAppFun with a cast on the outermost term (testing that casts preserve casted subterms)

def InferLetVal : Test p := -- isDefEq-calling base-case
  let t : Test p := Test.mk q
  t
#check_l4l PITest.InferLetVal

def InferLetVal' : Type := -- non-base-case version
  let _ : Type := f (Test.mk q)
  Sort
#check_l4l PITest.InferLetVal'

def InferLetType : Type :=
  let _ : f (Test.mk q) := x
  Sort
#check_l4l PITest.InferLetType

def InferLetBod : Type :=
  let _ : Type := Sort
  f (Test.mk q)
#check_l4l PITest.InferLetBod

-- TODO InferLetVal, InferLetType and InferLetBod with a cast on the outermost term (testing that casts preserve casted subterms)

noncomputable def InferLambdaDom : Type := (fun _ : f (Test.mk q) => Sort) x
#check_l4l PITest.InferLambdaDom

-- TODO version of InferLambdaDom above with dependent types

noncomputable def InferLambdaBod : Type := (fun _ : Type => f (Test.mk q)) Sort
#check_l4l PITest.InferLambdaBod

axiom InferForAllDom : f (Test.mk q) → Type
#check_l4l PITest.InferForAllDom

axiom InferForAllBod : Type → f (Test.mk q)
#check_l4l PITest.InferForAllBod

def InferProj : Type := (TestStruct.mk (f (Test.mk q))).1 
#check_l4l PITest.InferProj

end PITest
