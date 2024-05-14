import Lean4Lean.Commands

-- TODO where to introduce this axiom into the environment?
axiom prfIrrel (P : Prop) (p q : P) : p = q
axiom prfIrrelHEq (P Q : Prop) (heq : P = Q) (p : Q) (q : P) : HEq p q

#print Eq.refl
#print Eq.symm
#print Eq.trans
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

theorem appHEq {A B : Type u} {U : A → Type v} {V : B → Type v}
  (f : (a : A) → U a) (g : (b : B) → (V b)) (a : A) (b : B)
  (hAB : A = B) (hUV : HEq U V) (hAUBV : ((a : A) → U a) = ((b : B) → V b))
  (hfg : HEq f g) (hab : HEq a b)
  : HEq (f a) (g b) := by
  subst hAB
  subst hUV
  subst hab
  subst hfg
  rfl

/--
  I.e., `funextHEq`.
-/
theorem lambdaHEq {A B : Type u} {U : A → Type v} {V : B → Type v}
  (f : (a : A) → U a) (g : (b : B) → V b)
  (hAB : A = B) (hUV : HEq U V)
  (h : (a : A) → (b : B) → HEq a b → HEq (f a) (g b))
  : HEq (fun a => f a) (fun b => g b) := by
  subst hAB
  subst hUV
  have : f = g := funext fun a => eq_of_heq $ h a a HEq.rfl
  exact heq_of_eq this

theorem forAllHEq {A B : Type u} {U : A → Type v} {V : B → Type v}
  (hAB : A = B) (hUV : HEq U V)
  : ((a : A) → U a) = ((b : B) → V b) := by
  subst hAB
  subst hUV
  rfl

theorem castHEq {A B : Type u} (a : A) (hAB : A = B)
  : HEq (cast hAB a) a := by
  subst hAB
  rfl

-- verison of eq_of_heq that does not rely on proof-irrelevance
theorem eq_of_heq' {α : Sort u} {a a' : α} (h : HEq a a') : Eq a a' :=
  have : (α β : Sort u) → (a : α) → (b : β) → HEq a b → (h : Eq α β) → Eq (cast h a) b :=
    fun _ _ _ _ h₁ =>
      h₁.rec (fun h => prfIrrel _ rfl h ▸ rfl)
  this α α a a' h rfl

def cast' (A B : Sort u) (h : HEq A B) (a : A) : B := cast (eq_of_heq' h) a

-- theorem KHEqAux {T : Sort u} {a b : T} (h : K a b a b) : K.mk a b = h := prfIrrel _ _ _
-- theorem KHEq {T : Sort u} {a b : T} (hab : a = b) :
--   (h : Eq a b) → HEq (@Eq.rec _ a (fun _ _ => Type) Prop b h) Prop := hab ▸ fun h => HEq.rfl

-- theorem KHEq {T : Sort u} {a b : T}
--   (motive : (u v : T) → K a b u v → Type v) (m : motive a b (K.mk a b))
--   (h : K a b a b) : Eq (K.rec (motive := motive) m h) m := rfl

-- theorem EqHEq {T : Sort u} {a b : T} (hab : a = b)
--   {motive : (u : T) → Eq a u → Type v} (m : motive a (Eq.refl a)) :
--   (h : Eq a b) → HEq (@Eq.rec _ a motive m b h) m :=
--   hab ▸ fun h => prfIrrel _ (Eq.refl a) h ▸ HEq.rfl

inductive K : α → α → α → α → Prop where
  | mk (a b : α) : K a b a b

theorem KRedKLike {T : Sort u} {a b c d : T} (hac : a = c) (hbd : b = d)
  {motive : (u v : T) → K a b u v → Type v} (m : motive a b (K.mk a b)) :
  (h : K a b c d) → HEq (@K.rec _ a b motive m c d h) m :=
  hac ▸ hbd ▸ fun h => prfIrrel _ (K.mk a b) h ▸ HEq.rfl
#check_l4l KRedKLike

-- structure S (a b : α) : Type where
-- x : Nat
-- y : Nat

inductive S (a b : α) : Type where
| mk : Nat → Nat → S a b

noncomputable def S.x (s : S a b) : Nat := s.rec fun x _ => x
noncomputable def S.y (s : S a b) : Nat := s.rec fun _ y => y

theorem SEtaAux {T : Sort u} {a b : T} (s : S a b) : s = S.mk s.x s.y := s.rec (motive := fun s => s = S.mk s.x s.y) fun _ _ => rfl
#check_l4l SEtaAux

theorem SRedEta {T : Sort u} {a b : T}
  {motive : S a b → Type v} (m : (x y : Nat) → motive (S.mk x y)) (s : S a b) :
  HEq (@S.rec _ a b motive m s) (m s.x s.y) := Eq.rec (motive := fun s _ => HEq (@S.rec _ a b motive m s) (m s.x s.y)) (HEq.refl _) (SEtaAux s).symm
#check_l4l SRedEta

-- theorem ex
--   (a b c : Nat) (hab : a = b) :
--   (h : a = b) → (@Eq.rec _ a (fun _ _ => Nat) c b h) = c :=
--   hab ▸ fun _ => rfl
--
-- theorem ex' (a b c : Nat) (hab : a = b) : (h : a = b) → (@Eq.rec _ a (fun _ _ => Nat) c b h) = c :=
--      @Eq.rec Nat a (fun x h => ∀ (h : @Eq Nat a x), @Eq Nat (@Eq.rec Nat a (fun x x => Nat) c x h) c)
--        (fun x => @rfl Nat (@Eq.rec Nat a (fun x x => Nat) c a (Eq.refl a))) b hab
--
-- set_option pp.explicit true in
-- #print ex

-- #print KHEq

-- theorem ex (a b : Nat) (h : K a b a b)
--   : K.rec (motive := fun _ _ _ => Type) Nat h := cast (eq_of_heq' (KHEq (motive := fun _ _ _ => Type) rfl rfl Nat h)).symm a

axiom P : Prop
axiom p : P
axiom q : P
axiom r : P
axiom s : P
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

def PatchTestKLike {A : Type} (a : A) (h : K (Q p) (Q q) (Q r) (Q s)) : @K.rec _ (Q p) (Q q) (fun _ _ _ => Type) A (Q r) (Q s) h := a

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
