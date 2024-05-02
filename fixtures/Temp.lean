import Lean4Lean.Commands
set_option autoImplicit false

axiom P : Type
axiom p : P
axiom q : P
axiom hpq : p = q

axiom T : P → Type
axiom hTpq : T p = T q -- (provable from hpq)
axiom hTpq0 : (T p → Type) = (T q → Type) -- (provable from hpq)
axiom tp : T p
axiom tq : T q
axiom htpq : tp = Eq.mpr hTpq tq

universe u v

theorem test {A : Type u} {U V : A → Type v}
  (hAUBV : ((a : A) → U a) = ((a : A) → V a))
  : U = V := by
  sorry

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

-- example : ∀ {A B : Type u} {U : A → Type v} {V : B → Type v} (f : (a : A) → U a) (g : (b : B) → V b)
--      (a : A) (b : B) (hAB : A = B),
--      U = Eq.mpr (congrArg (· → Type v) hAB) V →
--        ∀ (hAUBV : ((a : A) → U a) = ((b : B) → V b)) (hUaVb : U a = V b),
--          f = Eq.mpr hAUBV g → a = Eq.mpr hAB b → f a = Eq.mpr hUaVb (g b) :=
--    fun {A B} {U} {V} f g a b hAB hUV hAUBV hUaVb hfg hab =>
--      Eq.rec (motive := fun {B} hAB =>
--        ∀ {V : B → Type v} (g : (b : B) → V b) (b : B),
--          U = Eq.mpr (congrArg (fun x => x → Type v) hAB) V →
--            ∀ (hAUBV : ((a : A) → U a) = ((b : B) → V b)) (hUaVb : U a = V b),
--              f = Eq.mpr hAUBV g → a = Eq.mpr hAB b → f a = Eq.mpr hUaVb (g b))
--        (fun {V} g b hUV hAUBV hUaVb hfg hab =>
--          Eq.ndrec (motive := fun {V} =>
--            ∀ (g : (b : A) → V b) (hAUBV : ((a : A) → U a) = ((b : A) → V b)) (hUaVb : U a = V b),
--              f = Eq.mpr hAUBV g → f a = Eq.mpr hUaVb (g b))
--            (fun g hAUBV hUaVb hfg =>
--              Eq.ndrec (motive := fun b => ∀ (hUaVb : U a = U b), f a = Eq.mpr hUaVb (g b))
--                (fun hUaVb => hfg ▸ Eq.refl (f a)) hab hUaVb)
--            hUV g hAUBV hUaVb hfg)
--        hAB g b hUV hAUBV hUaVb hfg hab
-- #print congrDepEq
--
-- theorem congrDepEq {A B : Type u} {U : A → Type v} {V : B → Type v} (f : (a : A) → U a) (g : (b : B) → (V b)) (a : A) (b : B)
--   (hAB : A = B) (hUV : U = Eq.mpr (congrArg (· → Type v) hAB) V) (hAUBV : ((a : A) → U a) = ((b : B) → V b)) (hUaVb : U a = V b)
--   (hfg : f = Eq.mpr hAUBV g) (hab : a = Eq.mpr hAB b) : f a = Eq.mpr hUaVb (g b) := by
--   subst hAB
--   subst hUV
--   subst hab
--   subst hfg
--   rfl

axiom X : (p : P) → (T p) → Type

theorem congrDep
  {A : Type u} {T : A → Type v}
  (f g : (a : A) → T a) (x y : A)
  (hfg : f = g) (hxy : x = y) (hT : T x = T y) : f x = Eq.mpr hT (g y) := by
  subst hxy
  subst hfg
  rfl

theorem ex (x : X p tp) : X q tq :=
  @Eq.mp (X p tp) (X q tq)
  (congrDepEq (X p) (X q) tp tq hTpq (fun _ => rfl) hTpq0 rfl
  (congrDepEq X X p q rfl (fun _ => rfl) rfl hTpq0 rfl hpq)
  htpq)
  x
#check_l4l ex

#print Eq.ndrec
set_option pp.all true
#print Eq.trans
#print Eq.mp
