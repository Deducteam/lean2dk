import Lean4Lean.Commands

-- TODO where to introduce this axiom into the environment?
axiom prfIrrel (P : Prop) (p q : P) : p = q

-- general form, to replace term t of type T containing proof subterm p at location l that calls `isDefEqProofIrrel p q` returning true
-- @Eq.mpr T[q@l] T (congrArg (fun x => T[x@l]) (prfIrrel P q p)) t

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

namespace PITest
axiom P : Prop
axiom p : P
axiom q : P
axiom p' : P
axiom q' : P

inductive Test : P → Type
| mk : (p : P) → Test p
inductive Test' : P → P → Type
| mk : (p q : P) → Test' p q

structure TestStruct where
x : Type

axiom f : Test p → Type
axiom g : Test p → Type → Type
axiom F : Type → Type
axiom x : f (Test.mk p)

axiom InferAppArg : f (Test.mk q) -- isDefEq-calling base-case
#check_l4l PITest.InferAppArg
axiom InferAppArg' : F (f (Test.mk q)) -- non-base-case version
#check_l4l PITest.InferAppArg

axiom InferAppFun : (g (Test.mk q)) Sort
#check_l4l PITest.InferAppFun

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

noncomputable def InferLambdaDom : Type := (fun _ : f (Test.mk q) => Sort) x
#check_l4l PITest.InferLambdaDom

noncomputable def InferLambdaBod : Type := (fun _ : Type => f (Test.mk q)) Sort
#check_l4l PITest.InferLambdaBod

axiom InferForAllDom : f (Test.mk q) → Type
#check_l4l PITest.InferForAllDom

axiom InferForAllBod : Type → f (Test.mk q)
#check_l4l PITest.InferForAllBod

def InferProj : Type := (TestStruct.mk (f (Test.mk q))).1 
#check_l4l PITest.InferProj

end PITest
