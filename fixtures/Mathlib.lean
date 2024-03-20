import Lean4Lean.Commands

-- #print ProbabilityTheory.cond_eq_inv_mul_cond_mul
-- set_option pp.all true in
-- #print Classical.em
theorem myEm : ∀ (p : Prop), Or p (Not p) :=
   fun (p : Prop) =>
     let U : Prop → Prop := fun (x : Prop) => Or (@Eq.{1} Prop x True) p;
     let V : Prop → Prop := fun (x : Prop) => Or (@Eq.{1} Prop x False) p;
     @letFun.{0, 0} (@Exists.{1} Prop fun (x : Prop) => U x)
       (fun (exU : @Exists.{1} Prop fun (x : Prop) => U x) => Or p (Not p))
       (@Exists.intro.{1} Prop (fun (x : Prop) => U x) True (@Or.inl (@Eq.{1} Prop True True) p (@rfl.{1} Prop True)))
       fun (exU : @Exists.{1} Prop fun (x : Prop) => U x) =>
       @letFun.{0, 0} (@Exists.{1} Prop fun (x : Prop) => V x)
         (fun (exV : @Exists.{1} Prop fun (x : Prop) => V x) => Or p (Not p))
         (@Exists.intro.{1} Prop (fun (x : Prop) => V x) False
           (@Or.inl (@Eq.{1} Prop False False) p (@rfl.{1} Prop False)))
         fun (exV : @Exists.{1} Prop fun (x : Prop) => V x) =>
         let u : Prop := @Classical.choose.{1} Prop (fun (x : Prop) => U x) exU;
         let v : Prop := @Classical.choose.{1} Prop (fun (x : Prop) => V x) exV;
         @letFun.{0, 0} (U u) (fun (u_def : U u) => Or p (Not p))
           (@Classical.choose_spec.{1} Prop (fun (x : Prop) => U x) exU) fun (u_def : U u) =>
           @letFun.{0, 0} (V v) (fun (v_def : V v) => Or p (Not p))
             (@Classical.choose_spec.{1} Prop (fun (x : Prop) => V x) exV) fun (v_def : V v) =>
             @letFun.{0, 0} (Or (@Ne.{1} Prop u v) p) (fun (not_uv_or_p : Or (@Ne.{1} Prop u v) p) => Or p (Not p))
               (Classical.em.match_1 p u v (fun (u_def : U u) (v_def : V v) => Or (@Ne.{1} Prop u v) p) u_def v_def
                 (fun (h : p) (x : V v) => @Or.inr (@Ne.{1} Prop u v) p h)
                 (fun (x : U u) (h : p) => @Or.inr (@Ne.{1} Prop u v) p h)
                 fun (hut : @Eq.{1} Prop u True) (hvf : @Eq.{1} Prop v False) =>
                 @letFun.{0, 0} (@Ne.{1} Prop u v) (fun (hne : @Ne.{1} Prop u v) => Or (@Ne.{1} Prop u v) p)
                   (@of_eq_true (@Ne.{1} Prop u v)
                     (@Eq.trans.{1} Prop (@Ne.{1} Prop u v) (@Ne.{1} Prop True False) True
                       (@congr.{1, 1} Prop Prop (@Ne.{1} Prop u) (@Ne.{1} Prop True) v False
                         (@congrArg.{1, 1} Prop (Prop → Prop) u True (@Ne.{1} Prop) hut) hvf)
                       (@Eq.trans.{1} Prop (Not (@Eq.{1} Prop True False)) (Not False) True
                         (@congrArg.{1, 1} Prop Prop (@Eq.{1} Prop True False) False Not
                           (@Eq.trans.{1} Prop (@Eq.{1} Prop True False) (Iff True False) False
                             sorry
                             (@Eq.trans.{1} Prop (Iff True False) (Not True) False (iff_false True) not_true_eq_false)))
                         not_false_eq_true)))
                   fun (hne : @Ne.{1} Prop u v) => @Or.inl (@Ne.{1} Prop u v) p hne)
               fun (not_uv_or_p : Or (@Ne.{1} Prop u v) p) =>
               @letFun.{0, 0} (p → @Eq.{1} Prop u v) (fun (p_implies_uv : p → @Eq.{1} Prop u v) => Or p (Not p))
                 (fun (hp : p) =>
                   @letFun.{0, 0} (@Eq.{1} (Prop → Prop) U V) (fun (hpred : @Eq.{1} (Prop → Prop) U V) => @Eq.{1} Prop u v)
                     (@funext.{1, 1} Prop (fun (x : Prop) => Prop) U V fun (x : Prop) =>
                       @letFun.{0, 0} (Or (@Eq.{1} Prop x True) p → Or (@Eq.{1} Prop x False) p)
                         (fun (hl : Or (@Eq.{1} Prop x True) p → Or (@Eq.{1} Prop x False) p) =>
                           @Eq.{1} Prop (Or (@Eq.{1} Prop x True) p) (Or (@Eq.{1} Prop x False) p))
                         (fun (x_1 : Or (@Eq.{1} Prop x True) p) => @Or.inr (@Eq.{1} Prop x False) p hp)
                         fun (hl : Or (@Eq.{1} Prop x True) p → Or (@Eq.{1} Prop x False) p) =>
                         @letFun.{0, 0} (Or (@Eq.{1} Prop x False) p → Or (@Eq.{1} Prop x True) p)
                           (fun (hr : Or (@Eq.{1} Prop x False) p → Or (@Eq.{1} Prop x True) p) =>
                             @Eq.{1} Prop (Or (@Eq.{1} Prop x True) p) (Or (@Eq.{1} Prop x False) p))
                           (fun (x_1 : Or (@Eq.{1} Prop x False) p) => @Or.inr (@Eq.{1} Prop x True) p hp)
                           fun (hr : Or (@Eq.{1} Prop x False) p → Or (@Eq.{1} Prop x True) p) =>
                           @letFun.{0, 0} (@Eq.{1} Prop (Or (@Eq.{1} Prop x True) p) (Or (@Eq.{1} Prop x False) p))
                             (fun (this : @Eq.{1} Prop (Or (@Eq.{1} Prop x True) p) (Or (@Eq.{1} Prop x False) p)) =>
                               @Eq.{1} Prop (Or (@Eq.{1} Prop x True) p) (Or (@Eq.{1} Prop x False) p))
                             (@propext (Or (@Eq.{1} Prop x True) p) (Or (@Eq.{1} Prop x False) p)
                               (@Iff.intro (Or (@Eq.{1} Prop x True) p) (Or (@Eq.{1} Prop x False) p) hl hr))
                             fun (this : @Eq.{1} Prop (Or (@Eq.{1} Prop x True) p) (Or (@Eq.{1} Prop x False) p)) => this)
                     fun (hpred : @Eq.{1} (Prop → Prop) U V) =>
                     @letFun.{0, 0}
                       (∀ (exU : @Exists.{1} Prop fun (x : Prop) => U x) (exV : @Exists.{1} Prop fun (x : Prop) => V x),
                         @Eq.{1} Prop (@Classical.choose.{1} Prop U exU) (@Classical.choose.{1} Prop V exV))
                       (fun
                           (h₀ :
                             ∀ (exU : @Exists.{1} Prop fun (x : Prop) => U x)
                               (exV : @Exists.{1} Prop fun (x : Prop) => V x),
                               @Eq.{1} Prop (@Classical.choose.{1} Prop U exU) (@Classical.choose.{1} Prop V exV)) =>
                         @Eq.{1} Prop u v)
                       (@Eq.mpr.{0}
                         (∀ (exU : @Exists.{1} Prop fun (x : Prop) => U x) (exV : @Exists.{1} Prop fun (x : Prop) => V x),
                           @Eq.{1} Prop (@Classical.choose.{1} Prop U exU) (@Classical.choose.{1} Prop V exV))
                         (∀ (exU exV : @Exists.{1} Prop fun (x : Prop) => V x),
                           @Eq.{1} Prop (@Classical.choose.{1} Prop V exU) (@Classical.choose.{1} Prop V exV))
                         (@id.{0}
                           (@Eq.{1} Prop
                             (∀ (exU : @Exists.{1} Prop fun (x : Prop) => U x)
                               (exV : @Exists.{1} Prop fun (x : Prop) => V x),
                               @Eq.{1} Prop (@Classical.choose.{1} Prop U exU) (@Classical.choose.{1} Prop V exV))
                             (∀ (exU exV : @Exists.{1} Prop fun (x : Prop) => V x),
                               @Eq.{1} Prop (@Classical.choose.{1} Prop V exU) (@Classical.choose.{1} Prop V exV)))
                           (@congrArg.{1, 1} (Prop → Prop) Prop U V
                             (fun (_a : Prop → Prop) =>
                               ∀ (exU : @Exists.{1} Prop fun (x : Prop) => _a x)
                                 (exV : @Exists.{1} Prop fun (x : Prop) => V x),
                                 @Eq.{1} Prop (@Classical.choose.{1} Prop _a exU) (@Classical.choose.{1} Prop V exV))
                             hpred))
                         fun (exU exV : @Exists.{1} Prop fun (x : Prop) => V x) =>
                         @Eq.refl.{1} Prop (@Classical.choose.{1} Prop V exU))
                       fun
                         (h₀ :
                           ∀ (exU : @Exists.{1} Prop fun (x : Prop) => U x) (exV : @Exists.{1} Prop fun (x : Prop) => V x),
                             @Eq.{1} Prop (@Classical.choose.{1} Prop U exU) (@Classical.choose.{1} Prop V exV)) =>
                       @letFun.{0, 0} (@Eq.{1} Prop u v) (fun (this : @Eq.{1} Prop u v) => @Eq.{1} Prop u v) (h₀ exU exV)
                         fun (this : @Eq.{1} Prop u v) => this)
                 fun (p_implies_uv : p → @Eq.{1} Prop u v) =>
                 Classical.em.match_2 p u v (fun (not_uv_or_p : Or (@Ne.{1} Prop u v) p) => Or p (Not p)) not_uv_or_p
                   (fun (hne : @Ne.{1} Prop u v) => @Or.inr p (Not p) (@mt p (@Eq.{1} Prop u v) p_implies_uv hne))
                   fun (h : p) => @Or.inl p (Not p) h

set_option l4l.check true

-- TODO where to introduce this axiom into the environment?
axiom prfIrrel (P : Prop) (p q : P) : p = q

axiom P : Prop
axiom p : P
axiom q : P
axiom p' : P
axiom q' : P

inductive Test : P → Type
| mk : (p : P) → Test p
inductive Test' : P → P → Type
| mk : (p q : P) → Test' p q

-- general form, to replace term t of type T containing proof subterm p at location l that calls `isDefEqProofIrrel p q` returning true
-- @Eq.mpr T[q@l] T (congrArg (fun x => T[x@l]) (prfIrrel P q p)) t

def PITest1 : Test q := Test.mk p
def PITest1' : Test q :=
  @Eq.mpr (Test q) (Test p) (congrArg (fun x => Test x) (prfIrrel P q p)) (Test.mk p)
#check_l4l PITest1'

-- set_option l4l.patch_prfirrel in
-- set_option l4l.prfirrel off in
theorem PITest11 : Test' q q' := Test'.mk p p'

-- set_option l4l.prfirrel off in
def PITest11' : Test' q q' :=
  @Eq.mpr (Test' q q') (Test' p p')
  (congr (f₁ := fun x => Test' q x) (f₂ := fun x => Test' p x)
    (congr (f₁ := fun x => Test' x) (f₂ := fun x => Test' x) rfl (prfIrrel P q p))
    (prfIrrel P q' p'))
  (Test'.mk p p')
#check_l4l PITest11'

-- assert equality of PITest11 and PITest11'

-- set_option l4l.pp_prfirrel on in
-- #print PITest11
-- ^ should delaborate to: [Test'.mk p p' : Test' [p/q (PI)] [p'/q' (PI)]]

def PITest2 : ∀ (_ q : P), Test q := fun p _ => Test.mk p
def PITest2' : ∀ (_ q : P), Test q :=
  fun p q => @Eq.mpr (Test q) (Test p) (congrArg (fun x => Test x) (prfIrrel P q p)) (Test.mk p)







