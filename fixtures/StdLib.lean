import Init
universe u
theorem em (p : Prop) : p ∨ ¬p := Classical.em p
set_option pp.all true

open Classical

axiom myRefl {α : Type} (a b : α) : Eq a b

theorem myEm (p : Prop) : p ∨ ¬p :=
  let U (x : Prop) : Prop := x = True ∨ p
  let V (x : Prop) : Prop := x = False ∨ p
  have exU : ∃ x, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x, V x := ⟨False, Or.inl rfl⟩
  let u : Prop := choose exU
  let v : Prop := choose exV
  have u_def : U u := choose_spec exU
  have v_def : V v := choose_spec exV
  have not_uv_or_p : u ≠ v ∨ p :=
    match u_def, v_def with
    | Or.inr h, _ => Or.inr h
    | _, Or.inr h => Or.inr h
    | Or.inl hut, Or.inl hvf =>
      have hne : u ≠ v := by simp [hvf, hut, true_ne_false]
      Or.inl hne
  have p_implies_uv : p → u = v :=
    fun hp =>
    have hpred : U = V :=
      funext fun x =>
        have hl : (x = True ∨ p) → (x = False ∨ p) :=
          fun _ => Or.inr hp
        have hr : (x = False ∨ p) → (x = True ∨ p) :=
          fun _ => Or.inr hp
        show (x = True ∨ p) = (x = False ∨ p) from
          propext (Iff.intro hl hr)
    have h₀ : ∀ exU exV, @choose _ U exU = @choose _ V exV := by
      rw [hpred]; intros; exact myRefl _ _
    show u = v from h₀ _ _
  match not_uv_or_p with
  | Or.inl hne => Or.inr (mt p_implies_uv hne)
  | Or.inr h   => Or.inl h
-- #print CoeOut.mk
-- #print Quot
-- #print Quot.lift
-- #print funext
-- #reduce semiOutParam (Sort u)
--
-- #print Classical.em
-- #print myEm
-- #print Classical.em
#print Subtype.val
#print Subtype.property

def test1 (s : Subtype P1) : Subtype.mk (Subtype.val s) (Subtype.property s) = s := rfl

noncomputable instance (priority := low) myPropDecidable (a : Prop) : Decidable a :=
  choice <| match myEm a with
    | Or.inl h => ⟨isTrue h⟩
    | Or.inr h => ⟨isFalse h⟩

def P1 : Bool → Prop
  | .true => True
  | .false => True

def P2 : Bool → Prop
  | .true => True
  | .false => False

def p1 : P1 .true := .intro
def p2 : P2 .true := .intro

#reduce (@Subtype.mk Bool P2 (@Subtype.val Bool P1 (@Subtype.mk Bool P1 Bool.true p1)) (@Subtype.property Bool P1 (@Subtype.mk Bool P1 Bool.true p1)))
#check Subtype.val
#check Subtype.property
