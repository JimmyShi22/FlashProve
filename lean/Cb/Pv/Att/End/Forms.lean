-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/Forms.lean: affine forms on early and late entries, and the claim on an end value of a
plain sumcheck as such a form.

Definitions, statements and proofs. A sub-proof's verifier ties each end value of a sumcheck to
entries of a message that is sent late: the end value's hidden value less a public combination of
late entries is 0. Cb/Sub/Late.lean pulls such a claim back to the early entries, along the forms
that say what each late entry is meant to be. This file has the small algebra of forms that is
needed to write the claims, and the one statement that all ends use.

Main names:
  aConst, aAdd, aSub, aSmul, aSum, aEnt: forms, with their values (val_aConst and so on).
  late a m: the early entries m with the forms' values as late entries.
  liftF f, liftA a: a form on the early entries as a form on early and late entries; liftF_pull,
    val_liftA.
  endF T o a r: the claim on end value a of the output statement o: what was shown, less the last
    coordinate times the mask entry, less the form r, is 0.
  endF_pull: if r, read at late a m, is worth the map a at o's point, the pull-back of endF holds
    of m exactly if the block's output claim on a holds (EHolds).

Limits: nothing on an honest prover or on hiding. That a claim written here is a claim that the
programs add is not said here.


-/
import Cb.Pv.Att.Plain
import Cb.Sub.Late

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open TWhole Cb Cb.Sub Finset

variable {E J : Type} [Field E]

/-! ### Forms -/

/-- A constant. -/
def aConst (c : E) : Aff E J := ⟨fun _ => 0, c⟩
/-- A sum of two forms. -/
def aAdd (a b : Aff E J) : Aff E J := ⟨fun j => a.co j + b.co j, a.c0 + b.c0⟩
/-- A difference of two forms. -/
def aSub (a b : Aff E J) : Aff E J := ⟨fun j => a.co j - b.co j, a.c0 - b.c0⟩
/-- A multiple of a form. -/
def aSmul (c : E) (a : Aff E J) : Aff E J := ⟨fun j => c * a.co j, c * a.c0⟩
/-- A sum of forms over a finite set. -/
def aSum {ι : Type} (s : Finset ι) (f : ι → Aff E J) : Aff E J :=
  ⟨fun j => ∑ i ∈ s, (f i).co j, ∑ i ∈ s, (f i).c0⟩
/-- One entry. -/
def aEnt [DecidableEq J] (j : J) : Aff E J := ⟨fun i => if i = j then 1 else 0, 0⟩

section Val
variable [Fintype J] (m : J → E)

theorem val_aConst (c : E) : (aConst c : Aff E J).val m = c := by
  simp [aConst, Aff.val]

theorem val_aAdd (a b : Aff E J) : (aAdd a b).val m = a.val m + b.val m := by
  simp only [aAdd, Aff.val, add_mul, sum_add_distrib]
  ring

theorem val_aSub (a b : Aff E J) : (aSub a b).val m = a.val m - b.val m := by
  simp only [aSub, Aff.val, sub_mul, sum_sub_distrib]
  ring

theorem val_aSmul (c : E) (a : Aff E J) : (aSmul c a).val m = c * a.val m := by
  simp only [aSmul, Aff.val, mul_add, mul_sum, mul_assoc]

theorem val_aSum {ι : Type} (s : Finset ι) (f : ι → Aff E J) :
    (aSum s f).val m = ∑ i ∈ s, (f i).val m := by
  simp only [aSum, Aff.val, sum_mul, sum_add_distrib]
  rw [sum_comm]

theorem val_aEnt [DecidableEq J] (j : J) : (aEnt j : Aff E J).val m = m j := by
  simp [aEnt, Aff.val]

end Val

/-! ### Early and late entries -/

section Late
variable {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂]

/-- The early entries m, with the forms' values as late entries. -/
def late (a : J₂ → Aff E J₁) (m : J₁ → E) : J₁ ⊕ J₂ → E := Sum.elim m fun i => (a i).val m

/-- A form on the early entries, as a form on early and late entries. -/
def liftF (f : Form E J₁) : Form E (J₁ ⊕ J₂) := ⟨Sum.elim f.co fun _ => 0, f.tg⟩

/-- The pull-back of a lifted form says what the form says. -/
theorem liftF_pull (a : J₂ → Aff E J₁) (f : Form E J₁) (m : J₁ → E) :
    (pullF a (liftF f)).Holds m ↔ f.Holds m := by
  rw [pullF_holds]
  unfold Form.Holds Form.gap liftF
  rw [Fintype.sum_sum_type]
  simp

/-- An affine form on the early entries, as a form on early and late entries. -/
def liftA (a : Aff E J₁) : Aff E (J₁ ⊕ J₂) := ⟨Sum.elim a.co fun _ => 0, a.c0⟩

theorem val_liftA (al : J₂ → Aff E J₁) (a : Aff E J₁) (m : J₁ → E) :
    (liftA (J₂ := J₂) a).val (late al m) = a.val m := by
  unfold liftA Aff.val late
  rw [Fintype.sum_sum_type]
  simp

/-- The pull-back of the claim that a form is 0. -/
theorem claim_pull (a : J₂ → Aff E J₁) (r : Aff E (J₁ ⊕ J₂)) (m : J₁ → E) :
    (pullF a r.claim).Holds m ↔ r.val (late a m) = 0 := by
  rw [pullF_holds, Aff.claim_holds]
  rfl

end Late

/-! ### The claim on an end value -/

section End
variable [Fintype E] (T : PlainSc E) {J₂ : Type} [Fintype J₂] [DecidableEq T.J] [DecidableEq J₂]

/-- The point of the challenges of an output statement. -/
noncomputable def pointAt (o : T.our.par.Out) : Fin T.nv → E :=
  ldPartFn T.nv T.deg T.dat (T.our.ini o.st (T.our.par.hp o.st o.pt))

/-- The claim on end value a: what was shown, less the last coordinate times the mask entry, less
the form r, is 0. -/
noncomputable def endF (o : T.our.par.Out) (a : T.A) (r : Aff E (T.J ⊕ J₂)) : Form E (T.J ⊕ J₂) :=
  (aSub (aSub (aConst (o.vals a))
    (aSmul (T.our.lst o.st (T.our.par.hp o.st o.pt)) (aEnt (.inl (T.cAt a))))) r).claim

/-- If r is worth the map a at o's point, the pull-back of the claim is the block's output claim. -/
theorem endF_pull (al : J₂ → Aff E T.J) (o : T.our.par.Out) (a : T.A) (r : Aff E (T.J ⊕ J₂))
    (m : T.J → E) (hr : r.val (late al m) = T.map o.st m a (pointAt T o)) :
    (pullF al (endF T o a r)).Holds m ↔ T.our.par.EHolds o m a := by
  unfold endF
  rw [claim_pull, val_aSub, val_aSub, val_aConst, val_aSmul, val_aEnt, hr,
    psc_our_val E T.our o m a]
  show o.vals a - T.our.lst o.st (T.our.par.hp o.st o.pt) * m (T.cAt a) -
      T.map o.st m a (pointAt T o) = 0 ↔
    T.map o.st m a (pointAt T o) + m (T.cAt a) * T.our.lst o.st (T.our.par.hp o.st o.pt) =
      o.vals a
  constructor
  · intro h
    linear_combination -h
  · intro h
    linear_combination -h

end End

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.liftF_pull
#print axioms Cb.Pv.Att.End.endF_pull
