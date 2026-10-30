-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/End/Hid.lean: the hidden values of the named scalars of an attention sub-proof, as values
and as forms; the three linear claims on the further scalars at their meant value.

Definitions, statements and proofs. The named scalars of the key forms (KSc in
Inst/Model/Att/KeyForms.lean) are sent as further scalars of the first three sumchecks of the chain
of Cb/Pv/Att/OwnSteps.lean. This file says where each stands, gives its hidden value (what was sent
less its mask entry), and states the three linear claims that Cb/Pv/Att/OwnSteps.lean leaves free.

Main names:
  hv l kk m j: the hidden value of scalar number j of a list l of sent scalars with the mask entries
    at the places kk; 0 from the list's end on. hvF: the same as a form. val_hvF.
  hidV P x rE m: the hidden value of each named scalar. x holds the further scalars of the two units
    of the scores; rE are those of the denominator times the output.
  hidA P u: the same as forms, at a run u; val_hidA.
  JoinLay P: the lookup's letters in the join: the public letters and the form of the hidden value
    at the end of the key side, both from the first statement.
  LMat P, LDat P, LEat P: the three linear claims. LMat and LDat: the hidden value of each scalar
    that one claim ties to a table is its rule value. LEat: the same, and the join on the hidden
    values.

Limits: which scalar is which follows a reading of the verifier on bytes; no theorem ties the two.
The places are meant for two plane messages (npl = 2).


-/
import Cb.Pv.Att.End.Riders
import Cb.Pv.Att.End.Join
import Cb.Pv.Att.OwnLast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att.End
open TWhole Cb Cb.Sub Finset Blocks
open Inst.Model Inst.Model.AttSeg

variable {E : Type} [Field E]

/-- The hidden value of scalar number j of a list of sent scalars. -/
def hv {J : Type} {n : ℕ} (l : List E) (kk : Fin n → J) (m : J → E) (j : ℕ) : E :=
  if h : j < n then l.getD j 0 - m (kk ⟨j, h⟩) else 0

/-- The same as a form on early and late entries. -/
def hvF {J₁ J₂ : Type} [DecidableEq J₁] [DecidableEq J₂] {n : ℕ} (l : List E) (kk : Fin n → J₁)
    (j : ℕ) : Aff E (J₁ ⊕ J₂) :=
  if h : j < n then hidF (l.getD j 0) (kk ⟨j, h⟩) else aConst 0

theorem val_hvF {J₁ J₂ : Type} [Fintype J₁] [Fintype J₂] [DecidableEq J₁] [DecidableEq J₂] {n : ℕ}
    (al : J₂ → Aff E J₁) (l : List E) (kk : Fin n → J₁) (m : J₁ → E) (j : ℕ) :
    (hvF (J₂ := J₂) l kk j).val (late al m) = hv l kk m j := by
  unfold hvF hv
  split
  · exact val_hidF m al _ _
  · exact val_aConst _ _

/-- The hidden value of a scalar that stands in the list. -/
theorem hv_ofFn {J : Type} {n : ℕ} (r : Fin n → E) (kk : Fin n → J) (m : J → E) (j : Fin n) :
    hv (List.ofFn r) kk m j.val = r j - m (kk j) := by
  have hl : j.val < (List.ofFn r).length := by
    rw [List.length_ofFn]
    exact j.isLt
  unfold hv
  rw [dif_pos j.isLt, List.getD_eq_getElem _ _ hl, List.getElem_ofFn]

/-- Which of the three lists of further scalars holds a named scalar, and at which place. -/
def placeK (D : Dim) : KSc → ℕ × ℕ
  | .cell .m1 jj => (0, jj)
  | .cell .d1 jj => (0, 3 + jj)
  | .cell .m2 jj => (0, 6 + jj)
  | .ms .M => (0, 11)
  | .ss .M => (0, 12)
  | .cell .d2 jj => (1, jj)
  | .ms .D => (1, 5)
  | .ss .D => (1, 6)
  | .acc => (2, 0)
  | .zo => (2, 1)
  | .zc => (2, 2)
  | .rh => (2, 3)
  | .rh' => (2, 4)
  | .ib k => (2, 5 + k)
  | .rg => (2, 5 + D.lT)
  | .rg' => (2, 5 + D.lT + 1)
  | .cell _ _ => (2, 5 + D.lT + 2)

/-- The first, the second or the third of three. -/
def pick3 {α : Type} (i : ℕ) (a b c : α) : α :=
  match i with
  | 0 => a
  | 1 => b
  | _ => c

theorem pick3_map {α β : Type} (f : α → β) (i : ℕ) (a b c : α) :
    f (pick3 i a b c) = pick3 i (f a) (f b) (f c) := by
  unfold pick3
  split <;> rfl

section Own
variable [Fintype E] {M X : Type} (P : OwnPar E M X)

/-- The hidden value of each named scalar. lM, lD, lE: the three lists of sent scalars. -/
def hid3 (lM lD lE : List E) (m : P.J → E) (k : KSc) : E :=
  pick3 (placeK P.D k).1 (hv lM P.kM m (placeK P.D k).2) (hv lD P.kD m (placeK P.D k).2)
    (hv lE P.kE m (placeK P.D k).2)

/-- The hidden value of each named scalar, at a statement x that holds the further scalars of the
two units of the scores, and the further scalars rE. -/
def hidV (x : Seen E X) (rE : Fin (5 + P.D.lT + 2) → E) (m : M) : KSc → E :=
  hid3 P (x.2.getD 0 []) (x.2.getD 1 []) (List.ofFn rE) (P.msg m)

/-- The same as forms, at a run. -/
def hidA {J₂ : Type} [DecidableEq J₂] (u : P.Run) (k : KSc) : Aff E (P.J ⊕ J₂) :=
  pick3 (placeK P.D k).1 (hvF (List.ofFn u.rM) P.kM (placeK P.D k).2)
    (hvF (List.ofFn u.rD) P.kD (placeK P.D k).2) (hvF (List.ofFn u.rE) P.kE (placeK P.D k).2)

theorem val_hidA {J₂ : Type} [Fintype J₂] [DecidableEq J₂] (al : J₂ → Aff E P.J) (u : P.Run)
    (m : M) (k : KSc) :
    (hidA P (J₂ := J₂) u k).val (late al (P.msg m)) = hidV P u.y0 u.rE m k := by
  unfold hidA
  rw [pick3_map fun a : Aff E (P.J ⊕ J₂) => a.val (late al (P.msg m))]
  simp only [val_hvF]
  rfl

/-- The lookup's letters in the join. -/
structure JoinLay where
  /-- the table of scales at which the key forms are formed -/
  scl : Scl
  /-- the public letters, from the first statement -/
  q : X → JoinPub E
  /-- the hidden value at the end of the lookup's key side, as a form on the early entries -/
  ce : X → Aff E P.J

/-- The linear claim on the further scalars of the unit below the diagonal. -/
def LMat (x : Seen E X) (r : Fin (3 * P.npl + 7) → E) (m : M) : Prop :=
  RuleAt P.D P.C nameM r P.kM (P.pub0 x) (P.tOf m) (P.msg m)

/-- The linear claim on the further scalars of the unit on the diagonal. -/
def LDat (x : Seen E X) (r : Fin 7 → E) (m : M) : Prop :=
  RuleAt P.D P.C nameD r P.kD (P.pub0 x) (P.tOf m) (P.msg m)

/-- The linear claim on the further scalars of the denominator times the output: the rule values,
and the join on the hidden values. -/
def LEat (Q : JoinLay P) (x : Seen E X) (r : Fin (5 + P.D.lT + 2) → E) (m : M) : Prop :=
  RuleAt P.D P.C (nameE P.D) r P.kE (P.pub0 x) (P.tOf m) (P.msg m) ∧
    joinVal (Q.q x.1) (KF (scl := Q.scl) P.D P.C (P.pub0 x) (hidV P x r m))
      ((Q.ce x.1).val (P.msg m)) = 0

end Own

end Cb.Pv.Att.End

#print axioms Cb.Pv.Att.End.val_hvF
#print axioms Cb.Pv.Att.End.val_hidA
