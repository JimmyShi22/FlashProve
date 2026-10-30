-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/CsOut.lean: the library's new form and new target of a code switch, written out.

The library's code switch (Cb/Ld/LdSwitchWords.lean) combines its rows into one: a sum over the
names of the rows, each row under its coefficient. At the sizes of two neighbouring stages
(OnBytes/Slice/CsData.lean) the coefficient of a row is the power of one element θ whose exponent is
the row's number in the order of batching. This file writes the two sums out by the kinds of rows:
the carried claim, θ times the sample's row, and for draw number i the rows of the three folded
rows' symbols under the powers 2 + 3 i, 3 + 3 i and 4 + 3 i of θ.

Main theorems: `form_out` (the new form, at each coordinate of a new message), `tgt_out` (the new
target).
Not claimed. Nothing on a protocol. Nothing on what the format's own functions compute.
-/
import OnBytes.Slice.CsData

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood Run

variable {s s' : Sg}

/-- A sum over the names of the rows, sorted by kinds. It holds for every way in which the names
are listed. -/
private theorem sum_rows (t : ℕ) [inst : Fintype (LdRow Unit t (Unit ⊕ Unit ⊕ Unit))]
    (F : LdRow Unit t (Unit ⊕ Unit ⊕ Unit) → GE) :
    ∑ ν, F ν = F (.inl ()) + F (.inr (.inl ())) + ∑ i : Fin t, (F (.inr (.inr (i, .inl ())))
      + F (.inr (.inr (i, .inr (.inl ())))) + F (.inr (.inr (i, .inr (.inr ()))))) := by
  obtain rfl : inst = instFintypeSum Unit (Unit ⊕ Fin t × (Unit ⊕ Unit ⊕ Unit)) :=
    Subsingleton.elim _ _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_unique,
    Fintype.sum_unique, add_assoc]
  refine congrArg (_ + ·) (congrArg (_ + ·) (Finset.sum_congr rfl fun i _ => ?_))
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_unique, Fintype.sum_unique,
    Fintype.sum_unique, add_assoc]

/-- The new form: the old form, the sample's row under θ, the three rows of draw number i under
the powers 2 + 3 i, 3 + 3 i, 4 + 3 i. -/
theorem form_out (hf : CsFit s s') (f : CsK s → GE) (ρo : (csSw hf).Zo.D) (Qs : Fin s.t → s.Ps)
    (θ : GE) (n : CsK s ⊕ CsFree hf) :
    (csSw hf).W.form' f ρo (Qs, θ) n
      = ldPad f n + θ * (csSample hf).mat ρo () n + ∑ i : Fin s.t, θ ^ (2 + 3 * i.val) *
          (ldPad (s.cMid.row (Qs i) (.inl ())) n + θ * ldPad (s.cMid.row (Qs i) (.inr (.inl ()))) n
            + θ ^ 2 * ldPad (s.cMid.row (Qs i) (.inr (.inr ()))) n) := by
  refine (@sum_rows s.t _ fun ν =>
    θ ^ (csRowNo s ν).val * (csSw hf).W.rows f ρo Qs ν n).trans ?_
  show θ ^ 0 * ldPad f n + θ ^ 1 * (csSample hf).mat ρo () n + ∑ i : Fin s.t,
    (θ ^ (2 + 3 * i.val) * ldPad (s.cMid.row (Qs i) (.inl ())) n
      + θ ^ (2 + 3 * i.val + 1) * ldPad (s.cMid.row (Qs i) (.inr (.inl ()))) n
      + θ ^ (2 + 3 * i.val + 2) * ldPad (s.cMid.row (Qs i) (.inr (.inr ()))) n) = _
  rw [pow_zero, one_mul, pow_one]
  refine congrArg (_ + ·) (Finset.sum_congr rfl fun i _ => ?_)
  ring

/-- The new target, likewise. -/
theorem tgt_out (hf : CsFit s s') (τ : GE) (ans : Unit → GE) (y : s.Ps → s.cMid.Aa → GE)
    (Qs : Fin s.t → s.Ps) (θ : GE) :
    (csSw hf).W.tgt' τ ans y (Qs, θ)
      = τ + θ * ans () + ∑ i : Fin s.t, θ ^ (2 + 3 * i.val) *
          (y (Qs i) (.inl ()) + θ * y (Qs i) (.inr (.inl ()))
            + θ ^ 2 * y (Qs i) (.inr (.inr ()))) := by
  refine (@sum_rows s.t _ fun ν =>
    θ ^ (csRowNo s ν).val * (csSw hf).W.vals τ ans y Qs ν).trans ?_
  show θ ^ 0 * τ + θ ^ 1 * ans () + ∑ i : Fin s.t,
    (θ ^ (2 + 3 * i.val) * y (Qs i) (.inl ())
      + θ ^ (2 + 3 * i.val + 1) * y (Qs i) (.inr (.inl ()))
      + θ ^ (2 + 3 * i.val + 2) * y (Qs i) (.inr (.inr ()))) = _
  rw [pow_zero, one_mul, pow_one]
  refine congrArg (_ + ·) (Finset.sum_congr rfl fun i _ => ?_)
  ring

end OnBytes.Slice

#print axioms OnBytes.Slice.form_out
#print axioms OnBytes.Slice.tgt_out
