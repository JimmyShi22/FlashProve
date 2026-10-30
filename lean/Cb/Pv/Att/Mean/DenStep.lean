-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Att/Mean/DenStep.lean: the test of the denominators of an attention segment at the lookup's
point, as one statement at one point.

The relation of an attention segment (RFraw in Inst/Model/Att/Trace.lean) asks that the identity at3
is 0 at every valid index: the denominator of a row of scores is the sum of the row's softmax
weights. An attention sub-proof tests these identities at the point z that its lookup has drawn, and
draws nothing further for them.

Main names:
  denOut D C z t: what is tested: the sum over the pairs b of wp D C z .w3 b times the read, at the
    points yg and yi, of the array (g, i) ↦ the identity at3 at (b, g, i). wp, yg and yi are cut
    from z (Inst/Model/Att/Points.lean): with u the inner point of the family w3, yg is u from
    coordinate 1 on (lg coordinates), yi is u from coordinate 1 + lg on (lT coordinates), and
    wp D C z .w3 b is the equality weight of the coordinates of the call's point in front of u at
    the number of piece b.
  denVec D t: the same identities as one vector on the cube (b | g | i), 0 where b is no pair.
  DenStep D C z t: if denOut is 0, every identity at3 at a valid index is 0.
  denOut_split: denOut is the batch of the reads of the denominators less the batch of the reads of
    the sums of the softmax weights.

Limits: DenStep is a definition, and no hypothesis of any theorem. It does not hold at every z: for
cells at which some identity is
not 0, denOut is 0 at some points z. How many such points there are is not counted here. Nothing is
said on a verifier or on hiding.


-/
import Inst.Model.Att.KeyForms

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Att

open Finset
open Inst.Model.AttSeg

variable {E : Type} [Field E] (D : Dim) (C : Calls) (z : ℕ → E) (t : Raw → E)

/-- What an attention sub-proof tests of the identities at3, at the lookup's point z. -/
def denOut : E :=
  ∑ b ∈ range D.nb, wp D C z .w3 b *
    rd2 D (yg D C z) (eqT D (yi D C z)) fun g i => idnVal D t (.at3 b g i)

/-- The identities at3 as one vector on the cube (b | g | i); 0 where b is not the number of a
pair. -/
def denVec (X : ℕ) : E :=
  if X / D.T / D.nG < D.nb then idnVal D t (.at3 (X / D.T / D.nG) (X / D.T % D.nG) (X % D.T))
  else 0

/-- The step at the point z: if the test's value is 0, every identity at3 at a valid index is 0. -/
def DenStep : Prop :=
  denOut D C z t = 0 → ∀ b g i, Idn.Valid D (.at3 b g i) → idnVal D t (.at3 b g i) = 0

/-- The test's value is the batch of the reads of the denominators less the batch of the reads of
the sums of the softmax weights. -/
theorem denOut_split :
    denOut D C z t =
      (∑ b ∈ range D.nb, wp D C z .w3 b * rd2 D (yg D C z) (eqT D (yi D C z)) (denV t b)) -
        ∑ b ∈ range D.nb, wp D C z .w3 b * rd2 D (yg D C z) (eqT D (yi D C z)) (EF D t b) := by
  unfold denOut rd2
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [← mul_sub, ← sum_sub_distrib]
  congr 1
  refine sum_congr rfl fun g _ => ?_
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  show _ * (denV t b g i - EF D t b g i) = _
  ring

end Cb.Pv.Att

#print axioms Cb.Pv.Att.denOut_split
