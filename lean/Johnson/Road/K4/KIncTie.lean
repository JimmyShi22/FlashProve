-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/KIncTie.lean: THE SUM OF THE LOOKUP's END FORM's COEFFICIENTS OVER THE VALUE's NAMES
IS THE SUM OVER THE MASK's SLOTS. One statement: the premise hkI of `d2_four`
(Johnson/Road/K4/Inc4Heard.lean), at the value with its slots and orders laid (`Plan4L.plan`,
Johnson/Road/K4/ValueSlots.lean), its message and n := ns + 1.

  `Plan4L.hkI_of`: ∑ over the value's names j of kInc x j · msg mm j = ∑ over s below ns + 1 of
    kIncAt fo F s · mask s, from two premises: the value's letter kIncS at x is `kIncAt fo F`
    (Johnson/Road/K4/LookLeft.lean), slot by slot; and `MaskLetters`
    (Johnson/Road/K4/MaskTiesH.lean): maskAt mm is the mask up to ns.

HOW. The value's kInc is 0 outside the names of the own mask row: the re-indexing is the step inside
`Plan4.kEnd_eq` (Johnson/Road/K4/ValueSays.lean).

Limits. Both premises stay premises. An equation of sums: nothing on what a mask hides, nothing on
soundness.
-/
import Johnson.Road.K4.MaskTiesH
import Johnson.Road.K4.ValueSays
import Johnson.Road.K4.LookLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.Slice
open Cb Cb.Pv.Lay Cb.Pv.Lay.At Finset
open Inst.Model (Scl)

variable [scl : Scl] {M X : Type} {QL : Plan4L GE M X}

/-- **The premise hkI.** -/
theorem Plan4L.hkI_of (x : X) (mm : M) (mask : ℕ → GE) {n0 nT nI : ℕ}
    (Lm : MaskLetters QL mm mask n0 nT nI) {fo : Forest.Heard} {F : Fork}
    (hS : ∀ s, QL.plan.kIncS x s = kIncAt fo F s) :
    ∑ j, QL.plan.full.kInc x j * QL.plan.full.msg mm j =
      ∑ s : Fin (QL.ns + 1), kIncAt fo F s * mask s := by
  have e : ∑ j : QL.plan.J, QL.plan.kInc x j * QL.plan.msg mm j =
      ∑ s : Fin (QL.plan.ns + 1), QL.plan.kIncS x s * QL.plan.maskAt mm s := by
    simp only [Fintype.sum_sum_type, Plan4.kInc, Plan4.msg, zero_mul, sum_const_zero, zero_add,
      add_zero]
  refine e.trans (Finset.sum_congr rfl fun s _ => ?_)
  rw [hS]
  exact congrArg _ (Lm.isM _ (Nat.lt_succ_iff.mp s.isLt))

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4L.hkI_of
