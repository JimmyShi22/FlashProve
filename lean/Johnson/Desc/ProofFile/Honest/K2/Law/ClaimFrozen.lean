-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/ClaimFrozen.lean: the kind "the code switch" (K2): THE CLAIM AT
WHAT A FOLD LEFT, KEPT IN ARRAYS (`frozenLeft`, Honest/K2/Closing.lean), IS THE CLAIM AT WHAT THE
FOLD LEFT: at the sizes' own two codes and kept shapes, where the main code's message length is a
power of two. An honest prover's closing hands on what `foldEnd` leaves in that kept form.
Statements with their proofs.

  `frozen_main` with `frozen_mask`, `frozen_kept`: within the arrays' sizes the kept form has the
                    entries of what it was made of: the main row and a kept member's real rows below
                    the code's message length; the two mask rows below the mask code's
  `claimTrue_frozen` THE TOP: 2 ^ (the main code's length's logarithm) = that length ⊢ `ClaimTrue Z
                    old (frozenLeft ‹Z's main code› ‹Z's mask code› Z.kept W)` ↔ `ClaimTrue Z old W`

By: `claimTrue_congr_in` (Johnson/Desc/K2/Honest/Carry/ReadsIn.lean) · the definitions. NEAR, NOT
CALLED: the library's `range_map_at`, `zipIdx_map_at` (Johnson/Road/FormsKeysDictA.lean) and
`getD_range_map` (Johnson/Road/FormsKeysTab.lean): an array of a function's values read within: the
three small laws here go by the same one step in place; these files stand in another part of the
library, over which this file does not stand.

Limits. Neither claim is had here. THE PREMISE IS PUBLIC AND A PREMISE: the program's
`Codes.lengthsOk` (OnBytes/Iop/Ground.lean) asks it of every code; nothing here ties it to that
test. THE CODES AND THE KEPT SHAPES ARE THE SIZES' OWN: a closing freezes at its segment's codes,
code numbers and kept shapes: that these are the sizes' at which the claim is asked is not proved
here. Beyond the arrays' sizes the kept form is 0: nothing is said there. Nothing on tails. Nothing
on any property.
-/
import Johnson.Desc.K2.Honest.Carry.ReadsIn
import Johnson.Desc.ProofFile.Honest.K2.Closing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open OnBytes
open OnBytes.Slice (GE readE formAt)
open VerifiableInference.Desc.K2.Honest (Left Sizes zeroG ClaimTrue claimTrue_congr_in Held)

/-- The main row, below the code's message length. -/
theorem frozen_main (c z : Code) (kept : List OracleShape) (W : Left) (j : Nat) (hj : j < c.ell) :
    (frozenLeft c z kept W).main j = W.main j := by
  unfold frozenLeft
  simp [Array.getD, hj]

/-- The two mask rows, below the mask code's message length. -/
theorem frozen_mask (c z : Code) (kept : List OracleShape) (W : Left) (r i : Nat) (hr : r < 2)
    (hi : i < z.ell) : (frozenLeft c z kept W).mask r i = W.mask r i := by
  unfold frozenLeft
  simp [Array.getD, hr, hi]

/-- A kept member's rows, at its real rows, below the code's message length. -/
theorem frozen_kept (c z : Code) (kept : List OracleShape) (W : Left) (a b j : Nat)
    (ha : a < kept.length) (hb : b < (kept.getD a {}).mainRows) (hj : j < c.ell) :
    ((frozenLeft c z kept W).kept a).main b j = (W.kept a).main b j := by
  rw [List.getD_eq_getElem _ _ ha] at hb
  unfold frozenLeft
  simp [Array.getD, ha, hb, hj]

/-- **THE CLAIM AT WHAT IS KEPT IN ARRAYS IS THE CLAIM AT WHAT THE FOLD LEFT**: at the sizes' own
two codes and kept shapes, where the main code's length is a power of two. -/
theorem claimTrue_frozen (Z : Sizes) (old : SingleRows) (W : Left)
    (hp : 2 ^ (Z.codes.base.getD Z.code default).logEll = (Z.codes.base.getD Z.code default).ell) :
    ClaimTrue Z old (frozenLeft (Z.codes.base.getD Z.code default)
      (Z.codes.mask.getD Z.maskCode default) Z.kept W) ↔ ClaimTrue Z old W := by
  refine claimTrue_congr_in Z old _ _ (fun j hj => frozen_main _ _ _ _ j hj) (fun a i hi => ?_)
    (fun r i hr hi => frozen_mask _ _ _ _ r i hr hi)
  unfold Held.entryIn
  split
  · rename_i hb
    have ha : a < Z.kept.length := by
      by_contra h
      rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h)] at hb
      exact Nat.not_lt_zero _ hb
    have hj : i / 2 ^ ceilLog2 (Z.kept.getD a {}).mainRows <
        (Z.codes.base.getD Z.code default).ell := by
      rw [← hp]
      exact Nat.div_lt_of_lt_mul (by rwa [← pow_add])
    unfold Held.entry
    exact frozen_kept _ _ _ _ a _ _ ha hb hj
  · rfl

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.frozen_main
#print axioms ProofFile.Honest.K2.frozen_mask
#print axioms ProofFile.Honest.K2.frozen_kept
#print axioms ProofFile.Honest.K2.claimTrue_frozen
