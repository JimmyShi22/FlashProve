-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookBatch.lean.
A lookup's claims, each under its own power of the batching element, as one batched form of a
ledger with exponents.

The lookup's side has its claims as a list of affine forms on the caller's entries with one entry
more (Fo.AffK (Option J) K), and their share of the one equation as Fo.powSum x n0 of their values.
The ledger's side has claims with exponents (ℕ × TWhole.Form K J) and the one form
OnBytes.Road.Rows.batchAt x. This file lays the first as the second.

Main names:
  `lookLed n0 forms`: form number i of the list, as the claim that it is 0, under the exponent
    n0 + i.
  `lookLed_gap`: (batchAt x (lookLed n0 forms)).gap m is powSum x n0 of the forms' values at
    zext m.
  `lookLed_exps`: the exponents are n0, n0 + 1, .., one for each form.
  `lookLed_nodup`, `lookLed_lt`: so no exponent stands twice, and each is at least n0 and below
    n0 + forms.length.
Needs: OnBytes/Tie/Pv/Led/LedJoint.lean (batchAt, batchAt_gap).
Does not say: which forms a lookup's claims are; that the entries' places are the ledger's.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoClaimsForm
import OnBytes.Tie.Pv.Led.LedJoint

set_option autoImplicit false

namespace Fo
open TWhole OnBytes.Road.Rows Cb.Fo

section
variable {K J : Type} [Field K] [DecidableEq J]

/-- The forms as claims with exponents. -/
def lookLed (n0 : ℕ) (forms : List (AffK (Option J) K)) : List (ℕ × Form K J) :=
  (forms.zipIdx n0).map fun p => (p.2, ⟨coOf p.1, -p.1.2⟩)

theorem lookLed_gap [Fintype J] (x : K) (n0 : ℕ) (forms : List (AffK (Option J) K)) (m : J → K) :
    (batchAt x (lookLed n0 forms)).gap m =
      powSum x n0 (forms.map fun f => AffK.val f (zext m)) := by
  rw [batchAt_gap, look_batch]
  unfold lookLed
  rw [List.map_map]
  refine congrArg List.sum (List.map_congr_left fun p _ => ?_)
  show x ^ p.2 * (∑ j, coOf p.1 j * m j - -p.1.2) = _
  rw [val_zext_co, sub_neg_eq_add]

theorem lookLed_exps (n0 : ℕ) (forms : List (AffK (Option J) K)) :
    (lookLed n0 forms).map Prod.fst = List.range' n0 forms.length := by
  unfold lookLed
  rw [List.map_map]
  show (forms.zipIdx n0).map Prod.snd = _
  exact List.zipIdx_map_snd n0 forms

theorem lookLed_nodup (n0 : ℕ) (forms : List (AffK (Option J) K)) :
    ((lookLed n0 forms).map Prod.fst).Nodup := by
  rw [lookLed_exps]
  exact List.nodup_range' (step := 1) (by decide)

theorem lookLed_lt (n0 : ℕ) (forms : List (AffK (Option J) K)) (e : ℕ)
    (he : e ∈ (lookLed n0 forms).map Prod.fst) : n0 ≤ e ∧ e < n0 + forms.length := by
  rw [lookLed_exps, List.mem_range'_1] at he
  exact he

end
end Fo
