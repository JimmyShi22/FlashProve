-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/SamplePointSmall.lean: the round in which the point of a committed table's out-of-domain sample
is drawn has an error of at most 2^-128, AS A SHARE OF ALL POINTS, at the full size.

Why. OnBytes/Flat/EntryRecord.lean shows that every table has a collision at no more than `recER`
points (`entryFull_record`), and bounds the chance of a collision for a point MADE FROM HASH BLOCKS
(`fr_bound`: the samplers' bias to a power, times `recER` over the number of points). The count
`recER` itself is compared with nothing there. In an interactive oracle proof the verifier draws
the point uniformly; what that round needs is `recER` against the number of points. It follows,
since the bias is at least 1.

  `recER_le_of_recBound`: general in the sizes: a bound on `recBound` bounds `recER` as a share.
  `samplePoint_small`: at the full size, at the configuration's own set of points, for every claim
    and every rest of the configuration.

Limits. A comparison of two numbers; `recER` is still not evaluated. Nothing on the compiled
verifier, whose point is no uniform one: there `fr_bound` itself is what counts.
-/
import OnBytes.Flat.EntryRecord

set_option autoImplicit false

namespace OnBytes.Slice
open Prob Cb Cb.Ood Hiop _root_.Iop _root_.Run Rom
open scoped ENNReal

/-- A bound on the chance of a collision at a point made from hash blocks bounds the number of points
with a collision, as a share of all points. -/
theorem recER_le_of_recBound (T : Fmt.M1.Code) (eM lg s : ℕ) {c : ℝ≥0∞}
    (h : recBound T eM lg s ≤ c) :
    ((recER T eM lg s : ℕ) : ℝ≥0∞) ≤ c * (Fintype.card (recZ T.l lg s).D : ℝ≥0∞) := by
  unfold recBound at h
  unfold recER
  exact (ENNReal.div_le_iff (card_ne_zero' _) (card_ne_top' _)).1
    (le_trans (le_mul_of_one_le_left (_root_.zero_le _) (one_le_pow₀ (one_le_kapSl 128))) h)

end OnBytes.Slice

namespace OnBytes.Flat
open Prob Cb Hiop _root_.Iop _root_.Run OnBytes.Slice OnBytes.Join1
open scoped ENNReal

/-- **The round of a sample's point, at the full size: at most 2^-128 of all points give a
collision**, whatever the table (with `entryFull_record`). -/
theorem samplePoint_small {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
    (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) :
    ((recER recT Params.recordRadius recLg recS : ℕ) : ℝ≥0∞) ≤
      ((2 : ℝ≥0∞)⁻¹) ^ 128 * (Fintype.card (DecR.configurationOfStoredTable A R).Seed : ℝ≥0∞) :=
  recER_le_of_recBound recT Params.recordRadius recLg recS fr_bound

end OnBytes.Flat

#print axioms OnBytes.Slice.recER_le_of_recBound
#print axioms OnBytes.Flat.samplePoint_small
