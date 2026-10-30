-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoPhi.lean.
The weights on the rows of the planes' matrix: the byte-level verifier's own arrays, read.

The law of the reads (`ReadsLaw`, OnBytes/Tie/Pv/Lookup/Port/FoReads.lean) and the columns' sums
(`colsK`, OnBytes/Tie/Pv/Lookup/Forest/FoPlaneRows.lean; `pinColK`,
OnBytes/Tie/Pv/Lookup/Forest/FoPin.lean) are worded with weights on lists over a ring: `phiBK`
(OnBytes/Tie/Pv/Lookup/Forest/FoPlane.lean) and the powers 2 ^ (r % 32). The byte-level verifier has
arrays of its own, `Forest.phiB` and `Forest.phiP` (OnBytes/Model/Look.lean). This file states that
these arrays, read in any commutative ring, are those weights.

Main names:
  `phiB_val`: whatever `Forest.phiB g lm e` returns, read, is `phiBK` at the shape, lm and the point
    `g.zb e` read.
  `phiB_some`: it returns an array if `planeCols` passes lm.
  `phiB_getD`: so, where `planeCols` passes lm, the same of `(Forest.phiB g lm e).getD #[]`, the
    form in which OnBytes/Model/AttentionTables.lean takes the array.
  `phiP_val`: entry r of `Forest.phiP lm`, read, is 2 ^ (r % 32), for r below 2 ^ lm.
  `phiP_size`: the array has 2 ^ lm entries.
Does not say: that the weights of the three tables on the planes' matrix are these arrays (that is
read off OnBytes/Model/Layer.lean, AttentionTables.lean and HeadTables.lean); that `g.zb e`, read,
is the point of the record of end values (`HeardIs` has that as a field); that `ReadsLaw` holds.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Port.FoTwins
import OnBytes.Tie.Pv.Lookup.Forest.FoPlane

set_option autoImplicit false

namespace Fo
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest

section
variable {K : Type} [CommRing K] (ρ : Reading K)

/-- What `Forest.phiB` returns, read. -/
theorem phiB_val (g : Heard) (lm e : ℕ) (a : Array E) (h : phiB g lm e = some a) :
    rdL ρ a = phiBK g.shape lm (rdL ρ (g.zb e)) := by
  unfold phiB at h
  simp only at h
  split at h
  · rw [← Option.some.inj h, eqTab_val, rdL_append, rdL_extract, rdL_extract]
    unfold phiBK
    rw [rdL_length]
  · exact absurd h (by simp)

/-- It returns an array if `planeCols` passes lm. -/
theorem phiB_some (g : Heard) (lm e : ℕ) (h : (planeCols g.shape lm).toBool = true) :
    ∃ a, phiB g lm e = some a := by
  unfold phiB
  simp only
  rw [if_pos h]
  exact ⟨_, rfl⟩

theorem phiB_getD (g : Heard) (lm e : ℕ) (h : (planeCols g.shape lm).toBool = true) :
    rdL ρ ((phiB g lm e).getD #[]) = phiBK g.shape lm (rdL ρ (g.zb e)) := by
  obtain ⟨a, ha⟩ := phiB_some g lm e h
  rw [ha]
  exact phiB_val ρ g lm e a ha

theorem phiP_size (lm : ℕ) : (phiP lm).size = 2 ^ lm := by simp [phiP]

/-- An entry of `Forest.phiP`, read. -/
theorem phiP_val (lm r : ℕ) (hr : r < 2 ^ lm) :
    ρ.val ((phiP lm).getD r zeroE) = (2 : K) ^ (r % 32) := by
  have e : (phiP lm).getD r zeroE = ofF (2 ^ (r % 32)).toUInt64 := by
    unfold phiP
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range]
    simp [hr]
  have h64 : 2 ^ (r % 32) < 2 ^ 64 :=
    Nat.pow_lt_pow_right (by norm_num) (lt_trans (Nat.mod_lt r (by norm_num)) (by norm_num))
  rw [e, ofF_val, toNat_word _ h64, Nat.cast_pow]
  rfl

end
end Fo
