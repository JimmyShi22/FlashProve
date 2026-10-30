-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prices/Pays.lean: when a round of a plan pays for a proved error, in natural numbers.

A soundness lemma of a block bounds a round's error by a count: at most `count` of the `total`
challenges of the round are bad. The planner (OnBytes/Params/Planner.lean) gives every round a
price, `PlanRound.error`, and says yes of a plan only if every price, with the distance from uniform
of the round's draws, is at most 2 ^ (work - target). This file joins the two. `Covers r count
total`: the count is at most the price times the total. `Within target work count total`: count * 2
^ target ≤ 2 ^ work * total, an inequality between natural numbers. A round that holds and covers a
count has the count within the target (`within_of_covers`). `PaysAt P i n d count`: the plan P has
at the place i a round of the name n that draws d elements of the extension field and nothing else,
with work below the target, and that round covers the count among the |E| ^ d challenges and has it
within the target. A price `fieldError s k` covers k |E| ^ (k - 1) of |E| ^ k (`covers_field`).

Main definitions: `Covers`, `Within`, `PaysAt`.
Main theorems: `within_of_covers`, `covers_field`, `cardE_pos_of_good`, `not_within_all`,
`not_paysAt_nil`, `not_covers_free`.
What is not claimed: that a count bounds a prover's chance: that is the matter of the lemma that
counts. That proof of work is worth its bits: here the work is a number in an exponent. Nothing on
the sampler's bias: the planner's addition for the draws is dropped. No sum over rounds.

-/
import OnBytes.Params.HoldsLaws
import OnBytes.Params.PlanListsChains

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params.Prices
open Binary Bound

/-- The round's price covers an error of `count` challenges out of `total`. -/
def Covers (r : PlanRound) (count total : ℕ) : Prop := (count : ℚ) ≤ r.error.val * (total : ℚ)

/-- In natural numbers: count / total is at most 2 ^ (work - target). -/
def Within (target work count total : ℕ) : Prop := count * 2 ^ target ≤ 2 ^ work * total

/-- The plan has at the place i a round of the name n that draws d elements of the extension field
and nothing else; its work is below the target; its price covers `count` of the |E| ^ d challenges;
and the count is within the target, the round's work counted. -/
def PaysAt (P : Planned) (i : ℕ) (n : String) (d count : ℕ) : Prop :=
  ∃ r, P.rounds[i]? = some r ∧ r.entry.name = n ∧
    (r.entry.drawE = d ∧ r.entry.drawNZ = 0 ∧ r.entry.poss = 0 ∧ r.entry.trits = 0) ∧
    r.entry.work < P.set.target ∧ Covers r count (P.set.cardE ^ d) ∧
    Within P.set.target r.entry.work count (P.set.cardE ^ d)

/-- **A round that holds and covers a count has the count within the target.** -/
theorem within_of_covers {s : Setting} {unit : Binary} {r : PlanRound} {count total : ℕ}
    (h : roundHolds s unit r = true) (hc : Covers r count total) :
    Within s.target r.entry.work count total := by
  have h1 := roundHolds_sound h
  have h2 : (count : ℚ) ≤ (2 : ℚ) ^ ((r.entry.work : ℤ) - (s.target : ℤ)) * (total : ℚ) :=
    hc.trans (mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _))
  rw [zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0), zpow_natCast, zpow_natCast] at h2
  have hp : (0 : ℚ) < 2 ^ s.target := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hp] at h2
  unfold Within
  exact_mod_cast h2

/-- A quotient by 0 is marked bad. -/
theorem ratio_zero_bad (k : ℕ) : (Bound.ratio k 0).bad = true := by
  have hz : (Bound.ofNat 0).lo.isZero = true := by first | rfl | decide
  unfold Bound.ratio Bound.div
  rw [hz]
  simp only [Bool.or_true, ↓reduceIte, Bound.failed]

/-- A field error that is not marked bad is over a field with an element. -/
theorem cardE_pos_of_good {s : Setting} {k : ℕ} (hb : (fieldError s k).bad = false) :
    0 < s.cardE := by
  rcases Nat.eq_zero_or_pos s.cardE with h0 | h
  · exfalso
    unfold fieldError at hb
    rw [h0, ratio_zero_bad] at hb
    cases hb
  · exact h

/-- **The price k / |E| covers k |E| ^ (k - 1) of the |E| ^ k points.** -/
theorem covers_field {s : Setting} {r : PlanRound} {k count : ℕ}
    (he : r.error = (fieldError s k).error) (hb : (fieldError s k).bad = false)
    (hc : count ≤ k * s.cardE ^ (k - 1)) : Covers r count (s.cardE ^ k) := by
  have hq : (0 : ℚ) < (s.cardE : ℚ) := by exact_mod_cast cardE_pos_of_good hb
  have h1 : (k : ℚ) / (s.cardE : ℚ) ≤ r.error.val := by
    rw [he]
    exact le_error (encl_fieldError s k) hb
  have h2 : ((k * s.cardE ^ (k - 1) : ℕ) : ℚ) =
      (k : ℚ) / (s.cardE : ℚ) * ((s.cardE ^ k : ℕ) : ℚ) := by
    cases k with
    | zero => simp
    | succ j =>
      rw [Nat.add_sub_cancel]
      push_cast
      rw [pow_succ]
      field_simp
  unfold Covers
  calc (count : ℚ) ≤ ((k * s.cardE ^ (k - 1) : ℕ) : ℚ) := by exact_mod_cast hc
    _ = (k : ℚ) / (s.cardE : ℚ) * ((s.cardE ^ k : ℕ) : ℚ) := h2
    _ ≤ r.error.val * ((s.cardE ^ k : ℕ) : ℚ) :=
        mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)

/-! ## What must not pay -/

/-- The error of a verifier that says yes to all, every challenge, is not within a target above the
work. -/
theorem not_within_all {target work total : ℕ} (hw : work < target) (ht : 0 < total) :
    ¬ Within target work total total := by
  unfold Within
  intro h
  rw [Nat.mul_comm] at h
  have h2 : 2 ^ target ≤ 2 ^ work := Nat.le_of_mul_le_mul_right h ht
  exact absurd ((Nat.pow_le_pow_iff_right (by norm_num)).mp h2) (by omega)

/-- A plan without rounds pays nothing. -/
theorem not_paysAt_nil (s : Setting) (i : ℕ) (n : String) (d count : ℕ) :
    ¬ PaysAt ⟨s, []⟩ i n d count := by
  rintro ⟨r, hr, -⟩
  simp at hr

/-- A round with the price 0 covers no count but 0. -/
theorem not_covers_free {r : PlanRound} (h0 : r.error = {}) {count total : ℕ} (hc : 0 < count) :
    ¬ Covers r count total := by
  unfold Covers
  rw [h0]
  have : (({} : Binary).val) = 0 := by simp [Binary.val]
  rw [this, zero_mul]
  exact not_le.mpr (by exact_mod_cast hc)

end OnBytes.Params.Prices
