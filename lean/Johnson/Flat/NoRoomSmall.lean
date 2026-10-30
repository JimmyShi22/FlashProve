-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/NoRoomSmall.lean: a rule on a count at a shape of written round: at a round that draws
c * 128 matrix entries alone, without work, the count 4 ^ (c * 128) / 2 ^ 128 is a share of at most
2 ^ -128 of the written verifier messages; for c ≥ 1 there is no room: not of at most 2 ^ -129, and
one more bad value is too many. It is meant for the rounds of the smallness test.

The setting. A round of the smallness test draws matrix entries and nothing else: 128 combinations
of c columns, so c * 128 entries, each a pair of bits, without proof of work. Its typed values
number 4 ^ (c * 128). The error of the library's own round of that test is the number of values
that can be drawn divided by 2 ^ tau, tau the number of combinations (`Cb.Pv.Tail.eps`,
Cb/Pv/Tail/Block.lean). `RoundBelow n d εs` (OnBytes/Slice/ManyErr.lean) says that a count n of
bad typed values of the written round d, times the sampler's number w, is at most εs as a share of
the round's written verifier messages.

Main names:
  `EntriesOnly d n`: the written round d draws n matrix entries and nothing else, without work;
    positions, of which it has none, have at most 64 bits.
  `NoRoomSmall`: the closed statement: for every c, at a round with `EntriesOnly d (c * 128)` the
    count 4 ^ (c * 128) / 2 ^ 128 is a share of at most 2 ^ -128.
  `no_room_small`: it holds. It is stated at all c, so no power of a real size is computed.
How it is proved. The sampler's bias is a factor for each drawn element of the extension field
(`below_round_div_ex`, OnBytes/Slice/RatesEx.lean). This round draws none, so the factor is 1, and
there is no work, so nothing is divided: the share of typed values is the share of written messages.
  `le_inv_pow_iff`: a ≤ 2 ^ -k * N, in the extended non-negative reals, if and only if
    a * 2 ^ k ≤ N, in the natural numbers.

The division is that of the natural numbers. For c ≥ 1 it leaves no rest (`count_exact`). At c = 0
the count is 0 (`count_zero`), and the statement says nothing.

There is no room:
  `card_le_w`: the written messages of a round without work are at most w times the typed values.
  `not_below_129`: for c ≥ 1 the same count at the same round is NOT a share of at most 2 ^ -129.
  `not_noRoomSmall_129`: so the statement with 2 ^ -129 is false.
  `not_below_succ`: for c ≥ 1 one more bad typed value is NOT a share of at most 2 ^ -128.
  `not_entriesOnly_elem`: a round that also draws an element of the extension field is not covered;
  `door_elem`: for it the factor is above 1: (the bias) ^ 3 * 2 ^ -128 is not at most 2 ^ -128.
  `toyRound`, `entriesOnly_toy`, `toy_below`, `toy_not_below`: a round with c = 1.

Limits. The statement names no verifier. That the count of bad typed values of a protocol's round is
at most 4 ^ (c * 128) / 2 ^ 128, and that a plan's rounds have `EntriesOnly`, is not said here.

-/
import OnBytes.Slice.ManyErr
import OnBytes.Slice.RatesEx

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace VerifiableInference.Number
open Iop Prob Run OnBytes.Slice

/-- The written round d draws n matrix entries and nothing else, without work. -/
def EntriesOnly (d : PQ.RD) (n : ℕ) : Prop :=
  Fmt.dsOf d.entry d.kind = [.trits n] ∧ d.entry.work = 0 ∧ d.entry.logN ≤ 64

/-- **The rule:** at a written round of that shape that count is a share of at most 2 ^ -128. -/
def NoRoomSmall : Prop :=
  ∀ (c : ℕ) (d : PQ.RD), EntriesOnly d (c * 128) →
    RoundBelow (4 ^ (c * 128) / 2 ^ 128) d ((2 : ℝ≥0∞)⁻¹ ^ 128)

/-! ## Four small lemmas -/

theorem inv_pow_mul_pow (k : ℕ) : ((2 : ℝ≥0∞)⁻¹) ^ k * 2 ^ k = 1 := by
  rw [← mul_pow, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top, one_pow]

/-- A share of 2 ^ -k, in natural numbers. -/
theorem le_inv_pow_iff (a N k : ℕ) :
    (a : ℝ≥0∞) ≤ ((2 : ℝ≥0∞)⁻¹) ^ k * (N : ℝ≥0∞) ↔ a * 2 ^ k ≤ N := by
  constructor
  · intro h
    have h2 : (a : ℝ≥0∞) * 2 ^ k ≤ (N : ℝ≥0∞) :=
      calc (a : ℝ≥0∞) * 2 ^ k ≤ (((2 : ℝ≥0∞)⁻¹) ^ k * (N : ℝ≥0∞)) * 2 ^ k := mul_le_mul' h le_rfl
        _ = (N : ℝ≥0∞) * (((2 : ℝ≥0∞)⁻¹) ^ k * 2 ^ k) := by ring
        _ = (N : ℝ≥0∞) := by rw [inv_pow_mul_pow, mul_one]
    exact_mod_cast h2
  · intro h
    have h2 : (a : ℝ≥0∞) * 2 ^ k ≤ (N : ℝ≥0∞) := by exact_mod_cast h
    calc (a : ℝ≥0∞) = (a : ℝ≥0∞) * (((2 : ℝ≥0∞)⁻¹) ^ k * 2 ^ k) := by
          rw [inv_pow_mul_pow, mul_one]
      _ = ((2 : ℝ≥0∞)⁻¹) ^ k * ((a : ℝ≥0∞) * 2 ^ k) := by ring
      _ ≤ ((2 : ℝ≥0∞)⁻¹) ^ k * (N : ℝ≥0∞) := mul_le_mul' le_rfl h2

/-- The typed values of n matrix entries. -/
theorem card_vals_trits (n : ℕ) : Nat.card (Vals .two [.trits n]) = 4 ^ n := by
  rw [card_vals_all]
  exact Nat.mul_one _

/-- No element of the extension field is drawn: no factor for the sampler's bias. -/
theorem exAll_trits (n : ℕ) : exAll [Fmt.Draw.trits n] = 0 := rfl

/-- At a round that draws n matrix entries alone, without work: a count that is a share of at most
εs of the typed values is a share of at most εs of the written messages. -/
theorem below_of_entriesOnly {d : PQ.RD} {n : ℕ} (hd : EntriesOnly d n) (e : ℕ) (εs : ℝ≥0∞)
    (h : (e : ℝ≥0∞) ≤ εs * ((4 ^ n : ℕ) : ℝ≥0∞)) : RoundBelow e d εs := by
  obtain ⟨hds, hw, hlog⟩ := hd
  have h1 := below_round_div_ex d hlog e εs (by rw [hds, card_vals_trits]; exact h)
  have e0 : εs / 2 ^ d.entry.work = εs := by rw [hw, pow_zero, div_one]
  rw [hds, exAll_trits, pow_zero, one_mul, e0] at h1
  exact h1

/-- **The closed statement holds.** -/
theorem no_room_small : NoRoomSmall := fun _ _ hd =>
  below_of_entriesOnly hd _ _ ((le_inv_pow_iff _ _ 128).2 (Nat.div_mul_le_self _ _))

/-! ## The count -/

/-- For c ≥ 1 the division leaves no rest. -/
theorem count_exact {c : ℕ} (hc : 1 ≤ c) : 4 ^ (c * 128) / 2 ^ 128 * 2 ^ 128 = 4 ^ (c * 128) := by
  have h4 : (4 : ℕ) ^ (c * 128) = 2 ^ (2 * (c * 128)) := by
    rw [pow_mul 2 2 (c * 128)]
    norm_num
  rw [h4]
  exact Nat.div_mul_cancel (pow_dvd_pow 2 (by omega))

/-- At c = 0 the count is 0. -/
theorem count_zero : 4 ^ (0 * 128) / 2 ^ 128 = 0 := by norm_num

/-! ## There is no room -/

/-- The written messages of a round without work are at most w times the typed values: each typed
value has at most w of them. -/
theorem card_le_w (d : PQ.RD) (hlog : d.entry.logN ≤ 64) (hw : d.entry.work = 0) :
    Fintype.card (wRound d).Chal ≤ Nat.card (Vals .two (Fmt.dsOf d.entry d.kind)) * wOf d := by
  have h := cnt_comp_le (bsRound .two d.entry d.kind).φ
    (bsRound_good_ex d.entry d.kind hlog).fib (fun _ => True)
  rw [cnt_true, cnt_true] at h
  rw [card_wRound, hw, pow_zero, Nat.mul_one, Nat.card_eq_fintype_card]
  exact h

theorem card_pos (d : PQ.RD) : 0 < Fintype.card (wRound d).Chal := Fintype.card_pos

/-- At such a round with c ≥ 1 the written messages are at most count * w * 2 ^ 128. -/
theorem card_le_count {c : ℕ} {d : PQ.RD} (hc : 1 ≤ c) (hd : EntriesOnly d (c * 128)) :
    Fintype.card (wRound d).Chal ≤ 4 ^ (c * 128) / 2 ^ 128 * wOf d * 2 ^ 128 := by
  have h := card_le_w d hd.2.2 hd.2.1
  rw [hd.1, card_vals_trits, ← count_exact hc, Nat.mul_right_comm] at h
  exact h

/-- **One bit less room: false.** -/
theorem not_below_129 {c : ℕ} {d : PQ.RD} (hc : 1 ≤ c) (hd : EntriesOnly d (c * 128)) :
    ¬ RoundBelow (4 ^ (c * 128) / 2 ^ 128) d ((2 : ℝ≥0∞)⁻¹ ^ 129) := by
  intro h
  have h1 := (le_inv_pow_iff _ _ 129).1 h
  have h2 := card_le_count hc hd
  have h3 := card_pos d
  generalize 4 ^ (c * 128) / 2 ^ 128 * wOf d = t at h1 h2
  generalize Fintype.card (wRound d).Chal = C at h1 h2 h3
  omega

/-- **One more bad typed value: false.** -/
theorem not_below_succ {c : ℕ} {d : PQ.RD} (hc : 1 ≤ c) (hd : EntriesOnly d (c * 128)) :
    ¬ RoundBelow (4 ^ (c * 128) / 2 ^ 128 + 1) d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  intro h
  have h1 := (le_inv_pow_iff _ _ 128).1 h
  have h2 := card_le_count hc hd
  have h3 := card_pos d
  have hw : 0 < wOf d := by
    rcases Nat.eq_zero_or_pos (wOf d) with h0 | h0
    · rw [h0, Nat.mul_zero, Nat.zero_mul] at h2
      omega
    · exact h0
  rw [Nat.add_mul, Nat.one_mul] at h1
  generalize 4 ^ (c * 128) / 2 ^ 128 * wOf d = t at h1 h2
  generalize Fintype.card (wRound d).Chal = C at h1 h2 h3
  generalize wOf d = w at h1 hw
  omega

/-- A round that also draws an element of the extension field is not covered. -/
theorem not_entriesOnly_elem {d : PQ.RD} {n : ℕ}
    (h : Fmt.dsOf d.entry d.kind = [.elem, .trits n]) (m : ℕ) : ¬ EntriesOnly d m := by
  intro hd
  have e := h.symm.trans hd.1
  cases e

/-- For it the factor of the sampler's bias is above 1. -/
theorem door_elem : ¬ kapSl 128 ^ 3 * (2 : ℝ≥0∞)⁻¹ ^ 128 ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 := by
  intro h
  have h1 : kapSl 128 ^ 3 ≤ 1 :=
    calc kapSl 128 ^ 3 = kapSl 128 ^ 3 * ((2 : ℝ≥0∞)⁻¹ ^ 128 * 2 ^ 128) := by
          rw [inv_pow_mul_pow, mul_one]
      _ = kapSl 128 ^ 3 * (2 : ℝ≥0∞)⁻¹ ^ 128 * 2 ^ 128 := by ring
      _ ≤ (2 : ℝ≥0∞)⁻¹ ^ 128 * 2 ^ 128 := mul_le_mul' h le_rfl
      _ = 1 := inv_pow_mul_pow 128
  have h2 : kapSl 128 ≤ kapSl 128 ^ 3 :=
    calc kapSl 128 = kapSl 128 * 1 * 1 := by rw [mul_one, mul_one]
      _ ≤ kapSl 128 * kapSl 128 * kapSl 128 :=
          mul_le_mul' (mul_le_mul' le_rfl (one_le_kapSl 128)) (one_le_kapSl 128)
      _ = kapSl 128 ^ 3 := by ring
  have h3 : (1 : ℝ≥0∞) < kapSl 128 :=
    ENNReal.lt_add_right ENNReal.one_ne_top
      (ENNReal.inv_ne_zero.2 (ENNReal.pow_ne_top ENNReal.ofNat_ne_top))
  exact absurd (h2.trans h1) (not_le.2 h3)

/-! ## A round with c = 1 -/

/-- A round that draws 128 matrix entries and nothing else. -/
def toyRound : PQ.RD := ⟨{ name := "", trits := 128 }, .entries, [], none, []⟩

theorem entriesOnly_toy : EntriesOnly toyRound (1 * 128) := ⟨rfl, rfl, Nat.zero_le 64⟩

theorem toy_below : RoundBelow (4 ^ (1 * 128) / 2 ^ 128) toyRound ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  no_room_small 1 toyRound entriesOnly_toy

theorem toy_not_below : ¬ RoundBelow (4 ^ (1 * 128) / 2 ^ 128) toyRound ((2 : ℝ≥0∞)⁻¹ ^ 129) :=
  not_below_129 (Nat.le_refl 1) entriesOnly_toy

/-- **The statement with 2 ^ -129 is false.** -/
theorem not_noRoomSmall_129 : ¬ ∀ (c : ℕ) (d : PQ.RD), EntriesOnly d (c * 128) →
    RoundBelow (4 ^ (c * 128) / 2 ^ 128) d ((2 : ℝ≥0∞)⁻¹ ^ 129) :=
  fun h => toy_not_below (h 1 toyRound entriesOnly_toy)

end VerifiableInference.Number

#print axioms VerifiableInference.Number.le_inv_pow_iff
#print axioms VerifiableInference.Number.below_of_entriesOnly
#print axioms VerifiableInference.Number.no_room_small
#print axioms VerifiableInference.Number.count_exact
#print axioms VerifiableInference.Number.count_zero
#print axioms VerifiableInference.Number.card_le_w
#print axioms VerifiableInference.Number.not_below_129
#print axioms VerifiableInference.Number.not_below_succ
#print axioms VerifiableInference.Number.not_entriesOnly_elem
#print axioms VerifiableInference.Number.door_elem
#print axioms VerifiableInference.Number.entriesOnly_toy
#print axioms VerifiableInference.Number.toy_below
#print axioms VerifiableInference.Number.toy_not_below
#print axioms VerifiableInference.Number.not_noRoomSmall_129
