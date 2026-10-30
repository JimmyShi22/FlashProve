-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K06BelowWork.lean: Law/K06Below.lean's CLAUSE WITH THE FACTOR 2 ^ work IN THE COUNT: on a find by reading (B1): the bridge from a rule to a round's error asks errors that bear kitK × ceil × kitF, and kitF = 2 ^ work × w × others
(Johnson/Desc/Sound/RuleKit.lean: ALL settings of the test bits are counted: nothing is gained from work); K06Below's counts are without that factor: at work = 0 the two meet; at work > 0 K06Below's are 2 ^ work too small to bear them: its «for all w ≤ 62» is wider than what can be spent.
This file stands beside K06Below.lean.
WHAT IT DOES NOT SHOW. NO PROBABILITY OF A BAD CHALLENGE IS BOUNDED HERE: what is below 2^-128 is (a number typed beside each of the plan's entries: the price's numerator, at the point lt q^(lt - 1); times 2 ^ work) × (the sampler's fibre bound wOf d) against the number of the round's written verifier messages. That such a
number bounds the bad challenges is the bridge's. It stands over the LIBRARY's written round (_root_.Run.PQ.RD), not over TypedOracleCompiler.Run.PQ.RD: no cast is typed (B2).
  k06BelowWork   at all sizes with 1 ≤ lt ≤ 16 and all work ≤ 57: for every pair (entry, count) of k6Priced lt lPd w and every written round with that entry: RoundBelow (count * 2 ^ w) d 2^-128.
  WHY IT HOLDS: below_of_share asks count × 2^130 ≤ the number of typed values, and leans on work nowhere: there are 61 bits of room.

-/
import Johnson.Desc.Kinds.Law.K06Below

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.Below

open Johnson.Bridge (KindFits roundBelow_zero)
open Johnson.Desc.Ok (fieldBelow unitBelow)
open _root_.Run (PQ.RD)
open OnBytes.Slice (RoundBelow)
open OnBytes.Tie.Pv.Lay (eDraw eBat)
open scoped ENNReal

theorem small_work (c w : ℕ) (hc : c ≤ 8) (hw : w ≤ 57) : c * 2 ^ w ≤ 2 ^ 60 :=
  le_trans (Nat.mul_le_mul hc (Nat.pow_le_pow_right (by norm_num) hw)) (by norm_num)

/-- A sumcheck's pairs, the counts times 2 ^ w. -/
theorem sumBelowWork (b m ends w : ℕ) (hw : w ≤ 57) (p : Fmt.Entry × ℕ)
    (hp : p ∈ sumPriced b m ends w) (d : PQ.RD) (hd : d.entry = p.1) (hk : KindFits false d.kind) :
    RoundBelow (p.2 * 2 ^ w) d ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have hw' : w + 66 ≤ 128 := by omega
  simp only [sumPriced, List.mem_cons, List.mem_append, List.mem_replicate, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | ⟨_, rfl⟩ | rfl | rfl
  · exact oneBelow d _ (le_trans (small_work 1 w (by norm_num) hw) (by norm_num)) (by rw [hd]; simp [eDraw])
      (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; exact hw') hk
  · exact oneBelow d _ (le_trans (small_work 2 w (by norm_num) hw) (by norm_num)) (by rw [hd]; simp [eDraw])
      (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; exact hw') hk
  · exact unitBelow d _ (small_work 2 w (by norm_num) hw) (by rw [hd]; simp) (by rw [hd]) (by rw [hd])
      (by rw [hd]) (by rw [hd]) (by rw [hd]; exact hw') hk
  · rw [Nat.zero_mul]
    exact roundBelow_zero d _

/-- **The clause with the factor 2 ^ work**, as a closed proposition. -/
def K06BelowWork : Prop :=
  ∀ lt lPd w : ℕ, 1 ≤ lt → lt ≤ 16 → w ≤ 57 → ∀ p ∈ k6Priced lt lPd w, ∀ d : PQ.RD,
    d.entry = p.1 → KindFits false d.kind → RoundBelow (p.2 * 2 ^ w) d ((2 : ℝ≥0∞)⁻¹ ^ 128)

theorem k06BelowWork : K06BelowWork := by
  intro lt lPd w h1 h2 hw p hp d hd hk
  have hw' : w + 66 ≤ 128 := by omega
  simp only [k6Priced, List.mem_cons, List.mem_append] at hp
  rcases hp with rfl | rfl | hp | rfl | rfl | hp | hp | hp
  · have hdeg : lt * 2 ^ w ≤ 2 ^ 61 :=
      le_trans (Nat.mul_le_mul h2 (Nat.pow_le_pow_right (by norm_num) hw)) (by norm_num)
    have h := fieldBelow d (lt * 2 ^ w) lt hdeg h1 (le_trans h2 (by norm_num)) (by rw [hd]; simp [eDraw])
      (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; exact hw') hk
    have e : lt * q ^ (lt - 1) * 2 ^ w = lt * 2 ^ w * (Cb.Gl.p ^ 3) ^ (lt - 1) := by
      unfold q
      ring
    show RoundBelow (lt * q ^ (lt - 1) * 2 ^ w) d _
    rw [e]
    exact h
  · exact oneBelow d _ (le_trans (small_work 8 w (by norm_num) hw) (by norm_num)) (by rw [hd]; simp [eBat])
      (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; exact hw') hk
  · exact sumBelowWork _ _ _ w hw p hp d hd hk
  · exact oneBelow d _ (le_trans (small_work 1 w (by norm_num) hw) (by norm_num)) (by rw [hd]; simp [eDraw])
      (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; exact hw') hk
  · exact oneBelow d _ (le_trans (small_work 6 w (by norm_num) hw) (by norm_num)) (by rw [hd]; simp [eBat])
      (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; rfl) (by rw [hd]; exact hw') hk
  · exact sumBelowWork _ _ _ w hw p hp d hd hk
  · exact sumBelowWork _ _ _ w hw p hp d hd hk
  · exact sumBelowWork _ _ _ w hw p hp d hd hk

end VerifiableInference.Desc.Kinds.Head.Law.Below

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Below.k06BelowWork
