-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prices/Record.lean: at the typed full-size sizes of the setting "record with work", the
three rounds of a proof's shared chain in which the test on the table itself draws (LIN point, LOC,
LIN zeta) pay for counts of the proof library's form, in natural numbers.

`AtRecord x` (Johnson/Prices/Dear.lean) fixes the table and the stages. Asked besides: 7 low
variables, 64 requests, 22 row bits. For every list of codes and every plan P that `sharedPlan
recordSet codes x` returns (`k14_shared_at_record`), with q for the number of elements of the
format's extension field, n = 2 ^ 32, k = 446693374 and the library's typed radius e =
`recordRadius` = 2852142980:
 - place 0, LIN point, 18 drawn elements, no work: (64 * 18 + c) q ^ 17 of the q ^ 18 points are
   within the target 128, for every whole number c that is at most 11 B + 11 L, B being
   `Cb.bchksBound n k e` and L `Cb.listMax n (n - k) e`;
 - place 3, LOC, 64 positions below 2 ^ 32, 28 bits of work: g ^ 64 of the (2 ^ 32) ^ 64 lists, for
   every g that is at most n - e - 1 = 1442824315;
 - place 6, LIN zeta, 22 drawn elements, no work: 22 q ^ 21 of the q ^ 22 points. One radius serves
   LIN point and LOC: at these lines the lower and the upper radius of a later test's distance are
   the same number (the library's `rl_later`, `record_radius_le`, `rl_facts`, which are evaluations
   in Lean's kernel at the written numbers).

Main theorems: `recorded_of_atRecord`, `k14_shared_at_record`.
What is not claimed: what the heads of Johnson/Prices/Dear.lean, Johnson/Prices/Lin.lean and
Johnson/Prices/Zeta.lean do not claim: above all that some x meets the conditions and has a plan,
and that the counts bound a prover's chance. Nothing on the two sendings between these rounds.

-/
import Johnson.Prices.Lin
import Johnson.Prices.Dear
import OnBytes.Params.EntryCoveredRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params.Prices

/-- The typed sizes meet the conditions of the laws on LIN point and LOC. -/
theorem recorded_of_atRecord {x : LinSized} (hx : AtRecord x) : Recorded recordSet x :=
  ⟨hx.oneTime, by rw [hx.table]; decide, rr_set.1⟩

/-- The setting of the typed lines has the format's field, the target 128 and 28 bits of work for a
batch's rounds of positions. -/
theorem recordSet_numbers : recordSet.cardE = cardGl ∧ recordSet.target = 128 ∧
    recordSet.workOf .query .shared = 28 ∧ recordSet.workOf .closeness .shared = 0 ∧
    recordSet.workOf .field .shared = 0 := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **The three drawing rounds of the test on the table, on a shared chain at the typed sizes.** -/
theorem k14_shared_at_record {codes : Codes} {x : LinSized} {P : Planned} (hx : AtRecord x)
    (hk : x.shape.kLo = 7) (hN : x.lines.requests = 64) (hr : x.shape.kRow = 22)
    (h : sharedPlan recordSet codes x = .ok P) {c g : ℕ}
    (hc : (c : ℝ) ≤ 11 * Cb.bchksBound (2 ^ 32) 446693374 recordRadius +
      (Cb.listMax (2 ^ 32) (2 ^ 32 - 446693374) recordRadius : ℝ) * 11)
    (hg : g ≤ 2 ^ 32 - recordRadius - 1) :
    PaysAt P 0 "LIN point" 18 ((64 * 18 + c) * cardGl ^ 17) ∧
      (∃ r, P.rounds[3]? = some r ∧ r.entry.name = "LOC" ∧
        (r.entry.poss = 64 ∧ r.entry.logN = 32 ∧ r.entry.drawE = 0 ∧ r.entry.drawNZ = 0 ∧
          r.entry.trits = 0) ∧ r.entry.work < 128 ∧
        Covers r (g ^ 64) ((2 ^ 32) ^ 64) ∧ Within 128 r.entry.work (g ^ 64) ((2 ^ 32) ^ 64)) ∧
      PaysAt P 6 "LIN zeta" 22 (22 * cardGl ^ 21) := by
  have hR := recorded_of_atRecord hx
  obtain ⟨m0, g0, -, -, -⟩ := rl_facts
  have hw : wordOf x.table.code = ⟨32, 446693374⟩ := by rw [hx.table]; exact rr_word
  have hn : (wordOf x.table.code).n = 2 ^ 32 := by rw [hw]; rfl
  have hkk : (wordOf x.table.code).k = 446693374 := by rw [hw]
  have hv : x.table.v = 11 := by rw [hx.table]; rfl
  have hlog : x.table.code.logN = 32 := by rw [hx.table]; rfl
  refine ⟨?_, ?_, ?_⟩
  · have hp := point_pays recordSet codes x P h hR (by rw [hx.table]; exact g0)
      (by rw [hkk]; decide) (by rw [hv, hk]; decide) recordRadius c
      (by
        rw [hx.table, m0]
        exact record_radius_le)
      (by
        rw [hn, hkk, hv]
        push_cast
        exact hc)
    rw [hv, hk, hN] at hp
    exact hp
  · have hl := loc_pays recordSet codes x P h hR
      (by rw [hn, hx.table]; exact rl_later.2) recordRadius g
      (by rw [hn, hx.table]; exact le_of_eq rl_later.1) (by rw [hn]; exact hg)
    rw [hx.columns, hlog] at hl
    exact hl
  · have hz := (zeta_pays recordSet codes x P h).2
    rw [hr] at hz
    exact hz

end OnBytes.Params.Prices
