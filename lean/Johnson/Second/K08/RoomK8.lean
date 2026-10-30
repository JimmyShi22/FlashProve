--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Second/K08/RoomK8.lean: THE SMALLNESS TEST's 25 ROUNDS «RNG» OF THE FULL-SIZE PROOF FILE's
FIRST CHAIN, ONE BY ONE: the count that the kind's law as typed charges, against the cap 2⁻¹ ^ 128,
with the written plan's own error bound beside it, in whole numbers, by Lean's kernel.
Why. It was asked whether the law can hold at the cap at the release's
numbers: «room 0 by a one-column count; 2^-113.44 by a union bound». NO LAW IS NEW HERE: the kind
has, general in the place, k08CountCap128 and k08CountNoRoom
(Johnson/Desc/First/K8/LawCap.lean).
This file lays them at the 25 written rounds. Definitions, statements, proofs.
  rngRows P            of a list of rounds with error bounds: (position, trits, work, the bound's m,
  its
                       e) of the rounds named "RNG".
  table · tableRows    25 (position, columns), written out · the rows that follow: trits = columns ·
                       128, work 0, bound ⟨1, −128⟩.
  ★ rng_rows_written   rngRows proofLit.plan = tableRows. proofLit.plan is the written first list of
  the
                       proof file (48,293 rounds), which the verifier's test madeIs compares whole.
  rng_rest_written     at all 25: no group · no word fault · why .small · scope .request · no other
  field
                       of the entry is set.
  rng_rows_dry         the rounds of dryProofFull.1 that pass isSmall (the list of the kind's

                       AtWritten) stand at the same positions with the same trits and work.
  rng_rows_moved       a negative test: with the list's first round dropped the rows are others.
  rowB t               with N := 4 ^ t (the typed values: card_dr) and n := N / 2 ^ 128 (the law's
  count):
                       n · 2 ^ 128 = N · N < (n + 1) · 2 ^ 128 · N < n · 2 ^ 129 · N < (t / 128) · n
                       · 2 ^ 128.
  ★ rng_rows_room      every one of the 25 rows passes rowB. So the count's share of the typed
  values IS
                       the plan's bound 2^-128: room 0, and nothing over; one more bad value, or the
                       bar
                       2^-129, is too much; the count times the number of columns does not fit.
  ★ law_at_row         at a row r of the table and all p, s with Fits p s, p.tau = 128, s.columns *
  s.tau =
                       r's trits: the law's count card (Dr s) / 2 ^ s.tau is 4 ^ trits / 2 ^ 128 ·
                       it is
                       RoundBelow at 2⁻¹ ^ 128 · with one more it is not · at 2⁻¹ ^ 129 it is not.
  union_bits           2 ^ 14 < 24086 < 2 ^ 15 · 2 ^ 13 < 10248 < 2 ^ 14 · 2 ^ 14 < 20703 < 2 ^ 15.
  ★ rng_rows_in_scope  InScope W · ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z · madePinnedAt
  Z.p.X.P
                       Z.p.chains.made Z.first Z.made = true ⊢ the made plan's first list has these
                       rows.
Limits. THAT THE ROUND IS KNOWLEDGE SOUND AT THAT COUNT is the library's proved block (HoleAt,
Cb/Pv/Tail/Block.lean; block_good, Johnson/Desc/First/K8/Law.lean, under d.c.s.OK): not said here,
and
that OK is met at the 25 places is not shown here. That what is tested is committed before the draw
is not shown here. ONE ROUND OF ONE REQUEST: no sum over the 25 rounds, none over requests. That
a place's p has 128 combinations and these columns is law_at_row's premise. Lean's port of the
planner, not the C++ program; what the programs print is not read here. No soundness and no level is
claimed.

-/
import Johnson.Goal.Numbers.MadeInScope
import Johnson.Desc.First.K8.LawCap
import Johnson.Desc.First.K8.RoundsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace Second.K08
open OnBytes OnBytes.Params OnBytes.Slice Johnson.G Cb.Pv.Tail
open VerifiableInference.Number (isSmall)
open VerifiableInference.Desc.First.K8 (Par Fits rd k08CountCap128 k08CountNoRoom)
open VerifiableInference.PlanWritten (madePinnedAt made_of_pinned proofLit key_in_scope_pure)

def rngRows (P : Planned) : List (ℕ × ℕ × ℕ × ℕ × ℤ) :=
  (P.rounds.zipIdx.filter fun x => x.1.entry.name == "RNG").map fun x =>
    (x.2, x.1.entry.trits, x.1.entry.work, x.1.error.m, x.1.error.e)

/-- (position in the written list, columns). -/
def table : List (ℕ × ℕ) := [
  (1220, 24086), (3130, 10248), (5077, 24086), (6987, 10248), (8934, 24086), (10844, 10248),
  (12791, 24086), (14701, 10248), (16648, 24086), (18558, 10248), (20505, 24086), (22415, 10248),
  (24362, 24086), (26272, 10248), (28219, 24086), (30129, 10248), (32076, 24086), (33986, 10248),
  (35933, 24086), (37843, 10248), (39790, 24086), (41700, 10248), (43647, 24086), (45557, 10248),
  (47453, 20703)]

def tableRows : List (ℕ × ℕ × ℕ × ℕ × ℤ) := table.map fun x => (x.1, x.2 * 128, 0, 1, -128)

/-- ★ -/
theorem rng_rows_written : rngRows proofLit.plan = tableRows := by decide +kernel

theorem rng_rest_written :
    ((proofLit.plan.rounds.filter fun x => x.entry.name == "RNG").all fun x =>
      !x.group.isSome && !x.wordFault && decide (x.why = .small) && decide (x.scope = .request) &&
        decide (x.entry = { name := "RNG", trits := x.entry.trits })) = true := by
  decide +kernel

theorem rng_rows_dry :
    ((dryProofFull.1.zipIdx.filter fun x => isSmall x.1.1.entry).map fun x =>
      (x.2, x.1.1.entry.trits, x.1.1.entry.work)) = table.map fun x => (x.1, x.2 * 128, 0) := by
  decide +kernel

theorem rng_rows_moved :
    decide (rngRows ⟨proofLit.plan.set, proofLit.plan.rounds.drop 1⟩ = tableRows) = false := by
  decide +kernel

def rowB (t : ℕ) : Bool :=
  decide (4 ^ t / 2 ^ 128 * 2 ^ 128 = 4 ^ t) && decide (4 ^ t < (4 ^ t / 2 ^ 128 + 1) * 2 ^ 128) &&
    decide (4 ^ t < 4 ^ t / 2 ^ 128 * 2 ^ 129) &&
    decide (4 ^ t < t / 128 * (4 ^ t / 2 ^ 128) * 2 ^ 128)

/-- ★ -/
theorem rng_rows_room : (tableRows.all fun r => rowB r.2.1) = true := by decide +kernel

theorem rows_positive : (tableRows.all fun r => decide (0 < r.2.1)) = true := by decide +kernel

/-- ★ -/
theorem law_at_row {r : ℕ × ℕ × ℕ × ℕ × ℤ} (hr : r ∈ tableRows) (p : Par) (s : Size)
    (hf : Fits p s) (hτ : p.tau = 128) (hc : s.columns * s.tau = r.2.1) :
    Fintype.card (Dr s) / 2 ^ s.tau = 4 ^ r.2.1 / 2 ^ 128 ∧
      RoundBelow (Fintype.card (Dr s) / 2 ^ s.tau) (rd p) ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧
      ¬ RoundBelow (Fintype.card (Dr s) / 2 ^ s.tau + 1) (rd p) ((2 : ℝ≥0∞)⁻¹ ^ 128) ∧
      ¬ RoundBelow (Fintype.card (Dr s) / 2 ^ s.tau) (rd p) ((2 : ℝ≥0∞)⁻¹ ^ 129) := by
  have h0 : 0 < r.2.1 := of_decide_eq_true (List.all_eq_true.1 rows_positive r hr)
  have h1 : 1 ≤ s.columns := by
    rcases Nat.eq_zero_or_pos s.columns with e | e
    · rw [e, Nat.zero_mul] at hc
      exact absurd h0 (by rw [← hc]; exact Nat.lt_irrefl 0)
    · exact e
  exact ⟨by rw [card_dr, hc, hf.tau, hτ], k08CountCap128 p s hf hτ,
    (k08CountNoRoom p s hf hτ h1).1, (k08CountNoRoom p s hf hτ h1).2⟩

theorem union_bits :
    2 ^ 14 < 24086 ∧ 24086 < 2 ^ 15 ∧ 2 ^ 13 < 10248 ∧ 10248 < 2 ^ 14 ∧ 2 ^ 14 < 20703 ∧
      20703 < 2 ^ 15 := by decide

/-- ★ -/
theorem rng_rows_in_scope {o : ProofFile.SecondHashFunctionArgument} {W : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    (hW : VerifierAndGoals.InScope W = true) (h : ProofFile.pureRoad.pub o W.pol W.lay W.KL = .ok Z)
    (hy : madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    Z.p.chains.made.proof.head?.map rngRows = some tableRows := by
  unfold madePinnedAt at hy
  rw [key_in_scope_pure hW h] at hy
  rw [(made_of_pinned hy).1.2]
  exact congrArg some rng_rows_written

end Second.K08

#print axioms Second.K08.rng_rows_written
#print axioms Second.K08.rng_rest_written
#print axioms Second.K08.rng_rows_dry
#print axioms Second.K08.rng_rows_moved
#print axioms Second.K08.rng_rows_room
#print axioms Second.K08.rows_positive
#print axioms Second.K08.law_at_row
#print axioms Second.K08.union_bits
#print axioms Second.K08.rng_rows_in_scope
