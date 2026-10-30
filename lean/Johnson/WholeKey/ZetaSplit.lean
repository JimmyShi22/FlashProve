-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/WholeKey/ZetaSplit.lean: the error term zetaW (defined in Johnson/WholeKey/Zeta.lean) of the
theorem on index privacy equals its value with seven error numbers set to 0, plus an explicit
weighted sum of those seven numbers.

What this file has.
zetaW_split: an equation, for all parameters, every structure u of the numbers (NumsW), every number
t of queries and every number n of requests. zetaW at u is zetaW at u with zT, zL, zO, hT, hL, hO
and δ set to 0, plus an explicit sum. The sum is (zT + (M + 1) · zL + n · zO) + (hT + (M + 1) · hL +
n · hO) + (M + 2) · δ. The other six numbers of u, among them s1, are kept. With the seven set to 0,
zetaW is the sum of its two remaining terms: the tail term, which reads s1, and the cost of the hash
queries, which reads no number of u.
Here M + 1 is the number of copies, and M + 2 the number of tables (the first table and its copies).
In the premises PremW (Johnson/WholeKey/Premises.lean), zT, zL and zO bound the errors of the three
simulators of the interactive protocols. hT, hL and hO bound the measures of the aborts that may
depend on the private input. δ bounds the probability that a seed made from uniform digests lies
outside the public set Gs of seeds.

  err_le_zetaW   the explicit sum of the seven terms is a lower bound on zetaW. So every upper bound
      on zetaW is at least this sum; none, for example, is below n · hO.
  zetaW_clear_le   zetaW with the seven numbers set to 0 is a lower bound on zetaW.

How it fits. It rests on the definition of zetaW alone. It serves upper bounds on zetaW: a bound
that is proved where the seven numbers are 0 gives, with the explicit sum added, a bound at all
numbers. A lemma on the way to index privacy (Johnson/WholeKey/Statement.lean); not one of the
release's goal statements.

Limits.
  It is arithmetic on an explicit expression and gives no number. Whether any of the seven numbers
      can be taken small for a given prover is not said here.
  What zetaW bounds, and under which premises, is stated in Johnson/WholeKey/Statement.lean. What a
      bound of 1 or more means for index privacy: see Johnson/WholeKey/Zeta.lean, Limits.
Terms: Johnson/WholeKey/Defs.lean.
-/
import Johnson.WholeKey.Zeta

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom Prob
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (p : Params) (a : AtRecs lam L Bd aT aL) (c : CoinNums Bd) (u : NumsW)

/-- **zetaW is its value with the seven error numbers set to 0, plus the explicit sum of the
seven.** -/
theorem zetaW_split (t n : ℕ) :
    zetaW W S p a c u t n =
      zetaW W S p a c
          { u with zT := 0, zL := 0, zO := 0, hT := 0, hL := 0, hO := 0, δ := 0 } t n +
        ((u.zT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.zL + (n : ℝ≥0∞) * u.zO) +
          (u.hT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.hL + (n : ℝ≥0∞) * u.hO) +
          ((a.M + 2 : ℕ) : ℝ≥0∞) * u.δ) := by
  unfold zetaW
  dsimp only
  simp only [mul_zero, add_zero]
  ring

/-- The explicit sum of the seven error numbers is a lower bound on zetaW. -/
theorem err_le_zetaW (t n : ℕ) :
    (u.zT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.zL + (n : ℝ≥0∞) * u.zO) +
        (u.hT + ((a.M + 1 : ℕ) : ℝ≥0∞) * u.hL + (n : ℝ≥0∞) * u.hO) +
        ((a.M + 2 : ℕ) : ℝ≥0∞) * u.δ ≤ zetaW W S p a c u t n := by
  rw [zetaW_split W S p a c u t n]
  exact le_add_self

/-- zetaW with the seven error numbers set to 0 is a lower bound on zetaW. -/
theorem zetaW_clear_le (t n : ℕ) :
    zetaW W S p a c { u with zT := 0, zL := 0, zO := 0, hT := 0, hL := 0, hO := 0, δ := 0 } t n ≤
      zetaW W S p a c u t n := by
  rw [zetaW_split W S p a c u t n]
  exact le_self_add

end OnBytes.WholeKey

#print axioms OnBytes.WholeKey.zetaW_split
#print axioms OnBytes.WholeKey.err_le_zetaW
#print axioms OnBytes.WholeKey.zetaW_clear_le
