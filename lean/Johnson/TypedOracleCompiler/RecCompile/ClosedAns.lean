-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/RecCompile/ClosedAns.lean: the bound `soundnessBoundOverTypedOracles` of the compiled verifier with the answers
alone in each chain's first query (Johnson/TypedOracleCompiler/RecCompile/CmsAnsPr.lean) is at most a closed step
function, at any bound 2^-a on a round's error.

Statements and proofs. `soundnessBoundOverTypedOracles W εs tC tP` is n · εs + 2 (n + 1)² / 2^lam at
n = 5 (tC + tP + tVC W + 1): the wire W stands in it, through `tVC W`, the verifier's own queries.
`levelAt s N` (Johnson/Thin/K/Level/LevelAt.lean) is 2^-(127 - (j + s)) at the least j with
N ≤ 2^j, if j + s ≤ 126, and ⊤ else: no wire stands in it.

Main names (for every object with records L, letters Bd, aT, aL and every wire W at hash length 256;
under a + s = 128, εs ≤ c · 2^-a, c ≤ 1 + 1/4 and `tVC W ≤ n`):
  `epsA_le_levelAt`: soundnessBoundOverTypedOracles W εs tC tP ≤ levelAt s (5 (tC + tP + n + 1) + 1).
  `epsA_le_level`: if also tC + tP + n + 1 ≤ 2^i and i + 3 + s ≤ 126:
    soundnessBoundOverTypedOracles W εs tC tP ≤ 2^-(127 - (i + 3 + s)), which is 2^-(a - 4 - i).
  `epsA_le_lin`: if 5 (tC + tP + n + 1) + 1 is at most 2^126 / 2^s:
    soundnessBoundOverTypedOracles W εs tC tP ≤ (5 (tC + tP + n + 1) + 1) · 2^s · 2^-127: linear in the queries.

Limits: the hash length 256 is fixed, and a ≤ 128. These statements do not say that any object meets
the premises, nor that `soundnessBoundOverTypedOracles` bounds anything, and give no numeral. No bound on `tVC W` at a named
wire is given.


-/
import Johnson.TypedOracleCompiler.RecCompile.CmsAnsPr
import Johnson.Thin.K.Level.LevelAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.TopC
open scoped ENNReal

variable {I X : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}

/-- The bound is at most the closed step function. -/
theorem epsA_le_levelAt (W : QueryLayout 256 (typedOracleCarrier L Bd aT aL)) (εs c : ℝ≥0∞) (a s n tC tP : ℕ)
    (has : a + s = 128) (he : εs ≤ c * ((2 : ℝ≥0∞) ^ a)⁻¹) (hc : c ≤ 1 + (4 : ℝ≥0∞)⁻¹)
    (hV : tVC W ≤ n) :
    soundnessBoundOverTypedOracles W εs tC tP ≤ levelAt s ((tC + tP + n + 1) * 5 + 1) :=
  le_trans (level_at_le a s ((tC + tP + tVC W + 1) * (1 + 4)) εs c has he hc)
    (levelAt_mono s (Nat.succ_le_succ (Nat.mul_le_mul_right 5 (by omega))))

/-- The same in levels. -/
theorem epsA_le_level (W : QueryLayout 256 (typedOracleCarrier L Bd aT aL)) (εs c : ℝ≥0∞) (a s n tC tP i : ℕ)
    (has : a + s = 128) (he : εs ≤ c * ((2 : ℝ≥0∞) ^ a)⁻¹) (hc : c ≤ 1 + (4 : ℝ≥0∞)⁻¹)
    (hV : tVC W ≤ n) (hi : tC + tP + n + 1 ≤ 2 ^ i) (hj : i + 3 + s ≤ 126) :
    soundnessBoundOverTypedOracles W εs tC tP ≤ ((2 : ℝ≥0∞) ^ (127 - (i + 3 + s)))⁻¹ :=
  le_trans (epsA_le_levelAt W εs c a s n tC tP has he hc hV)
    (levelAt_le s _ (i + 3) (by
      have h1 : 1 ≤ 2 ^ i := Nat.one_le_two_pow
      rw [pow_add]
      omega) hj)

/-- The same, linear in the queries. -/
theorem epsA_le_lin (W : QueryLayout 256 (typedOracleCarrier L Bd aT aL)) (εs c : ℝ≥0∞) (a s n tC tP : ℕ)
    (has : a + s = 128) (he : εs ≤ c * ((2 : ℝ≥0∞) ^ a)⁻¹) (hc : c ≤ 1 + (4 : ℝ≥0∞)⁻¹)
    (hV : tVC W ≤ n) (hn : ((tC + tP + n + 1) * 5 + 1) * 2 ^ s ≤ 2 ^ 126) :
    soundnessBoundOverTypedOracles W εs tC tP ≤
      ((((tC + tP + n + 1) * 5 + 1) * 2 ^ s : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ 127)⁻¹ := by
  have hm : ((tC + tP + tVC W + 1) * (1 + 4) + 1) * 2 ^ s ≤ ((tC + tP + n + 1) * 5 + 1) * 2 ^ s :=
    Nat.mul_le_mul_right _ (Nat.succ_le_succ (Nat.mul_le_mul_right 5 (by omega)))
  exact le_trans
    (level_at_lin a s ((tC + tP + tVC W + 1) * (1 + 4)) εs c has he hc (le_trans hm hn))
    (mul_le_mul' (by exact_mod_cast hm) le_rfl)

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.epsA_le_levelAt
#print axioms TypedOracleCompiler.Compile.Batch.Cms.epsA_le_level
#print axioms TypedOracleCompiler.Compile.Batch.Cms.epsA_le_lin
