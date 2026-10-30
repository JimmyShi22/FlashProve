-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/StepS.lean: the step (S) from `argBKE` to `argP`: the committer's coins come from one
seed, isk = (i, seed), and the prover recomputes the `Node` of the sampled copy. The theorem is a
`Carry` (Rom/Carry.lean). (Words of this library: lean/GLOSSARY.md.)

  `tokFree_faceKE`, `noOther_faceKE`
      the two properties of programs that Compile/Batch/SeedStar.lean requires, for `argBKE`: its
      program of a batch does not look at the numbers of its tokens (if L.maxBatchSize = 2 ^ W.depthReq); it
      and V never query the auxiliary oracle
  `carryS`   if L.maxBatchSize = 2 ^ W.depthReq, σ.o = `OracleName.other` and σ.bias bk.w = 0: whatever extractor,
             simulator and bounds (α, ε, ζ) `argBKE` has, `argP` has the same extractor and
             simulator with α + b, ε, ζ(t, n) + b + t / (number of seeds). b bounds the bias, along
             a path of C, of the samples made from small ones; t bounds the adversary's queries to
             all oracles
  `bStd`   nWideB · 2^-λ / 4, where `nWideB` counts those samples of C that do not have exactly 2^λ
           outcomes: for λ > 0 it can be taken for b with `blocksStd` (Compile/SeedStd.lean;
           `pathBiasB_C_std`, Compile/Batch/SeedStd.lean)
  `bStd_le`   if all salts have λ bits, bStd ≤ 3 (M + 2) · 2^-λ / 4

The hypothesis L.maxBatchSize = 2 ^ W.depthReq (a field of `QueryLayout.OK`). The programs of
Compile/Batch/Prover.lean write the number 0 where no token is meant. That no such 0 is ever read is
proved for full request trees only; in the store of C the number 0 denotes one string and in the
small store of the prover with the seed another.

Limits: the header of Compile/Batch/SeedStar.lean. Perfect completeness is not carried over by a
`Carry`.
-/
import Compile.Batch.StarS
import Compile.Batch.SeedMain
import Compile.Batch.SeedParU
import Compile.Batch.SeedAvoid
import Compile.Batch.SeedAvoidU
import Compile.Batch.SeedLabelStd
import Compile.SeedSize
import Rom.Carry

noncomputable section

open Rom Iop ZKCP
open scoped ENNReal

namespace Compile.Batch
namespace Seed

open Compile.Seed (blocksStd)

variable {I X PP : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

theorem tokFree_faceKE (hN : L.maxBatchSize = 2 ^ W.depthReq) : (faceKE W WP p).TokFree :=
  tokFree_faceOf WP p _ fun _ _ trees w fl xs hx =>
    par_proveBU p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ _ _ W.depthReq trees w fl xs (hx.trans hN)

theorem noOther_faceKE : (faceKE W WP p).NoOther :=
  noOther_faceOf WP p _
    (fun trees w fl xs vs =>
      avoids_proveBU p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ _ _ W.depthReq trees w fl xs vs)
    (avoids_V W p)

/-- (S) The committer's coins come from one seed (hypotheses below). -/
theorem carryS (R : Gen.RelPair I X Unit PP) (B : ℕ) (bk : CoinPlan)
    (σ : SeedOracle (spec lam W.K L)) (b : ℝ≥0∞) (hN : L.maxBatchSize = 2 ^ W.depthReq) (hσ : σ.o = OracleName.other)
    (hw : σ.bias bk.w = 0) (hb : ∀ i, (C W WP p i).pathBiasB bk ≤ b) :
    Carry R B (argBKE W WP p) (argP W WP p bk σ) b
      (fun t _ => b + (t : ℝ≥0∞) / (σ.sd + 1 : ℕ)) := fun E Sim α ε ζ h =>
  mono_with (seedMainB I X PP lam L W WP p _ _ (faceKE W WP p) bk σ R B E Sim α b ε ζ hσ hw hb
      (tokFree_faceKE W WP p hN) (noOther_faceKE W WP p) (argBKE_eq W WP p ▸ h))
    le_rfl (fun _ _ => le_rfl) fun _ _ => (add_assoc _ _ _).le



/-- the term b for the standard decomposition into small samples -/
def bStd : ℝ≥0∞ := nWideB W WP p * (((4 * 2 ^ lam : ℕ) : ℝ≥0∞))⁻¹

theorem bStd_le (h1 : p.sMT = lam) (h2 : p.sFS = lam) :
    bStd W WP p ≤ (3 * (p.M + 2) : ℕ) * (((4 * 2 ^ lam : ℕ) : ℝ≥0∞))⁻¹ :=
  mul_le_mul_left (Nat.cast_le.2 (nWideB_le W WP p h1 h2)) _


end Seed
end Compile.Batch
