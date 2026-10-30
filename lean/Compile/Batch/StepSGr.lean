-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/StepSGr.lean: the step (S) of Compile/Batch/StepS.lean for a wire record whose rounds
may have proof-of-work bits. (Words of this library: lean/GLOSSARY.md.)

It assumes `W.OKG` (Iop/BatchWire.lean) and uses one field: there are 2^depthReq slots. `stepSGr`,
under `Seed.carryS`'s hypotheses on σ, bk, b: for a relation of the form `relPair Ryes Rno sub`,
whatever extractor, simulator and bounds `argBKE` has, `argP` has them with b added to α and
`zS σ b` to ζ. A `Carry` is an implication: it says nothing unless something is known about
`argBKE`. The search over nonces takes no sample (Compile/Batch/SeedShape.lean), which is why
nothing else is assumed of the wire record.

Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Limits: those of the header of Compile/Batch/StepS.lean; and nothing about the stop at a failed
search, nor about probabilities of a failed proof-of-work check.
-/
import Compile.Batch.StepS
import Compile.Batch.SeedGhost
import Compile.Batch.Prog
import Compile.GenStop

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP Compile.GenMap
open scoped ENNReal

/-- (S), the rounds may have proof-of-work bits (hypotheses below). -/
def Spec.stepSGr : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (Ryes Rno : I → X → Prop) (sub : ∀ i x, Ryes i x → Rno i x) (B : ℕ) (bk : CoinPlan)
      (σ : SeedOracle (spec lam W.K L)) (b : ℝ≥0∞),
    W.OKG → σ.o = OracleName.other → σ.bias bk.w = 0 → (∀ i, (C W WP p i).pathBiasB bk ≤ b) →
    Carry (relPair Ryes Rno sub) B (argBKE W WP p) (argP W WP p bk σ) b (zS σ b)

theorem stepSGr : Spec.stepSGr := fun _ _ _ _ W WP p _ _ _ B bk σ b hW hσ hw hb =>
  Seed.carryS W WP p _ B bk σ b hW.slots hσ hw hb

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (stp : X → List (Blk lam W.K) → Bool) (gV : IVKK lam L → X → PrfK lam L → TypedOracleComputation lam W.K L Bool)
  (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L))

end Compile.Batch
