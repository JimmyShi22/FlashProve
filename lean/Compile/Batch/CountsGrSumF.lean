-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CountsGrSumF.lean: the three sums over a list of numbers of proof-of-work bits that
occur in the bounds with such bits are sums `GBits.sumF` (Iop/GBitsSumF.lean), so that they can be
evaluated by the structure of the list, not round by round (words of this library:
lean/GLOSSARY.md).

  `sumMo_eq_sumF`  GBits.sumMo D s g = GBits.sumF D.mo g: the attempts after the first, at most
                   (Compile/Batch/CountsGrind.lean)
  `nTests_eq_sumF`  nTests s g = GBits.sumF (fun _ => 1) g: the rounds with such bits
                    (Compile/Batch/CountsGrTot.lean)
  `gFail_eq_sumF`  gFail D g = GBits.sumF (failBits D) g: the sum of the probabilities that a search
                   fails (Compile/Batch/FitGrind.lean)
  `sumF_pull`  the sums do not change when verifier messages are sampled from hash blocks
               (`GBits.pull`, Iop/GrindPull.lean)

Limits: nothing on any protocol.
-/
import Compile.Batch.CountsGrTot
import Iop.GBitsSumF
import Iop.GrindPull

noncomputable section

namespace Compile.Batch
open Iop
open scoped ENNReal

variable {Wn : Type}

theorem sumMo_eq_sumF (D : GrData Wn) :
    ∀ (s : Shape) (g : GBits s), GBits.sumMo D s g = GBits.sumF D.mo g
  | [], _ => rfl
  | _ :: s, (b, g) => congrArg ((if b = 0 then 0 else D.mo b) + ·) (sumMo_eq_sumF D s g)

theorem nTests_eq_sumF : ∀ (s : Shape) (g : GBits s), nTests s g = GBits.sumF (fun _ => 1) g
  | [], _ => rfl
  | _ :: s, (b, g) => congrArg ((if b = 0 then 0 else 1) + ·) (nTests_eq_sumF s g)

theorem gFail_eq_sumF (D : GrData Wn) :
    ∀ {s : Shape} (g : GBits s), gFail D g = GBits.sumF (failBits D) g
  | [], _ => rfl
  | _ :: _, (0, g) => congrArg ((0 : ℝ≥0∞) + ·) (gFail_eq_sumF D g)
  | _ :: _, (b + 1, g) => congrArg (failBits D (b + 1) + ·) (gFail_eq_sumF D g)

theorem sumF_pull {M : Type} [AddCommMonoid M] (f : ℕ → M) :
    ∀ {s : Shape} (σ : Samplers s) (g : GBits s), GBits.sumF f (GBits.pull σ g) = GBits.sumF f g
  | [], _, _ => rfl
  | _ :: _, (_, σs), (b, g) => congrArg ((if b = 0 then 0 else f b) + ·) (sumF_pull f σs g)

end Compile.Batch
