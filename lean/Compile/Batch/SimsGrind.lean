-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SimsGrind.lean: the three simulators of single sessions for a record of protocols with
proof-of-work bits (`L.grind`), as terms, from those of L. (Words of this library:
lean/GLOSSARY.md.)

  `Sims.grind`   the simulators of L at the verifier randomness without its proof-of-work bits, with
                 the fixed nonce put into the plain part of every round that has such bits
                 (Iop/Grind.lean: `simGrind`; Iop/BatchGrind.lean: `simGrindB`)
  `Sims.Good.grind`   if Sm is good with zT, zL, zO (`Sims.Good`, Compile/Batch/SpecLife.lean), they
                      (`Sm.grind`) are good with the same three numbers: where the simulator of L is
                      exact at the stripped randomness the new one is exact, whatever these bits
                      are, and under the uniform distribution the stripped randomness is uniform

Why. The compiler's theorems that name their simulator take three simulators of single sessions
(Compile/Batch/SpecLife.lean: `Sims`, `Sims.Good`). Iop/BatchGrindProofs.lean proves that hiding is
preserved ("there is a simulator"); here the terms.

Limits. These are simulators of the interactive protocols, whose honest provers send the fixed
nonce; the search for a nonce belongs to the compiler. They do not depend on the proof-of-work bits.
No statement here is a security level.
-/
import Iop.BatchGrindProofs
import Iop.GrindProofs
import Compile.Batch.SpecLife

noncomputable section

namespace Compile.BatchLife
open Iop Prob
open scoped ENNReal

variable {W : Type} [Inhabited W] {I X : Type} {L : BatchProtocol I X}

/-- The three simulators for the record of protocols with proof-of-work bits. -/
def Sims.grind (Sm : Sims L) (gT : GBits L.offline.shape)
    (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) : Sims (L.grind W gT gL gB) where
  T := simGrind gT (GNon.nil W _) Sm.T
  Lk := simGrind gL (GNon.nil W _) Sm.Lk
  B := simGrindB gB (fun _ _ => GNon.nil W _) Sm.B

/-- If Sm is good with zT, zL, zO (`Sims.Good`, Compile/Batch/SpecLife.lean), so is `Sm.grind`. -/
theorem Sims.Good.grind {Sm : Sims L} {Ryes : I → X → Prop} {zT zL zO : ℝ≥0∞}
    (h : Sm.Good Ryes zT zL zO) (gT : GBits L.offline.shape)
    (gL : GBits L.link.shape) (gB : GBits L.onlineBatch.loc.shape) :
    (Sm.grind (W := W) gT gL gB).Good Ryes zT zL zO where
  goodT := fun w x => by
    refine le_trans
      (le_trans (pr_mono _ ?_)
        (le_of_eq
          (grindUnif W _ gT {ρ | L.honestOfflineProver.output w x ρ ≠ Sm.T x ρ (L.offline.extAns x ρ (L.honestOfflineProver.ext w))})))
      (h.goodT w x)
    intro ρ hρ heq
    exact hρ ((grindSim W _ _ L.offline _ L.honestOfflineProver gT (GNon.nil W _) Sm.T w x ρ).2 heq)
  goodL := fun w x => by
    refine le_trans
      (le_trans (pr_mono _ ?_)
        (le_of_eq
          (grindUnif W _ gL {ρ | L.honestLinkProver.output w x ρ ≠ Sm.Lk x ρ (L.link.extAns x ρ (L.honestLinkProver.ext w))})))
      (h.goodL w x)
    intro ρ hρ heq
    exact hρ ((grindSim W _ _ L.link _ L.honestLinkProver gL (GNon.nil W _) Sm.Lk w x ρ).2 heq)
  goodB := fun w x hv J xs hxs => by
    refine le_trans
      (le_trans (pr_mono _ ?_)
        (le_of_eq (grindUnifB W L.maxBatchSize _ _ gB
            {ρ | L.honestOnlineBatchProver.output w x ρ J ≠
              Sm.B J xs (fun j => ρ.slot j.1)
                (L.onlineBatch.extAnsJ J xs (fun j => ρ.slot j.1) (L.honestOnlineBatchProver.ext w))})))
      (h.goodB w x hv J xs hxs)
    intro ρ hρ heq
    exact hρ (grindSimB W _ _ L.onlineBatch _ L.honestOnlineBatchProver gB (GNon.nil W _) L.maxBatchSize Sm.B w x ρ J xs heq)

end Compile.BatchLife
