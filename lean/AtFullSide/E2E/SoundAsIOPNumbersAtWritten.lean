-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/SoundAsIOPNumbersAtWritten.lean: THE NUMBERS OF SOUNDNESS AS AN IOP HAVE A MEMBER: at the
library's written copy of the full-size public files, `storedPublicFiles`, WITH NO HYPOTHESIS.

E2E/SoundAsIOPNumbers.lean stands under three premises on the public files: in scope, read, protocolDataWellFormed says
yes. `premises_zFull` (AtFullSide/Bind/LiveAtNamed.lean) meets them at `storedPublicFiles`. Here its theorems are called
there.

  `mostWork_zFull`       no round has more than 32 bits of proof of work.
  `rounds_zFull`         the whole run has 67,391 rounds.
  `probability_zFull`    for every P, every fill and every prover of the whole run, over uniform points and
                         the challenges that pass: the conclusion fails with probability at most
                         67391 * 2^-96 (which is at most 2^-79: `probability_zFull_79`).

Limits. Those of E2E/SoundAsIOPNumbers.lean. `storedPublicFiles` is a value written in Lean; no theorem ties it to a
file on a disk. In the side library, since `theLive_zFull` is an evaluation that is heavy to build.
-/
import E2E.SoundAsIOPNumbers
import AtFullSide.Bind.LiveAtNamed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtFullSide.AtFiles
open Prob
open Iop (Strat Rho)
open AtPublicFiles.AtFiles
open VerifierAndGoals (storedPublicFiles)

/-- **No round at storedPublicFiles has more than 32 bits of proof of work.** -/
theorem mostWork_zFull : mostWorkAtFiles storedPublicFiles ≤ 32 :=
  mostWorkInScope storedPublicFiles AtFullSide.Tie.premises_zFull.1 AtFullSide.Tie.premises_zFull.2.2

/-- **The whole run at storedPublicFiles has 67,391 rounds.** -/
theorem rounds_zFull (P : (filesAt storedPublicFiles).Provers) (fill : ((filesAt storedPublicFiles).withProvers P).Fill) :
    (((filesAt storedPublicFiles).withProvers P).wholeRunShape fill).length = 67391 :=
  roundsInScope storedPublicFiles AtFullSide.Tie.premises_zFull.1 AtFullSide.Tie.premises_zFull.2.2 P fill

/-- **THE BOUND AT storedPublicFiles, WITH NO HYPOTHESIS.** -/
theorem probability_zFull (P : (filesAt storedPublicFiles).Provers) (fill : ((filesAt storedPublicFiles).withProvers P).Fill)
    (β : Type) (prover : Strat (((filesAt storedPublicFiles).withProvers P).wholeRunShape fill) β) :
    pr (unif (Rho (((filesAt storedPublicFiles).withProvers P).wholeRunShape fill))) (ConclusionFails storedPublicFiles P fill prover) ≤
      (67391 : ℝ≥0∞) * (2 : ℝ≥0∞)⁻¹ ^ 96 :=
  let ⟨scope, ⟨pp, read⟩, live⟩ := AtFullSide.Tie.premises_zFull
  probabilityInScope storedPublicFiles pp scope read live P fill β prover

/-- **The same, at most 2^-79.** -/
theorem probability_zFull_79 (P : (filesAt storedPublicFiles).Provers) (fill : ((filesAt storedPublicFiles).withProvers P).Fill)
    (β : Type) (prover : Strat (((filesAt storedPublicFiles).withProvers P).wholeRunShape fill) β) :
    pr (unif (Rho (((filesAt storedPublicFiles).withProvers P).wholeRunShape fill))) (ConclusionFails storedPublicFiles P fill prover) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 79 :=
  (probability_zFull P fill β prover).trans bound_le_79

end AtFullSide.AtFiles

#print axioms AtFullSide.AtFiles.mostWork_zFull
#print axioms AtFullSide.AtFiles.rounds_zFull
#print axioms AtFullSide.AtFiles.probability_zFull
#print axioms AtFullSide.AtFiles.probability_zFull_79
