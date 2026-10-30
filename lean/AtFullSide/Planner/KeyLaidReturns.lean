-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Planner/KeyLaidReturns.lean: the key file's maker returns at the three full-size public
files as Ladder/Stored.lean spells them (`VerifierAndGoals.storedPublicFiles`), with no premise.

What it says. `theKeyLaid_zFull_returns`: `FlashProve.theKeyLaid (asDescriptionFiles storedPublicFiles)` returns the
written description of the key file, `writtenKFull`, with a run that is named from m, where m is
what `Key.madeAt` returns at the public part X₀ that `publicOfO` returns. It is `theKeyLaid_zFull`
(Johnson/AtFull/Top/KeyLaidZFull.lean) with its two premises shown: the layout file has 224,975
bytes (`lay_size`, AtFullSide/Layout/Size.lean) and reads as the written value `LW`
(`layoutRead_full`, AtFullSide/LayoutRead/Full.lean).

What it is for. The test `protocolDataWellFormed` accepts in the goals' scope where two makers return: the key
file's and the proof file's (`theLive_of_two`, Johnson/AtFull/Top/LiveOfTwo.lean). This is the first
of the two at `VerifierAndGoals.storedPublicFiles`. A run of Lean's evaluator can show such a return too, but proves
nothing; this is a theorem.

Why here. The two closed facts on the layout file stand over one constant (`lay_chars`,
AtFullSide/Layout/TieRfl.lean) that was seen to fail in Lean's kernel at the default thread stack
and passes at 128 MB: so they, and what calls them, stand in a side library, built with a larger
thread stack. Nothing under lean/Johnson/ imports it.

Limits. THE PROOF FILE's MAKER IS NOT SHOWN TO RETURN IN THIS FILE: so `protocolDataWellFormed` is not shown here
to accept at these files, and no example of the head is shown in this file; one, at storedPublicFiles alone, is
AtFullSide.Top.headMember_zFull, whose own Limits say what it is worth. At `VerifierAndGoals.storedPublicFiles` alone: not
at other files in the goals' scope, not at the files whose policy has limits (`VerifierAndGoals.zGap`).
`VerifierAndGoals.storedPublicFiles` is three terms written in Ladder/Stored.lean: no Lean code ties them to the top-level
folder examples/; the example's weights are synthetic. At the second hash function `OnBytes.secondHashFunction`,
a fixed function, and at the constant `fixedConfigurationDigest` in the digest's place, not at the digest of these
files. The closed facts beneath are proved by evaluation in Lean's kernel (`decide +kernel`; the
layout file's literal by `kernel_rfl`, Johnson/Unfolds/KernelRfl.lean, under a thread stack of 128
MB): no compiled code, no axiom beyond Lean's three. They have been checked by Lean's own kernel
alone: no independent checker has replayed them. Nothing on soundness.
-/
import Johnson.AtFull.Top.KeyLaidZFull
import AtFullSide.Layout.Size
import AtFullSide.LayoutRead.Full

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Planner
open VerifiableInference.Desc

/-- **THE KEY FILE's MAKER RETURNS AT THE THREE FILES OF `VerifierAndGoals.storedPublicFiles`.** No premise. -/
theorem theKeyLaid_zFull_returns :
    ∃ X₀ m,
      VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL
        (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      Key.madeAt X₀ VerifierAndGoals.storedPublicFiles.lay Key.fixedDigest = .ok m ∧
      FlashProve.theKeyLaid (VerifierAndGoals.asDescriptionFiles VerifierAndGoals.storedPublicFiles) =
        .ok (Johnson.G.writtenKFull,
          ((Key.descriptionFromSource (Johnson.AtFull.KeyBack.sourceKFull m) Johnson.KB8.rangesNumsFull
            Johnson.KB8.laterPlacesFull).pull Key.keyInstanceOfOutOfDomainSample).run) := by
  have h := Johnson.AtFull.Top.theKeyLaid_zFull Johnson.Unfolds.Layout.lay_size
    Johnson.AtFull.LayoutRead.layoutRead_full
  exact h

#print axioms AtFullSide.Planner.theKeyLaid_zFull_returns

end AtFullSide.Planner
