-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Top/WrittenAtFull.lean: at `VerifierAndGoals.storedPublicFiles` the data that the verifier's description holds
for the key file and for the proof file are the written data, with no premise.

What it says. `written_zFull`: the second arm of `written_or_no_all`
(Johnson/Goal/Description/KeyWritten.lean) to the letter, at `OnBytes.secondHashFunction` and `storedPublicFiles`. It is
`written_zFull_of` (Johnson/AtFull/Top/WrittenAtZFull.lean) with its two premises shown (`lay_size`,
AtFullSide/Layout/Size.lean; `layoutRead_full`, AtFullSide/LayoutRead/Full.lean).

Why here. The two closed facts on the layout file are shown in this side library, which is built
with a larger thread stack than the files under lean/Johnson/. Nothing under lean/Johnson/ imports
it.

Limits. Those of Johnson/AtFull/Top/WrittenAtZFull.lean, whole. THE TWO ARMS DO NOT EXCLUDE EACH
OTHER: that the second holds does not show that the verifier accepts any proof. "Data" are a depth,
three lists of rounds and three functions on numbers for each file (`OnBytes.Maker.WholeD`), not
bytes of a file and not weights. Nothing on soundness, on binding or on hiding is shown here.

-/
import Johnson.AtFull.Top.WrittenAtZFull
import AtFullSide.Layout.Size
import AtFullSide.LayoutRead.Full

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Top

/-- **AT `VerifierAndGoals.storedPublicFiles` THE KEY FILE'S AND THE PROOF FILE'S DATA ARE THE WRITTEN DATA.** No
premise. -/
theorem written_zFull :
    FlashProve.theKeyDataAt OnBytes.secondHashFunction (VerifierAndGoals.asDescriptionFiles VerifierAndGoals.storedPublicFiles) = Johnson.G.writtenKFull ∧
      FlashProve.theProofDataAt OnBytes.secondHashFunction (VerifierAndGoals.asDescriptionFiles VerifierAndGoals.storedPublicFiles) =
        Johnson.G.writtenPFull :=
  _root_.AtFull.Top.written_zFull_of Johnson.Unfolds.Layout.lay_size
    Johnson.AtFull.LayoutRead.layoutRead_full

end AtFullSide.Top

#print axioms AtFullSide.Top.written_zFull
