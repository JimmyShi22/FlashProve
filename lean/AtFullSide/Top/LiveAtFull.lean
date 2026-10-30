-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Top/LiveAtFull.lean: the test `protocolDataWellFormed` (Johnson/Goal/Description/Live.lean) accepts at
the three public files `VerifierAndGoals.storedPublicFiles` as Ladder/Stored.lean spells them, with no premise.

What it says. `theLive_zFull`: `FlashProve.protocolDataWellFormed (asDescriptionFiles storedPublicFiles) = true`.
`theProofLaid_zFull_returns`: the proof file's maker returns there. They are `theLive_zFull_of` and
`proofLaid_zFull` (Johnson/AtFull/Top/LiveAtZFull.lean) with their two premises shown: the layout
file has 224,975 bytes (`lay_size`, AtFullSide/Layout/Size.lean) and reads as the written value `LW`
(`layoutRead_full`, AtFullSide/LayoutRead/Full.lean).

What it is for. Three places at which the verifier rejects everything on the public files alone: the
test of the scope (`VerifierAndGoals.InScope`: whether they are files of which the goals speak), the test
`protocolDataWellFormed` (whether the three makers of its description return and their data fit the frame), and the
outer branches of the decision on the copy's file (`Desc.K15.linkDecisionAtParameterFile`). The third is settled
wherever the first passes (`Desc.K15.decWritten_inScope`,
Johnson/Goal/Conditions/EntryWrittenLaw.lean). These three are settled side by side in
AtFullSide/Top/ThreeTests.lean; they are not all: there are more, some settled and some not, and no
theorem says that any list of them is whole. The first passes at `storedPublicFiles` by
`VerifierAndGoals.inScope_full`. In scope, where `protocolDataWellFormed` says no, the verifier rejects every proof
(`VerifierAndGoals.theDescription_dead`, Johnson/Goal/Description/Dead.lean, with that file's limits), so that
a statement "whatever the verifier accepts is right" holds idly there. Here `protocolDataWellFormed` is shown to
say yes at the full-size files.

Why here. The two closed facts on the layout file are shown in this side library, which is built
with a larger thread stack than the files under lean/Johnson/. Nothing in the main library imports
this file, so only a build of the side library shows a break in it; no independent checker has
replayed it.

Limits. At `VerifierAndGoals.storedPublicFiles` alone. `VerifierAndGoals.storedPublicFiles` is three terms written in Ladder/Stored.lean: no
Lean code ties them to files in a folder of examples or to files that a program writes; the
example's weights are synthetic. At the second hash `OnBytes.secondHashFunction`, and at the constant `fixedConfigurationDigest`
in the digest's place, not at the digest of these files. Over the three makers' texts as they are,
the proof file's fourteen entry tests among them: a test more reopens it. Many closed facts beneath
are proved by evaluation in Lean's kernel (`decide +kernel`), and the two facts on the layout file
rest on `kernel_rfl` too (AtFullSide/Layout/Tie.lean, TieRfl.lean: one comparison of 224,975
characters): no compiled code, no axiom beyond Lean's three. A YES OF `protocolDataWellFormed` IS NO SIGN THAT THE
VERIFIER ACCEPTS ANY PROOF, and none that an honest prover's proof is accepted. Nothing on
soundness, on binding or on hiding is shown here.

-/
import Johnson.AtFull.Top.LiveAtZFull
import AtFullSide.Layout.Size
import AtFullSide.LayoutRead.Full

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Top

/-- **THE PROOF FILE's MAKER RETURNS AT THE THREE FILES OF `VerifierAndGoals.storedPublicFiles`.** No premise. -/
theorem theProofLaid_zFull_returns :
    ∃ P, FlashProve.theProofLaid (VerifierAndGoals.asDescriptionFiles VerifierAndGoals.storedPublicFiles) = .ok P :=
  _root_.AtFull.Top.proofLaid_zFull Johnson.Unfolds.Layout.lay_size
    Johnson.AtFull.LayoutRead.layoutRead_full

/-- **THE TEST `protocolDataWellFormed` ACCEPTS AT THE THREE FILES OF `VerifierAndGoals.storedPublicFiles`.** No premise. -/
theorem theLive_zFull : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles VerifierAndGoals.storedPublicFiles) = true :=
  _root_.AtFull.Top.theLive_zFull_of Johnson.Unfolds.Layout.lay_size
    Johnson.AtFull.LayoutRead.layoutRead_full

end AtFullSide.Top

#print axioms AtFullSide.Top.theProofLaid_zFull_returns
#print axioms AtFullSide.Top.theLive_zFull
