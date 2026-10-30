-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Top/WrittenAtZFull.lean: at `VerifierAndGoals.storedPublicFiles` the data that the verifier's description
holds for the key file and for the proof file are the written data, under two closed facts on the
layout file.

Why. `written_or_no_all` (Johnson/Goal/Description/KeyWritten.lean) says, at all public files in the
goals' scope: the verifier rejects everything, or both files' data are the written data. This file
shows the second arm at `storedPublicFiles`, at the second hash function.

Main name.
* `written_zFull_of`: the second arm of `written_or_no_all` to the letter, at `OnBytes.secondHashFunction` and
  `storedPublicFiles`. Two calls: `key_written_of_liveAt` and `proof_written_of_liveAt` (the same file), at
  `VerifierAndGoals.inScope_full` and at the yes of the test `protocolDataWellFormed` (`theLive_zFull_of`,
  Johnson/AtFull/Top/LiveAtZFull.lean).

Limits.
* hsz and bL are premises here: the layout file has 224,975 bytes, and `layoutRead` returns the
  written value on it. AtFullSide/Top/WrittenAtFull.lean has the statement with no premise.
* THE TWO ARMS DO NOT EXCLUDE EACH OTHER. That the second holds does not show that the first fails:
  that the verifier accepts any proof is shown nowhere.
* "Data" are, for each file, the stored table's depth, the three chains' lists of rounds and three
  functions on numbers (`OnBytes.Maker.WholeD`, OnBytes/Maker/Whole.lean): the shape of the
  interaction. Not the bytes of a key file or of a proof file, and not weights.
* Every limit of Johnson/AtFull/Top/LiveAtZFull.lean holds here: these three files alone; the
  second hash function; a constant in the digest's place; the makers' texts as they are;
  `VerifierAndGoals.storedPublicFiles` is a term that no Lean ties to files in a folder.
* Nothing on soundness, on binding or on hiding is shown here.

-/
import Johnson.AtFull.Top.LiveAtZFull
import Johnson.Goal.Description.KeyWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Top

/-- **At `VerifierAndGoals.storedPublicFiles` both files' data are the written data**: the second arm of
`written_or_no_all`, under two closed facts on the layout file. -/
theorem written_zFull_of (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (bL : OnBytes.Plan.layoutRead VerifierAndGoals.storedPublicFiles.lay = some Johnson.AtFull.LayoutRead.LW) :
    FlashProve.theKeyDataAt OnBytes.secondHashFunction (VerifierAndGoals.asDescriptionFiles VerifierAndGoals.storedPublicFiles) = Johnson.G.writtenKFull ∧
      FlashProve.theProofDataAt OnBytes.secondHashFunction (VerifierAndGoals.asDescriptionFiles VerifierAndGoals.storedPublicFiles) =
        Johnson.G.writtenPFull :=
  ⟨FlashProve.key_written_of_liveAt OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles VerifierAndGoals.inScope_full
      (theLive_zFull_of hsz bL),
    FlashProve.proof_written_of_liveAt OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles VerifierAndGoals.inScope_full
      (theLive_zFull_of hsz bL)⟩

end AtFull.Top

#print axioms AtFull.Top.written_zFull_of
