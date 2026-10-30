-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/AtWrittenFiles.lean

What this file has. open_zFull and open_zGap prove that the library's two named sets of public files
are in scope with a live description. These are VerifierAndGoals.storedPublicFiles, the stored full-size example, and
VerifierAndGoals.zGap, the same files with another acceptance policy. The theorems of this group on index
privacy after hashing assume one or both of these premises, and would be vacuous if no public files
met them. Here each is restated at the two sets, with no premise left on the public files. So none
of them is vacuous for want of public files. The first, privacyWithNumber_zFull, is index privacy of
the hashed scheme with placeholder provers: error at most 2 ^ -135 (one request, 2 ^ 64 oracle
queries), with proofs produced under the same search limits. That last is keyInGame_zFull and
sessionsInGame_zFull: the proofs in the view of the real experiment are produced, except with the
small probabilities stated in E2E/StringsInGame.lean and E2E/SessionsInGame.lean. By keyHolds_zFull
and sessionHolds_zFull, for any three provers, a produced proof for the first table or for a session
opens at least one column of the encoder's table of the index. It opens at most 62 or 64 positions
(E2E/StringsHoldClosed.lean). Last, allAtOnce_zFull has the eight clauses of
E2E/StringsOpenInGame.lean for one choice of parameters. The same six hold at VerifierAndGoals.zGap.

Where this stands (in full: E2E/ZetaAtCaps.lean): the step through hashing is proved for any provers
that meet twenty premises, here with an error bound; all three provers here are placeholders.

The index: in the release's use, the model's weights (Terms: E2E/HidingTerms.lean).

Theorems, each at the verifier's parameters at `VerifierAndGoals.storedPublicFiles` and at `VerifierAndGoals.zGap`
(Ladder/Stored.lean).
  `open_zFull`, `open_zGap`: the files are in scope with a live description.
  `privacyWithNumber_zFull`, `privacyWithNumber_zGap`: `PrivacyWithNumber` (E2E/ZetaAtCaps.lean).
  `keyHolds_zFull`, `keyHolds_zGap`, `sessionHolds_zFull`, `sessionHolds_zGap`: `KeyHolds` and
    `SessionHolds` (E2E/StringsHoldClosed.lean).
  `keyInGame_zFull`, `keyInGame_zGap`, `sessionsInGame_zFull`, `sessionsInGame_zGap`: `KeyInGame`
    (E2E/StringsInGame.lean) and `SessionsInGame` (E2E/SessionsInGame.lean). These four use only
    that the files are in scope.
  `allAtOnce_zFull`, `allAtOnce_zGap`: `AllAtOnce` (E2E/StringsOpenInGame.lean); its first two
    clauses are `PrivacyWithNumber`.

Limits, the weightiest first.
- In the results on index privacy and on the real experiment the three provers are placeholders,
  which send fixed messages and not the protocol's (silentAtC, E2E/FiveLeftSilentCaps.lean).
- VerifierAndGoals.storedPublicFiles and VerifierAndGoals.zGap are terms written in this library; no theorem ties them to any file
  on a disk.
- The digest c and the second public reading m stay fixed parameters: they are not proved to be
  those that VerifierAndGoals.verify computes from these files.
- That the description is live at them is proved in the side library lean/AtFullSide/
  (theLive_zFull, theLive_zGap).
- Each theorem keeps all the limits of the file that it comes from: restating it here adds only that
  its premises on the public files are met at two values.
- Nothing here bears on completeness or on soundness, and on what is hidden nothing beyond the
  statements that are restated.

Tests and notes.
- That the files are in scope is `VerifierAndGoals.filesRead` (Johnson/Goal/Files/FilesReadProof.lean).

Terms: E2E/HidingTerms.lean.

This file lies in the side library AtFullSide, which is built with a larger thread stack
(lake build AtFullSide).


-/
import E2E.StringsOpenInGame
import E2E.StringsHoldClosed
import E2E.ZetaAtCaps
import AtFullSide.Top.LiveAtPolicies

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtPublicFiles.AtWritten
open VerifierAndGoals (InScope asDescriptionFiles storedPublicFiles zGap)
open FlashProve (protocolDataWellFormed)
open AtPublicFiles.Shown AtPublicFiles.ZetaAt

/-- The stored full-size files are in scope with a live description. -/
theorem open_zFull : InScope storedPublicFiles = true ∧ protocolDataWellFormed (asDescriptionFiles storedPublicFiles) = true :=
  ⟨VerifierAndGoals.filesRead.full.1, AtFullSide.Top.theLive_zFull⟩

/-- The same files with the other acceptance policy. -/
theorem open_zGap : InScope zGap = true ∧ protocolDataWellFormed (asDescriptionFiles zGap) = true :=
  ⟨VerifierAndGoals.filesRead.other.1, AtFullSide.Top.theLive_zGap⟩

variable (c : VerifiableInference.Digest) (m : (VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).More)

/-! ## At storedPublicFiles -/

theorem allAtOnce_zFull : AllAtOnce ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input storedPublicFiles c m) :=
  allAtOnce_description storedPublicFiles open_zFull.1 open_zFull.2 c m

theorem privacyWithNumber_zFull :
    PrivacyWithNumber ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input storedPublicFiles c m) :=
  privacyWithNumber_description storedPublicFiles open_zFull.1 open_zFull.2 c m

theorem keyHolds_zFull : KeyHolds ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input storedPublicFiles c m) :=
  keyHolds_description storedPublicFiles open_zFull.1 open_zFull.2 c m

theorem sessionHolds_zFull :
    SessionHolds ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input storedPublicFiles c m) :=
  sessionHolds_description storedPublicFiles open_zFull.1 open_zFull.2 c m

theorem keyInGame_zFull : KeyInGame ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input storedPublicFiles c m) :=
  keyInGame_description storedPublicFiles open_zFull.1 c m

theorem sessionsInGame_zFull :
    SessionsInGame ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input storedPublicFiles c m) :=
  sessionsInGame_description storedPublicFiles open_zFull.1 c m

/-! ## At zGap -/

theorem allAtOnce_zGap : AllAtOnce ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input zGap c m) :=
  allAtOnce_description zGap open_zGap.1 open_zGap.2 c m

theorem privacyWithNumber_zGap :
    PrivacyWithNumber ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input zGap c m) :=
  privacyWithNumber_description zGap open_zGap.1 open_zGap.2 c m

theorem keyHolds_zGap : KeyHolds ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input zGap c m) :=
  keyHolds_description zGap open_zGap.1 open_zGap.2 c m

theorem sessionHolds_zGap :
    SessionHolds ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input zGap c m) :=
  sessionHolds_description zGap open_zGap.1 open_zGap.2 c m

theorem keyInGame_zGap : KeyInGame ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input zGap c m) :=
  keyInGame_description zGap open_zGap.1 c m

theorem sessionsInGame_zGap :
    SessionsInGame ((VerifierAndGoals.atSecondHashFunction VerifierAndGoals.theDescription).input zGap c m) :=
  sessionsInGame_description zGap open_zGap.1 c m

end AtPublicFiles.AtWritten

/- Each command below is expected to print a subset of [propext, Classical.choice, Quot.sound]. -/
#print axioms AtPublicFiles.AtWritten.open_zFull
#print axioms AtPublicFiles.AtWritten.open_zGap
#print axioms AtPublicFiles.AtWritten.allAtOnce_zFull
#print axioms AtPublicFiles.AtWritten.privacyWithNumber_zFull
#print axioms AtPublicFiles.AtWritten.keyHolds_zFull
#print axioms AtPublicFiles.AtWritten.sessionHolds_zFull
#print axioms AtPublicFiles.AtWritten.keyInGame_zFull
#print axioms AtPublicFiles.AtWritten.sessionsInGame_zFull
#print axioms AtPublicFiles.AtWritten.allAtOnce_zGap
#print axioms AtPublicFiles.AtWritten.privacyWithNumber_zGap
#print axioms AtPublicFiles.AtWritten.keyHolds_zGap
#print axioms AtPublicFiles.AtWritten.sessionHolds_zGap
#print axioms AtPublicFiles.AtWritten.keyInGame_zGap
#print axioms AtPublicFiles.AtWritten.sessionsInGame_zGap
