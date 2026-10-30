-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Top/LiveAtZFull.lean: the test `protocolDataWellFormed` (Johnson/Goal/Description/Live.lean) accepts
at `VerifierAndGoals.storedPublicFiles`, under two closed facts on the layout file.

`VerifierAndGoals.storedPublicFiles` is a set of three public files (parameter file, layout file, scale file) as
Ladder/Stored.lean spells them.

Why. Three places at which the verifier rejects everything on the public files alone: the test of
the scope (`VerifierAndGoals.InScope`: whether they are files of which the goals speak), the test `protocolDataWellFormed`
(whether the three makers of its description return and their data fit the frame), and the outer
branches of the decision on the copy's file (`Desc.K15.linkDecisionAtParameterFile`). The third is settled wherever
the first passes (`Desc.K15.decWritten_inScope`, Johnson/Goal/Conditions/EntryWrittenLaw.lean).
These three are settled side by side in AtFullSide/Top/ThreeTests.lean; they are not all that are
known: more have been found, some settled and some not, and no theorem says that any list of them is
whole. `storedPublicFiles` is in scope by `VerifierAndGoals.inScope_full` (Johnson/Goal/Files/ScopeExample.lean). In
scope, where `protocolDataWellFormed` says no, the verifier at the description's own parser rejects every proof, at
hash functions whose answers have 32 bytes (`VerifierAndGoals.theDescription_dead`,
Johnson/Goal/Description/Dead.lean); there a statement "whatever the verifier accepts is right"
holds idly. Statements on an honest prover ask that `protocolDataWellFormed` says yes. So its yes at the full-size
files is wanted as a theorem, not as the result of a run alone.

Main names.
* `proofLaid_zFull`: the proof file's maker `theProofLaid` returns. It is `proofLaid_zFull_at`
  (Johnson/AtFull/Top/ProofLaidWhole.lean) with all its premises paid but the two on the layout
  file: the public part and the planner's answer with their written parts (`publicOfO_zFull_all`,
  Johnson/AtFull/Public/AtX0All.lean; `madeAt_fields`, Johnson/AtFull/Made/MadeAtJoinD.lean); what
  the lookups' lot (the kind K3) reads of the public part (`readsX_zFull`,
  Johnson/AtFull/K3X/ReadsAtFull.lean); the lookups' three entry tests (`digEntry_zFull`,
  `readsEntry_zFull`, Johnson/AtFull/Entry/K3AtX0.lean; `headEntry_zFull`,
  Johnson/AtFull/Entry/K3HeadAtX0.lean).
* `theLive_zFull_of`: THE STATEMENT. By `theLive_of_two` (Johnson/AtFull/Top/LiveOfTwo.lean): in the
  goals' scope `protocolDataWellFormed` accepts where the key file's maker and the proof file's maker return. The
  key file's: `theKeyLaid_zFull` (Johnson/AtFull/Top/KeyLaidZFull.lean).

Limits.
* hsz and bL are premises here: the layout file has 224,975 bytes, and `layoutRead` returns the
  written value on it. Both are closed facts on a stored text. Their proofs lie in the side library,
  which is built with a larger stack: AtFullSide/Top/LiveAtFull.lean has the statement with no
  premise.
* At these three files alone.
* At the second hash function (`OnBytes.secondHashFunction`), and at the constant `fixedConfigurationDigest` in the digest's
  place, not at the digest of these files.
* What `protocolDataWellFormed` says hangs on what its three makers ask. The theorem stands over their texts as
  they are, the proof file's fourteen entry tests among them (`lawsAsk`,
  Johnson/Desc/Laid/ProofAsks.lean): a test more reopens it.
* `VerifierAndGoals.storedPublicFiles` is a term. No Lean ties it to files in a folder of examples or to files that a
  program writes, and the example's weights are synthetic (Ladder/Stored.lean's head).
* Much beneath rests on evaluations in Lean's kernel at written values; each file says which.
* A YES OF `protocolDataWellFormed` IS NO SIGN THAT THE VERIFIER ACCEPTS ANY PROOF, and none that an honest
  prover's proof is accepted. Nothing on soundness, on binding or on hiding is shown here.

-/
import Johnson.AtFull.Top.ProofLaidWhole
import Johnson.AtFull.K3X.ReadsAtFull
import Johnson.AtFull.Entry.K3HeadAtX0
import Johnson.AtFull.Top.KeyLaidZFull
import Johnson.AtFull.Top.LiveOfTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Top
open VerifiableInference.Desc.Key (fixedDigest_size)

/-- **The proof file's maker returns at `VerifierAndGoals.storedPublicFiles`**, under two closed facts on the layout
file. -/
theorem proofLaid_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (bL : OnBytes.Plan.layoutRead VerifierAndGoals.storedPublicFiles.lay = some Johnson.AtFull.LayoutRead.LW) :
    ∃ P, FlashProve.theProofLaid (VerifierAndGoals.asDescriptionFiles VerifierAndGoals.storedPublicFiles) = .ok P := by
  obtain ⟨X₀, hX, hG, hA, hV, ha, P, hc⟩ := Johnson.AtFull.Public.publicOfO_zFull_all hsz
  obtain ⟨m, hm, -, -, -, -, -, -, -, -, -, -, -, e1, hF, -⟩ :=
    Johnson.AtFull.Made.madeAt_fields P hG hA hV bL fixedDigest_size ha hc
  obtain ⟨_, _, _, h⟩ := proofLaid_zFull_at hsz bL hX hm hF e1
    (Johnson.AtFull.K3X.readsX_zFull hsz hX)
    (Johnson.AtFull.Entry.digEntry_zFull hsz bL hX hm rfl)
    (Johnson.AtFull.Entry.readsEntry_zFull hsz bL hX hm rfl)
    (Johnson.AtFull.Entry.headEntry_zFull hsz bL hX hm rfl)
  exact ⟨_, h⟩

/-- **The test `protocolDataWellFormed` accepts at `VerifierAndGoals.storedPublicFiles`**, under two closed facts on the layout file. -/
theorem theLive_zFull_of (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (bL : OnBytes.Plan.layoutRead VerifierAndGoals.storedPublicFiles.lay = some Johnson.AtFull.LayoutRead.LW) :
    FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles VerifierAndGoals.storedPublicFiles) = true := by
  obtain ⟨_, _, -, -, hK⟩ := Johnson.AtFull.Top.theKeyLaid_zFull hsz bL
  obtain ⟨_, hP⟩ := proofLaid_zFull hsz bL
  exact FlashProve.theLive_of_two VerifierAndGoals.storedPublicFiles VerifierAndGoals.inScope_full hK hP

end AtFull.Top

#print axioms AtFull.Top.proofLaid_zFull
#print axioms AtFull.Top.theLive_zFull_of
