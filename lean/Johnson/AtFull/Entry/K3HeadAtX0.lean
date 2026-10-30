-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/K3HeadAtX0.lean: row 13 of the proof file's entry tests (`K3Asks.headEntry`,
Johnson/Desc/First/Look/K3AsksDoor.lean) says yes at the three full-size public files as
Ladder/Stored.lean spells them (`VerifierAndGoals.storedPublicFiles`). One statement: a call. Under the two closed facts
on the layout file that `madeAt_zFull` (Johnson/AtFull/Made/MadeAtZFull.lean) takes.
  **`headEntry_zFull`** (k₃): `headEntry_zFull_of` (K3AtX0.lean) with its two equations on the
    head's lookup paid: the six calls, their tables stripped, are `callsHead` (`head_calls_zFull`),
    and the numbers of padding keys are `pubHead` (`head_pub_zFull`):
    Johnson/AtFull/K3X/HeadForEntry.lean.
Limits. Those of K3AtX0.lean: UNDER hsz AND b₁, WHICH ARE NOT PAID HERE; at `VerifierAndGoals.storedPublicFiles` alone; a
yes of a test on public data: no proof is read, and nothing is accepted. Nothing on soundness, on a
binding of the commitment (the opening form, `BindsWith`), on correctness of extraction, on
completeness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.AtFull.Entry.K3AtX0
import Johnson.AtFull.K3X.HeadForEntry

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Entry
open OnBytes OnBytes.Model OnBytes.Model.Verify
open VerifiableInference.PlanWritten (publicOfO)
open VerifiableInference.Desc.Key (madeAt fixedDigest)
open VerifiableInference.Desc.K3Asks
open Johnson.AtFull.LayoutRead (LW)

/-- **k₃: the entry test on the output head's calls says yes.** -/
theorem headEntry_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (b₁ : Plan.layoutRead VerifierAndGoals.storedPublicFiles.lay = some LW) {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) {m : Johnson.G.OfPlan.Made} (hm : madeAt X₀ VerifierAndGoals.storedPublicFiles.lay fixedDigest = .ok m)
    {Zp : ProofFile.Pub} (hZ : Zp.made = ProofFile.Law.blankM m) : headEntry Zp = true :=
  headEntry_zFull_of hsz b₁ hX hm hZ (Johnson.AtFull.K3X.head_calls_zFull hsz hX)
    (Johnson.AtFull.K3X.head_pub_zFull hsz hX)

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.headEntry_zFull
