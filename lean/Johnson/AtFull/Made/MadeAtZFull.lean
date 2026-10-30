-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/MadeAtZFull.lean: `Key.madeAt` returns at the three full-size public files as
Ladder/Stored.lean spells them (`VerifierAndGoals.storedPublicFiles`), at the constant digest `Key.fixedDigest`.

What it says. `madeAt_zFull`: under
  hsz   the stored layout file has 224,975 bytes, and
  b₁    it reads as the written value `LW`,
there is a public part X₀ that `publicOfO` returns at the three stored files (at the second hash
function `OnBytes.secondHashFunction`), and `Key.madeAt X₀ storedPublicFiles.lay Key.fixedDigest` returns, with its value
said: the chains of the written sizes and plans, the built segments, and the written sendings. What
the steps behind ask of the same X₀ stands beside: `PubFull`, the arms' test, the range checks.

How. `publicOfO_zFull_all` (Johnson/AtFull/Public/AtX0All.lean) hands six of `madeAt_at_full`'s
eight hypotheses at one X₀ (Johnson/AtFull/Made/MadeAtJoinD.lean); the digest's 32 bytes are
`Key.fixedDigest_size` (Johnson/Desc/Key/SlotIs.lean); b₁ stays a premise.

Limits. hsz and b₁ are premises: closed facts on the stored layout file, shown in a side library
that is built with a larger thread stack: one constant beneath them, `lay_chars`
(AtFullSide/Layout/TieRfl.lean), was seen to fail in Lean's kernel at the default stack. hsz is
`lay_size` (AtFullSide/Layout/Size.lean), b₁ is `layoutRead_full` (AtFullSide/LayoutRead/Full.lean).
AT THE CONSTANT DIGEST OF 32 BYTES 0x01, NOT AT THE DIGEST OF THESE FILES: for every digest of 32
bytes, and so for the files' own, see Johnson/AtFull/Made/PlannedZFull.lean. `VerifierAndGoals.storedPublicFiles` is three
terms written in Ladder/Stored.lean: no Lean code ties them to the top-level folder examples/; the
example's weights are synthetic. It is a step toward an example of the head; no example of the head
is shown in this file; two, at storedPublicFiles and at zGap alone, are AtFullSide.Top.headMember_zFull and
headMember_zGap, whose own Limits say what they are worth. Nothing on soundness.
-/
import Johnson.AtFull.Made.MadeAtJoinD
import Johnson.AtFull.Public.AtX0All
import Johnson.Desc.Key.SlotIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages OnBytes.Params
open VerifiableInference.PlanWritten (FirstWritten MadeWritten publicOfO)
open VerifiableInference.Desc.Key (fixedDigest fixedDigest_size)
open Johnson.G (keySendsFull proofSendsFull)
open Johnson.AtFull.LayoutRead (LW)
open VerifiableInference.Desc.LinkJoin (armsB)

/-- **`Key.madeAt` RETURNS AT THE THREE FILES OF `VerifierAndGoals.storedPublicFiles`**, at the constant digest
`fixedDigest` (not the digest of these files), under two closed facts on the layout file. -/
theorem madeAt_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (b₁ : Plan.layoutRead VerifierAndGoals.storedPublicFiles.lay = some LW) :
    ∃ (X₀ : Public) (links₀ links : Array LinkH) (sh : Plan.Shape),
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      VerifiableInference.Desc.Key.madeAt X₀ VerifierAndGoals.storedPublicFiles.lay fixedDigest =
        .ok ⟨{ X := X₀, cfg := fixedDigest, chains := chainsAt (xOf X₀ sh checksFull) fixedDigest,
               built := { links := links } },
             (keySendsFull.1, keySendsFull.2.1, keySendsFull.2.2),
             (proofSendsFull.1, proofSendsFull.2.1, proofSendsFull.2.2)⟩ ∧
      linksOf X₀ default = .ok links₀ ∧
      declareLinks links₀ X₀.NGr X₀.p4 = .ok (links, declaredFull) ∧
      links.toList.map viewOf = viewFull ∧
      Plan.shapeOfLayout X₀.layers.wsLay X₀.layers.wsLay.lk = some sh ∧
      shapesOf X₀ (some VerifierAndGoals.storedPublicFiles.lay) = .ok (links, xOf X₀ sh checksFull) ∧
      FirstWritten (chainsAt (xOf X₀ sh checksFull) fixedDigest).proof.first ∧
      MadeWritten (chainsAt (xOf X₀ sh checksFull) fixedDigest).made ∧
      H2K.Sizes.PubFull X₀ ∧ armsB X₀ = true ∧ rangeChecksOf X₀ = some checksFull := by
  obtain ⟨X₀, hX, hG, hA, hV, ha, P, hc⟩ := Johnson.AtFull.Public.publicOfO_zFull_all hsz
  obtain ⟨links₀, links, sh, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    madeAt_at_full P hG hA hV b₁ fixedDigest_size ha hc
  exact ⟨X₀, links₀, links, sh, hX, h1, h2, h3, h4, h5, h6, h7, h8, P, ha, hc⟩

#print axioms Johnson.AtFull.Made.madeAt_zFull

end Johnson.AtFull.Made
