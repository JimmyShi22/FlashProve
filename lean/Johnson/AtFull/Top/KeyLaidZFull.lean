-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/AtFull/Top/KeyLaidZFull.lean: the key file's maker returns at the three full-size public
files as Ladder/Stored.lean spells them (`VerifierAndGoals.storedPublicFiles`).

What it says. `theKeyLaid_zFull`: under hsz (the stored layout file has 224,975 bytes) and b₁ (it
reads as the written value `LW`), `FlashProve.theKeyLaid (asDescriptionFiles storedPublicFiles)` returns the written key
file's description `writtenKFull`, with a run that is named from m, where m is what `Key.madeAt`
returns at the public part X₀ that `publicOfO` returns: both returns stand in the statement.

How. Three returns inside it (`keyLaid_of_parts`, Johnson/AtFull/Top/OnePlanner.lean): the public
part and `Key.madeAt`'s value: `madeAt_zFull` (Johnson/AtFull/Made/MadeAtZFull.lean); the key file's
back: `keyBack_at_fixed_of_shapes` (Johnson/AtFull/KeyBack/KeyBackOfShapes.lean) at the
join's shapes, its three equations by `proofSized_join`, `first_of_arms`, `layout_join`.

Limits. hsz and b₁ are premises; they are shown in the side library: `lay_size`
(lean/AtFullSide/Layout/Size.lean), `layoutRead_full` (lean/AtFullSide/LayoutRead/Full.lean).
`VerifierAndGoals.storedPublicFiles` is three terms written in Ladder/Stored.lean: no Lean code ties them to the top-level
folder examples/; the example's weights are synthetic. At the second hash function `OnBytes.secondHashFunction`,
a fixed function, and at the constant `fixedConfigurationDigest` in the digest's place, not at the digest of these
files. It is one of the two returns from which `protocolDataWellFormed` accepts in scope (`theLive_of_two`,
Johnson/AtFull/Top/LiveOfTwo.lean), and so a step toward an example of the head, that is, of files
in scope at which `protocolDataWellFormed` accepts: THE PROOF FILE's MAKER IS NOT SHOWN TO RETURN IN THIS FILE: no
example of the head is shown in this file; two, at storedPublicFiles and at zGap alone, are
AtFullSide.Top.headMember_zFull and headMember_zGap,
whose own Limits say what they are worth. Nothing on soundness.
-/
import Johnson.AtFull.Made.MadeAtZFull
import Johnson.AtFull.Made.MadeAtJoinS
import Johnson.AtFull.KeyBack.KeyBackOfShapes
import Johnson.AtFull.Top.OnePlanner

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Top
open OnBytes OnBytes.Model OnBytes.Model.Verify
open Johnson.AtFull.Made
open Johnson.AtFull.LayoutRead (LW)
open VerifiableInference.Desc

/-- **THE KEY FILE's MAKER RETURNS AT THE THREE FILES OF `VerifierAndGoals.storedPublicFiles`**, under two closed facts on
the layout file. -/
theorem theKeyLaid_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (b₁ : Plan.layoutRead VerifierAndGoals.storedPublicFiles.lay = some LW) :
    ∃ X₀ m,
      VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL
        (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      Key.madeAt X₀ VerifierAndGoals.storedPublicFiles.lay Key.fixedDigest = .ok m ∧
      FlashProve.theKeyLaid (VerifierAndGoals.asDescriptionFiles VerifierAndGoals.storedPublicFiles) =
        .ok (Johnson.G.writtenKFull,
          ((Key.descriptionFromSource (Johnson.AtFull.KeyBack.sourceKFull m) Johnson.KB8.rangesNumsFull
            Johnson.KB8.laterPlacesFull).pull Key.keyInstanceOfOutOfDomainSample).run) := by
  obtain ⟨X₀, _, links, sh, hX, hm, -, -, -, -, hs, -, -, P, ha, hc⟩ := madeAt_zFull hsz b₁
  have hK := FlashProve.keyLaid_of_parts hX hm
    (Johnson.AtFull.KeyBack.keyBack_at_fixed_of_shapes VerifierAndGoals.inScope_full hX hm hs
      (proofSized_join P sh checksFull) (first_of_arms P hc ha) (layout_join X₀ sh checksFull))
  exact ⟨X₀, _, hX, hm, hK⟩

#print axioms Johnson.AtFull.Top.theKeyLaid_zFull

end Johnson.AtFull.Top
