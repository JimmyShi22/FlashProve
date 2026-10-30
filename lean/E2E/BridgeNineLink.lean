-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/BridgeNineLink.lean: `nineFit_link` proves `NineFit` (E2E/BridgeAccept.lean: the nine clauses of
`OnBytes.Prover.HonFit` that do not read the session's prover) from `KeyFive`, at three public files
Z, with the link's prover filled in. The second of the three honest provers is `linkProverAtFiles b Z`
(E2E/BridgePremWLink.lean), the explicit honest prover of the link, and there is no fall at the link
(`Falls`: a set of verifier randomness that is set aside on the acceptance side).
E2E/BridgeNineCut.lean cuts the nine clauses in two, at general parameters: `KeyFive`, the four on
the key file's prover and the one on the measure of the OOD seeds that are set aside, and
`LinkFour`, the four on the link's prover. `LinkFour` is proved here (`linkFour_any`); `KeyFive`
stays a hypothesis. So the link's clauses of the acceptance side (`HonFit`) are proved of the prover
of which E2E/BridgePremWLink.lean proves the link's clauses of the privacy side (`PremW`). All is
stated at the wiring of `lettersZ Z c₀ m₀`, at every digest c₀ and every list m₀ of further digests
(below: the pair), for public files that are in scope and at which the IOP's own test accepts.

  `nineFit_link`: `NineFit hT (linkProverAtFiles b Z) W FT (fun _ _ _ => ∅) Zs S Yes ζ pT 0` from
    `KeyFive hT W FT Zs S Yes ζ pT`, where W is the wiring `(lettersZ Z c₀ m₀).W`. Free parameters:
    the key file's prover hT and its falls FT, the OOD seeds Zs that are set aside, the OOD-seed
    wire S, the relation Yes, the bounds ζ and pT, and b. The bound for the link is 0
  `linkFour_any`: `LinkFour` at the wiring of every pair, at the bound 0, for any three provers Hs
    whose second is `linkProverAtFiles b Z` and any falls F that are empty at the link, at every Yes and Zs

That the acceptance side and the privacy side hold at one value of the three provers, with this
second prover, is stated in Lean in E2E/BridgeBothAtLink.lean, under that file's hypotheses.

By what. `linkFour_any` is one call of `OnBytes.LinkSim.AtHome.homeSide_accepted`
(Johnson/LinkSim/AtHome/HomeAccepted.lean), which calls the theorem on that prover's acceptance,
`linkFits_at` (Johnson/Goal/Conditions/LinkFitsAt.lean). `homeSide_accepted` is stated at one pair:
at the wiring of `homeR b Z` (Johnson/Goal/Conditions/HomeAtWider.lean), which by unfolding is the
wiring of the pair (`allZeroDigest`, []). `wiring_any` (E2E/BridgePremWLink.lean) carries it to every pair:
the four clauses read the wiring and no OOD-seed wire. `nineFit_link` is `nineFit_of`
(E2E/BridgeNineCut.lean) at k and at `linkFour_any`. That lemma is called at the three provers
`proversOf hT (linkProverAtFiles b Z) Fm` (E2E/BridgePrivacy.lean) and at the falls that `fallsOf`
(E2E/BridgeAccept.lean) builds from FT, no fall at the link, and FB; there h and hF hold by
unfolding. Definitions: `protocolAtFiles`, `lettersZ` (E2E/BridgeJoinAtFiles.lean); `filesAt`, `FullSizeMatrix`
(E2E/ObjectAtFiles.lean); `PadZ`, `pads_nonempty` (E2E/TiedAtFiles.lean); `Family`
(E2E/HonestFamily.lean); `FallB` (E2E/BridgeAccept.lean); `ThreeProvers`, `Falls`
(Johnson/Prover/All/OfHonest.lean); `AccLaw` (Johnson/Prover/Law/Defs.lean); `Honest`
(Iop/InteractiveOracleProof.lean); `InScope` (Ladder.lean); `protocolDataWellFormed` (Johnson/Goal/Description/Live.lean); `asDescriptionFiles`
(Johnson/Goal/Tie/ReadThruHead.lean); `allZeroDigest` (Johnson/Goal/Conditions/BindsAtThe.lean).

Hypotheses. Of both theorems. scope: Z is in scope (`InScope Z = true`). live: the IOP's own test on
the public files accepts (`protocolDataWellFormed (asDescriptionFiles Z) = true`). Of `linkFour_any`. h: the link's prover
`Hs.Lk` is `linkProverAtFiles b Z`. hF: `F.Lk` is empty at all arguments. Of `nineFit_link`. k: `KeyFive`.

Limits.
- The key file's four clauses and the bound ζ stay hypotheses (k). No value is shown here to meet
  `KeyFive`.
- Of the link's four clauses one has content: the clause on acceptance, `accL`. It is an `AccLaw`:
  it speaks of the interactive verifier, and only of runs in which all proof-of-work tests are
  passed. The clause on the external strings (`extL`) holds by unfolding. The other two (`whL`,
  `prL`) speak of an abort set that is empty at that term (`home_withheld`,
  Johnson/LinkSim/AtHome/TwoViews.lean).
- In `nineFit_link` the family Fm and its falls FB are parameters that the conclusion does not name:
  they only make up three provers, with their falls, for the call of `linkFour_any`.
- "At every pair" means: at each pair (c₀, m₀) that is fixed before the hash function is drawn.
- The limits of the head of Johnson/LinkSim/AtHome/HomeAccepted.lean hold here too: nothing on
  acceptance at public files that are out of scope or at which the test does not accept; that some
  public files pass both is not proved there (`open_zFull` and `open_zGap`,
  AtFullSide/E2E/AtWrittenFiles.lean, prove it of the library's two named sets); the four clauses
  are not all of `HonFit`; nothing on soundness. So do the limits of E2E/BridgePremWLink.lean.
- `accL` is a statement on the link's interactive protocol, as said above. It is not the library's
  completeness of a protocol (`Honest.Acc`, Iop/InteractiveOracleProof.lean), which is not claimed of this prover
  (the docstring of `linkRec`, Johnson/Prover/Link/LinkFrame.lean). Beyond that, nothing on
  completeness, soundness or hiding follows from this file alone.
-/

import E2E.BridgePremWLink
import E2E.BridgeNineCut
import Johnson.LinkSim.AtHome.HomeAccepted

set_option autoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace AtPublicFiles.AtFiles
open Iop Prob Hiop AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed
open OnBytes.Slice (frS)
open LPFD.Full (XF)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed allZeroDigest)
open OnBytes.Prover (ThreeProvers Falls)
open OnBytes.LinkSim.AtHome (homeSide_accepted)

/- Among all that this file imports, the search for this instance runs out of its budget. It is a
proposition, so whichever proof is found, the statements below are the same. -/
local instance (priority := high) : Nonempty PadZ := pads_nonempty frS 402653181

variable (c₀ : VerifiableInference.Digest) (m₀ : List (Iop.Dig 256)) (b : PublicFiles → ℕ) (Z : PublicFiles)

/-- **The link's four clauses (`LinkFour`), at the wiring of every pair (c₀, m₀) and at the bound 0,
for any three provers whose second is `linkProverAtFiles b Z`, with no fall at the link.** Hs and F are
variables, and h and hF are equations on their fields `Lk`, so that Lean has no value to unfold. -/
theorem linkFour_any (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (Hs : ThreeProvers (protocolAtFiles Z)) (F : Falls Hs) (h : Hs.Lk = linkProverAtFiles b Z) (hF : ∀ w x c, F.Lk w x c = ∅)
    (Yes : FullSizeMatrix → XF → Prop) (Zs : FullSizeMatrix → (protocolAtFiles Z).EncodingRandomness → Set (protocolAtFiles Z).OutOfDomainSeed) :
    LinkFour (aT := (filesAt Z).annT) Hs.Lk (lettersZ Z c₀ m₀).W F.Lk Zs Yes 0 :=
  have h4 := homeSide_accepted b Z scope live Hs F Yes Zs h hF
  have h0 : LinkFour (aT := (filesAt Z).annT) Hs.Lk (lettersZ Z allZeroDigest []).W F.Lk Zs Yes 0 :=
    ⟨h4.1, h4.2.1, h4.2.2.1, h4.2.2.2⟩
  (congrArg (fun W' => LinkFour (aT := (filesAt Z).annT) Hs.Lk W' F.Lk Zs Yes 0)
    (wiring_any Z allZeroDigest [] c₀ m₀)).mp h0

/-- **The nine clauses (`NineFit`) from `KeyFive`: the link's four are proved.** -/
theorem nineFit_link (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hT : Honest (protocolAtFiles Z).offline (FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed))
    (Fm : Family (protocolAtFiles Z).onlineBatch.loc (FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed)) (FB : FallB Fm)
    (FT : FullSizeMatrix × (protocolAtFiles Z).EncodingRandomness × (protocolAtFiles Z).OutOfDomainSeed → (protocolAtFiles Z).Rec → hT.Coin → Set (Rho (protocolAtFiles Z).offline.shape))
    (Zs : FullSizeMatrix → (protocolAtFiles Z).EncodingRandomness → Set (protocolAtFiles Z).OutOfDomainSeed) {S} {Yes : FullSizeMatrix → XF → Prop} {ζ pT : ℝ≥0∞}
    (k : KeyFive hT (lettersZ Z c₀ m₀).W FT Zs S Yes ζ pT) :
    NineFit hT (linkProverAtFiles b Z) (lettersZ Z c₀ m₀).W FT (fun _ _ _ => ∅) Zs S Yes ζ pT 0 :=
  nineFit_of k
    (linkFour_any c₀ m₀ b Z scope live (proversOf hT (linkProverAtFiles b Z) Fm)
      (fallsOf hT (linkProverAtFiles b Z) Fm FT (fun _ _ _ => ∅) FB) rfl (fun _ _ _ => rfl) Yes Zs)

end AtPublicFiles.AtFiles

#print axioms AtPublicFiles.AtFiles.linkFour_any
#print axioms AtPublicFiles.AtFiles.nineFit_link
