-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/ClaimsN.lean: A TEXT OF THE TYPE OF THE LETTER claims OF THE KIND
K11's LOT OF HALVES (`headMergeLot`, Honest/K11/Part.lean), GENERAL IN THE SIZE: WITH THE OUTPUT
HEAD's LINK AND TWO COUNTS OF ROUNDS AS ARGUMENTS; AND WITH THESE THREE FOUND OFF THE PUBLIC PART
AND THE GROUND. Three definitions with code. NOTHING IS STATED OR PROVED IN THIS FILE. `openHonest`
(Honest/OpenHonest.lean) lays `headClaimsByPlace` as the lot's claims, and E2E/K11AtTheTerm.lean and
AtFullSide/K11/LendsAtTheTerm.lean use it in `headMergeLot`; `headClaimsN` is called by kind K13's
`headArmOfSeg` (Honest/K13/PileOfAnySize.lean).

  `headFourN m n₀ n₁`      the four things that the claim reads of what the head heard: the text of
                           `headFourOfK6` (Honest/K11/ThreeTiesStatement.lean) at the key points
                           `keysAtLink m n₀` (KeysAtLink.lean of this folder). m: the head's link.
                           n₀: the rounds of the first chain in front of the lookup on that link's
                           calls. n₁: those in front of the head's own sub-protocol
  `headClaimsN m n₀ n₁`    the kind's own text of the asked claims (`headMergeClaims`, Claims.lean
                           of this folder) at these four
  `headClaimsByPlace Z G`  the same with the three found: m: the link at which the lot lays the
                           kind's sub-protocol (`K11.parOf Z G`) · the chain: the library's
                           `ProofFile.onlineFirstChainAt Z` · n₀, n₁: the frame's `roundsInFront`
                           (Honest/ForKinds.lean) in that chain's flat list at piece 3 (the kind K3)
                           and piece 4 (the kind K6) of link m; WHERE THE CHAIN IS REJECTED OR A
                           PLACE IS NOT FOUND: NO CLAIM, IN SILENCE. LAID BY `openHonest`

Why. The other text (`headClaimsAt`, Honest/K11/Plays/FrontClaimStatement.lean) is written at the
full size's numbers: link 24, numbers 340 and 341. A play at a smaller example has another chain.

Limits. DEFINITIONS ALONE. WHAT IS SHOWN OF THEM AT THE FULL SIZE, IN THE GOALS' SCOPE:
`headFourN_scope` and `headArmOfSeg_scope` (Honest/K13/PileOfAnySizeAt.lean): `headFourN` and the
text over `headClaimsN`, at the head's segment and the two counts, are the written ones; of
`headClaimsByPlace`: under the library's head, where the base returns, it is `headClaimsAt` at the
head's chain (`headClaimsByPlace_at_head`, Plays/ClaimsNIs.lean). AT ANOTHER SIZE NOTHING IS SHOWN
OF THEM: there they are code; no file of the library runs them. Pieces 3 and 4 are read off the
driver's list of a head's kinds
(`kindsBeforeBatching`, Johnson/Desc/First/Driver/Chain.lean). `ProofFile.onlineFirstChainAt` does not ask the two tests
that the maker of the IOP as written in Lean asks before: so `headClaimsByPlace` can hand out claims
where that maker rejects; it makes the whole chain: how often, only a run says; and the link that
`K11.parOf` gives is 0 at an empty ground. The limits of KeysAtLink.lean. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.KeysAtLink
import Johnson.Desc.ProofFile.Honest.K11.Claims
import Johnson.Desc.ProofFile.Honest.K6.Heard
import Johnson.Desc.Kinds.Head.AtZ
import Johnson.Desc.Kinds.Law.RowRides
import Johnson.Desc.ProofFile.LinkAt
import Johnson.Desc.ProofFile.Lot.K11

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.AtZ (rqAt)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open ProofFile.Honest.K6 (headTHr headRs headWin)

/-- **The four things that the claim reads of what the head heard.** m: the head's link. n₀: the
rounds of the first chain in front of the lookup on that link's calls. n₁: those in front of the
output head's own sub-protocol. -/
def headFourN (m n₀ n₁ : Nat) (Z : Pub) (G : Ground) : HeadHeardFour :=
  { keys := keysAtLink m n₀ Z G
    overPositions := headTHr (parOf G.W.hS (workOf G.W)) n₁
    overChannels := headRs (parOf G.W.hS (workOf G.W)) n₁
    checked := fun x => headWin (parOf G.W.hS (workOf G.W)) (rqAt Z x.pub)
      (OnBytes.Desc.Reply.tokOf x.asked) }

/-- **The claims, at the head's link and two counts of rounds.** -/
def headClaimsN (m n₀ n₁ : Nat) : Pub → Ground → Inst → List Fmt.Drawn → List WsClaim :=
  headMergeClaims (headFourN m n₀ n₁)

/-- **The claims, with the three found off the public part and the ground.** -/
def headClaimsByPlace (Z : Pub) (G : Ground) : Inst → List Fmt.Drawn → List WsClaim :=
  match onlineFirstChainAt Z with
  | .error _ => fun _ _ => []
  | .ok c =>
    match roundsInFront c.blocksInOrder ⟨1, some (_root_.K11.parOf Z G).link, 3, .K3⟩,
        roundsInFront c.blocksInOrder ⟨1, some (_root_.K11.parOf Z G).link, 4, .K6⟩ with
    | some n₀, some n₁ => headClaimsN (_root_.K11.parOf Z G).link n₀ n₁ Z G
    | _, _ => fun _ _ => []

end ProofFile.Honest.K11

#print axioms ProofFile.Honest.K11.headFourN
#print axioms ProofFile.Honest.K11.headClaimsN
#print axioms ProofFile.Honest.K11.headClaimsByPlace
