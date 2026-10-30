-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/AtLinkThere.lean: under the library's hypothesis
`P5J.AtMgA` (Johnson/P5J/MgAtAll.lean) a member of the first chain's flat list stands at each of
the fifty borders in front of a lookup. One theorem; no definition.

Terms. Honest/K3/GLOSSARY.md. In this file: `borderOf l d` (Johnson/Desc/Sound/MgAt/K3Open.lean) is
the number of the border in front of link l's lookup, and `IM.k3Place l d` (Johnson/IMR/K3Seat.lean)
is that lookup's place, written out. The sort d is false for the lookup on the calls and true for
the lookup on the digits.

What is shown.
  `member_at_link`: at a link l below 25 and either sort d, the first chain's flat list has a member
    at the border `borderOf l d`, and that member's place is `IM.k3Place l d`.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA`.
  `hl`: the link's number is below 25.

How the proof goes. It calls `P5J.At.places_paid` (Johnson/P5J/PlacesPaid.lean) and `places_are_k3`
(Johnson/Desc/Sound/MgAt/K3Open.lean).

Users. Each main theorem of Honest/K3/Law/Thread/AtLink.lean speaks of whatever stands at such a
border; by `member_at_link` something stands there. The theorem is called in these files under
Honest/K3/Law/Thread/: CallsHeardFront.lean [not in this library], CallsHeardLink.lean,
DigitsHeardLink.lean, DigitsPointsAt.lean, HeadCallsTie.lean, KeepsThread.lean, LayersTieHead.lean.

Limits. At the full size alone: that limit comes with `P5J.AtMgA`. Whether the member's step accepts
anywhere is not spoken of. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound.MgAt (borderOf places_are_k3)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **A member stands at the border in front of a lookup**, and its place is `IM.k3Place l d`.
Conditional on the library's hypothesis `P5J.AtMgA` and on l < 25. -/
theorem member_at_link (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (d : Bool) : ∃ blk, cF.blocksInOrder[borderOf l d]? = some blk ∧ blk.place = IM.k3Place l d := by
  have hp : (cF.blocksInOrder.map (·.place))[borderOf l d]? = some (IM.k3Place l d) := by
    have e : cF.blocksInOrder.map (·.place) = P5J.At.ps := P5J.At.places_paid h.scope h.reads h.laid
    rw [e]
    exact places_are_k3 hl d
  rw [List.getElem?_map] at hp
  obtain ⟨blk, h1, h2⟩ := Option.map_eq_some_iff.1 hp
  exact ⟨blk, h1, h2⟩

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.member_at_link
