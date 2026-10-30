-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/FirstFillThree.lean: CONDITIONAL: WHICH PROVER's SIDE STANDS AT
THE PLACES OF THREE KINDS IN THE PROVER THAT onlineProverFromPublicFiles RETURNS AT THE FILLING widerFillAt: the next
token's (K7), the members' batching's (K13) and the lookups' (K3). Statements with their proofs:
each is wider_first_find (Honest/Thread/FirstFill.lean) at what the kind's own list holds at the
place. General in the three public files that onlineProverFromPublicFiles reads.

  k7_half_wider    CONDITIONAL: at ⟨1, some (A.G.built.size - 1), 1, .K7⟩: replyHalf …
                   (Honest/K7.lean)
  k13_half_wider   CONDITIONAL: at K13.k13Place (whereOf A.Z): K13.proverSideOfClaimCombination at the reader
                   I.weights A.Z and the filler O.pile A.Z A.G (Honest/K13/Part.lean)
  k3_half_wider    CONDITIONAL: at the place of a site s of A.Z: the seated row at that site, as the
                   lookups' list sets it (seatAt, Honest/K3/Law/Thread/HalfOfLot.lean), at the
                   reader I.weights A.Z and the request's reader K3.reqAt A.Z

The premises. h: onlineProverFromPublicFiles returns A at the filling · K: WiderKinds at A's public part and ground · in
k3_half_wider: hs: s is one of the public part's sites (K3.lookSites A.Z).

K7's list holds one side: read off its text; find_single (Honest/Thread/FindBasics.lean), called.
K13's: its authors' own k13Lot_find (Honest/K13/LotKind.lean), called. K3's: the lookups' own
theLot_find (Honest/K3/Law/Thread/SitesOnce.lean), called at the request's reader of the public
part: the filling's list theLotInst is theLot at that reader, by unfolding. Where a list's authors
have the like statement in a file of their own, theirs is the one to keep and this one to strike.

Whose. By the authors of the attention sub-protocol's (K5's) own rounds.

Limits. Conditional. Neither h nor K is proved here (on WiderKinds see
Honest/Thread/FirstFillKinds.lean). That a sub-protocol stands at one of these places is not said
here; nor that the public part has a site. The statements are about lists and places. No property of
a prover or a protocol is claimed.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstFill
import Johnson.Desc.ProofFile.Honest.Thread.FindBasics
import Johnson.Desc.ProofFile.Honest.K3.Law.LotKind
import Johnson.Desc.ProofFile.Honest.K13.LotKind
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SitesOnce

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstFill
open VerifiableInference.Desc (Place KindName)

variable {W₀ : Type} {I : WiderIn W₀} {o o' : SecondHashFunctionArgument} {S : OnBytes.HonestTrace.Sz} {O : OnlineProverArguments}
  {pol lay KL : ByteArray} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}

/-- **THE SIDE THAT IS FOUND AT THE NEXT TOKEN's PLACE.** CONDITIONAL: onlineProverFromPublicFiles returns A at the
filling; WiderKinds at A's public part and ground. -/
theorem k7_half_wider (h : onlineProverFromPublicFiles o' pol lay KL (widerFillAt I o S O) = .ok A)
    (K : WiderKinds I o S O A.Z A.G) :
    A.H.first.find? (fun g => g.place == ⟨1, some (A.G.built.size - 1), 1, .K7⟩) =
      some (replyHalf (A.G.built.size - 1) 1 A.G.W.hS.V) := by
  refine wider_first_find h K (q := (replyLot, .K7))
    (by unfold widerPairs; exact .tail _ (.tail _ (.head _))) rfl ?_
  exact find_single (replyHalf (A.G.built.size - 1) 1 A.G.W.hS.V)

/-- **THE SIDE THAT IS FOUND AT THE PLACE OF THE MEMBERS' BATCHING.** CONDITIONAL: onlineProverFromPublicFiles returns A
at the filling; WiderKinds at A's public part and ground. -/
theorem k13_half_wider (h : onlineProverFromPublicFiles o' pol lay KL (widerFillAt I o S O) = .ok A)
    (K : WiderKinds I o S O A.Z A.G) :
    A.H.first.find?
        (fun g => g.place == K13.k13Place (VerifiableInference.Desc.K13.whereOf A.Z)) =
      some (K13.proverSideOfClaimCombination (I.weights A.Z) (O.pile A.Z A.G)
        (VerifiableInference.Desc.K13.whereOf A.Z)) := by
  refine wider_first_find h K (q := (HLot.byPub I.weights (LongLots.plain o S O).k13, .K13))
    (by unfold widerPairs; exact .tail _ (.tail _ (.tail _ (.tail _ (.head _))))) rfl ?_
  exact K13.k13Lot_find (I.weights A.Z) O.pile A.Z A.G

/-- **THE SIDE THAT IS FOUND AT A LOOKUP's PLACE.** CONDITIONAL: onlineProverFromPublicFiles returns A at the filling;
WiderKinds at A's public part and ground; s is one of the public part's sites. -/
theorem k3_half_wider (h : onlineProverFromPublicFiles o' pol lay KL (widerFillAt I o S O) = .ok A)
    (K : WiderKinds I o S O A.Z A.G) {s : K3.Site} (hs : s ∈ K3.lookSites A.Z) :
    A.H.first.find? (fun g => g.place == s.at_.place) =
      some (K3.Law.AtThr.seatAt id (I.weights A.Z) (K3.reqAt A.Z) A.Z s) := by
  refine wider_first_find h K (q := (HLot.byPub I.weights (LongLots.plain o S O).k3, .K3))
    (by unfold widerPairs; exact .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _))))))
    (K3.Law.spot_of_site A.Z s hs).1 ?_
  exact K3.Law.AtThr.theLot_find id (I.weights A.Z) (K3.reqAt A.Z) A.Z A.G s hs

end ProofFile.Honest.FirstFill

#print axioms ProofFile.Honest.FirstFill.k7_half_wider
#print axioms ProofFile.Honest.FirstFill.k13_half_wider
#print axioms ProofFile.Honest.FirstFill.k3_half_wider
