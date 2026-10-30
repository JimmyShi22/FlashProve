-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/ClaimIsOfK3Statement.lean: `HeadClaimIs` AT THE BARE LIST, AT
BORDER 346, WITH NO TIE LEFT AMONG ITS PREMISES: the one tie that `HeadClaimIsOfKeysBare`
(ThreeTiesBareStatement.lean of this folder) left open, each call's key point along the fold, IS
PAID BY THE LOOKUPS' AUTHORS' `head_keys_tie` (Honest/K3/Law/Thread/HeadCallsTie.lean), at their
text `headKeysOfK3 cF` for the letter keys: A STATEMENT ALONE: a definition of a proposition.
NOTHING IS PROVED IN THIS FILE, and it is none of the library's goals: it is a lemma's statement.

  `HeadClaimIsOfK3`   the library's head · the maker's base Bs · the letter claims answers at the
                      link with the kind's own text of the asked claims, at the four things that the
                      output head's rounds heard, the key points by `headKeysOfK3 cF`: `HeadClaimIs
                      cF.blocksInOrder (fun x => ProofFile.startS Zp x.pub) 346 link claims (fun x => x.asked)`

Limits. A JOIN OF TWO LEMMAS: NOTHING NEW IS SHOWN BESIDE THEM. THREE PREMISES STAY: the head; the
base; and the one on the letter claims, which says what that letter is at the link: whoever lays
claims pays it, AT THAT TEXT: the premise has become narrower, not lighter. `HeadClaimIs` is a
sentence on every fold that returns: THAT A FOLD RETURNS IS SHOWN OF NO ROUNDS. THE BARE FORM ALONE
(cF.blocksInOrder): not the list with each block's test on the words laid in front. THIS LEMMA IS NO BETTER
THAN WHAT IT JOINS: the lookups' authors call their file a reading copy, no hand-in; by their word
it has been built over one seal and read by one reader of their own. Their text has been evaluated
at no data; where the list of sites has none at link 24 it falls back on a default shape in silence:
under the head that does not happen (their `head_calls_site_found`): so it is the meant text under
the head alone. The head is a premise, at the earlier hash, at the full size: no example of it is
shown here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.ThreeTiesBareStatement
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HeadCallsTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K13.Honest (SiteClaims HeadClaimIs roundsAhead)
open ProofFile.Honest.K3.Law.AtThr (headKeysOfK3)

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. -/
def HeadClaimIsOfK3 : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain S ProofFile.Cl) (xP : VerifiableInference.Desc.First.Look.Place)
    (Bs : ProofFile.PureBase) (link : Nat) (claims : SiteClaims Inst),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xP →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    (∀ x hd, claims link x hd = some (headMergeClaims
      (headFourOfK6 (headKeysOfK3 cF) (roundsAhead cF.blocksInOrder 341)) Zp Bs.G₀ x hd).toArray) →
    HeadClaimIs cF.blocksInOrder (fun x : Inst => ProofFile.startS Zp x.pub) 346 link claims
      (fun x => x.asked)

end ProofFile.Honest.K11
