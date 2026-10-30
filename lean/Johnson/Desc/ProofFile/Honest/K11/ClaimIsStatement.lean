-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K11/ClaimIsStatement.lean: THE LAW ON THE HEAD's CLAIM IN THE FORM IN
WHICH THE PILE's FILLER TAKES IT AS A PREMISE (`HeadClaimIs`,
Johnson/Desc/K13/Honest/ClaimsIsAt.lean), AT THE FIRST CHAIN's OWN LIST UNDER THE LIBRARY's ONE
HYPOTHESIS, FROM THE FOUR TIES ALONG THAT LIST's FOLD: A STATEMENT ALONE: a definition of a
proposition. NOTHING IS PROVED IN THIS FILE, and it is none of the library's goals: it is a lemma's
statement.

  `HeadClaimIsAtHead`   under the library's one hypothesis at the full size; Bs: what the maker's
                        base returns; link, claims: the filler's letters. WHERE the parameter's arm
                        at link is the honest side's text as an array (`headMergeClaims`,
                        Claims.lean of this folder, at the hypothesis's public part and Bs's
                        ground); and THE FOUR TIES (`FourTies`, ClaimOfQuietStatement.lean of this
                        folder) hold at every state without a mark, with the asked reply heard, that
                        the fold over the first 346 sub-protocols returns, AT THE LIST OF WHAT THE
                        ROUNDS IN FRONT DREW: `HeadClaimIs` holds at that list of sub-protocols, the
                        description's first state at the instance's public half, number 346, and the
                        instance's asked reply

THE LIST IS THE FIRST CHAIN's FLAT LIST WITH EACH SUB-PROTOCOL BEHIND THE TEST THAT EVERY WORD SHOWN
IS BELOW THE PRIME (`Sound.below`, Johnson/Desc/Sound/ChainRule.lean; by that file's own words "a
device of the proof: it is no text of the description and runs nowhere"): IT IS NOT THE LIST THAT
RUNS. The library's "reached" (`RchAt`, Johnson/Top/H0/Walk/ReachAt.lean) is said of that list, and
its condition on the state in front of the merge leans on that test. AT THE BARE LIST NOTHING IS
SAID. Near, for whoever must cross back: the library's equation of the two at the whole verdict
(`FoldBelow`, ChainRule.lean; its proof: Johnson/Desc/Sound/FoldBelowProof.lean): the text that runs
makes the test on all that is shown once, then folds the bare list.

The premise on the filler's letter lays the text's list as an array: where the text yields no claim
(the asked token is no entry of the vocabulary; `weightsClaim` refuses) that arm is the empty array,
never nothing: `HeadClaimIs` does not look there.

Limits. THE FOUR TIES ARE A PREMISE: nothing here says what the output head's own block lays into
what the head heard, and the four parameters of Claims.lean stay open. The hypothesis is a premise;
it stands at the earlier hash. That a fold returns anywhere is not said. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.ClaimAskedStatement
import Johnson.Desc.K13.Honest.ClaimsIsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open VerifiableInference.Desc (Chain foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (below)
open VerifiableInference.Desc.K13.Honest (SiteClaims HeadClaimIs roundsAhead)

/-- The statement. Not proved here; a lemma's statement, none of the library's goals. -/
def HeadClaimIsAtHead : Prop :=
  ∀ (H : Pub → Ground → HeadHeardFour) (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD)
    (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain S ProofFile.Cl)
    (xP : VerifiableInference.Desc.First.Look.Place) (Bs : ProofFile.PureBase) (link : Nat)
    (claims : SiteClaims Inst),
    P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xP →
    ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs →
    (∀ x hd, claims link x hd = some (headMergeClaims H Zp Bs.G₀ x hd).toArray) →
    (∀ (x : Inst) rs cols sj c,
      foldBlocks 0 ((cF.blocksInOrder.map below).take 346) (ProofFile.startS Zp x.pub) rs cols =
        .ok (sj, rs.drop (roundsAhead (cF.blocksInOrder.map below) 346), c) →
      sj.failed = none → sj.out.reply = some x.asked →
      FourTies (H Zp Bs.G₀) x
        ((rs.take (roundsAhead (cF.blocksInOrder.map below) 346)).map (·.drawn)) sj) →
    HeadClaimIs (cF.blocksInOrder.map below) (fun x : Inst => ProofFile.startS Zp x.pub) 346 link claims
      (fun x => x.asked)

end ProofFile.Honest.K11

#print axioms ProofFile.Honest.K11.HeadClaimIsAtHead
