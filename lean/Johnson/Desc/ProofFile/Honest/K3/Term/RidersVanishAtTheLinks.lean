-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AT ANY FILLING.
Johnson/Desc/ProofFile/Honest/K3/Term/RidersVanishAtTheLinks.lean: the honest side of the kind
"lookup" (K3), at the lookups on the calls: each array of the caller's rider is 0 at every vertex of
its cube (the field cubes of AtAttention, AtLayers and AtHead, K3/Law/Thread/ExchangeOuts.lean and
ExchangeHeadAll.lean), stated at a link of the first chain as its description finds the link's
place, shape and record.

Premises: the three on the public files (in scope; the files are read; publicOf returns); "the
request is served"; how the link's place is found (attAt; layAt with tlAt; at the head nothing);
the link's number is below 25; at the head, that the instance is read as the request; and one
premise on the messages: the committed symbols are the packing of the honest trace's list at the
link, restricted to the record's sizes (BaseAt).

What is shown.
  attentionRiderVanishesAtTheLink, layersRiderVanishesAtTheLink, headRiderVanishesAtTheLink.
    The head's holds at every place and every token, at the head's sizes, policy and map of cells
    off the public record (k3SizesAt, k3PolicyAt, k3AdrAt) and at the request that the request
    file's words spell (rqAt).

Not claimed: that any committed symbols are that packing; that a verifier's block accepts; anything
on soundness, completeness or zero knowledge.
-/
import Johnson.Desc.First.Look.K3AttInst
import Johnson.Desc.First.Look.K3CallerAtPlan
import Johnson.Desc.First.Look.K3CallerAttScope
import Johnson.Desc.First.Look.K3CallerLayTests
import Johnson.Desc.First.Look.K3LettersAt
import Johnson.Desc.ProofFile.Honest.K3.Term.SelectorsAreOneHotAtTheHonestTrace
import Johnson.Desc.ProofFile.Honest.K3.Term.AttentionRiderVanishesAtTheHonestTrace
import Johnson.Desc.ProofFile.Honest.K3.Term.HeadRiderVanishesAtTheHonestTrace
import Johnson.Desc.ProofFile.Honest.K3.Term.RequestAtTheLettersCoversTheSamePositions
import Johnson.Desc.ProofFile.Honest.K3.Term.HonestTraceFillsThePlansSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes (OracleShape)
open OnBytes.Model (HTailF2)
open OnBytes.HonestTrace (theTrace ServesAt)
open OnBytes.Model.Verify (publicOf)
open OnBytes.Road (Hd.shapeA)
open Inst.Model (Instance ppref ScalesAndPolicy)
open Cb.Pv.Tail (BaseAt)
open VerifiableInference.OnPublicFiles (k3SizesAt k3PolicyAt k3AdrAt)
open VerifiableInference.Desc.Kinds.Head.AtZ (rqAt)
open VerifiableInference.Desc.Kinds.Head.Law (headRider)
open VerifiableInference.Desc.First.Look (Place Sent laySg attSg szOf symAt sigListCalls seatCalls
  ownPart attAt layAt pubAt attRider layRider lookAt_att attOK_scope_link attFits_of)

variable {files : VerifierAndGoals.PublicFiles} {settings : ScalesAndPolicy} {layout : Option ByteArray}
  {publicRecord : OnBytes.Model.Verify.Public} {index : Cm.Idx} {request : Instance ppref}

/-- **At an attention link the rider's array is 0 on its cube**, where the committed symbols are the
packing of the honest trace's list at the link. -/
theorem attentionRiderVanishesAtTheLink (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsRead : publicOf files.pol files.KL layout = .ok publicRecord)
    (requestIsServed : ServesAt publicRecord index request) {link : ℕ}
    (linkIsSmall : link < 25) {place : Place} {shape : OnBytes.Attention.Shape} {tail : HTailF2}
    (placeIsFound : attAt publicRecord link = some (place, shape, tail)) (sent : Sent)
    (radius : OracleShape → Nat) (extension : Iop.ExtSpec) (witnessPart : Type)
    (messages : (attSg place sent radius).Msg)
    (symbolsPackTheTrace : BaseAt
      (symAt sent.codes (sigListCalls sent radius place.link) (seatCalls sent place.link) tail
        messages)
      (restrictedToTheSizes (szOf tail) (theTrace publicRecord index request link))) :
    Cb.Rider.OnCubes (attRider place shape tail sent radius extension witnessPart).g
      (attRider place shape tail sent radius extension witnessPart).f () messages := by
  have marks :=
    OnBytes.HonestTrace.planMarks_in_scope filesAreInScope filesAreRead publicPartIsRead
  have stepIsTwo : (if publicRecord.p4 then 2 else 1) = 2 := by rw [marks.p4]; rfl
  unfold attAt at placeIsFound
  split at placeIsFound
  · rename_i linkIsOdd
    obtain ⟨plansPlace, plansPlaceIsFound, rest⟩ := Option.bind_eq_some_iff.1 placeIsFound
    obtain ⟨plan, planIsFound, rest⟩ := Option.bind_eq_some_iff.1 rest
    obtain ⟨madeShape, shapeIsMade, rest⟩ := Option.map_eq_some_iff.1 rest
    obtain ⟨placeIs, rest⟩ := Prod.mk.inj rest
    obtain ⟨shapeIs, tailIs⟩ := Prod.mk.inj rest
    subst placeIs shapeIs tailIs
    have groupIsSmall : link / 2 < 12 := by omega
    have linkIsItsGroups : 2 * (link / 2) + 1 = link := by omega
    have linkIsInFrontOfTheHead :
        link < (if publicRecord.p4 then 2 else 1) * publicRecord.NGr := by
      rw [stepIsTwo, marks.groups]
      omega
    have linkIsNoLayersLink : link % (if publicRecord.p4 then 2 else 1) ≠ 0 := by
      rw [stepIsTwo]
      omega
    have publicTests := attOK_scope_link filesAreInScope filesAreRead publicPartIsRead
      plansPlaceIsFound linkIsInFrontOfTheHead linkIsNoLayersLink
      (OnBytes.Params.settingOf publicRecord.P.frame) plan.seam.tl sent radius
    rw [stepIsTwo] at publicTests
    obtain rfl : madeShape = plansPlace.fs :=
      Option.some.inj (shapeIsMade.symm.trans publicTests.shape)
    obtain ⟨plan', planIsFound', recordIsFound, -⟩ :=
      lookAt_att plansPlaceIsFound (Nat.ne_of_lt linkIsInFrontOfTheHead) linkIsNoLayersLink
    rw [stepIsTwo] at planIsFound'
    obtain rfl : plan' = plan := Option.some.inj (planIsFound'.symm.trans planIsFound)
    have shapeIsThePlans : Hd.shapeA publicRecord (link / 2) = plan'.S := by
      unfold OnBytes.Road.Hd.shapeA
      rw [planIsFound]
      rfl
    rw [shapeIsThePlans] at publicTests
    have ridden := denominatorsAreRowSumsAtTheHonestTrace filesAreInScope filesAreRead
      publicPartIsRead requestIsServed groupIsSmall
    rw [shapeIsThePlans, linkIsItsGroups] at ridden
    exact attentionRiderVanishesWhereDenominatorsAreRowSums _ plan'.S plan'.seam.tl sent radius
      extension witnessPart messages _
      (attentionMessagesHoldTheTraceWhereTheSymbolsPackIt publicRecord index request
        (recordAtTheLinkHasThePlansMatrices filesAreInScope filesAreRead publicPartIsRead
          linkIsSmall recordIsFound)
        _ plan'.S sent radius messages symbolsPackTheTrace)
      (attFits_of publicTests.fits) ridden
  · cases placeIsFound

/-- **At a layers' link the rider's arrays are 0 on their cubes**, where the committed symbols are
the packing of the honest trace's list at the link. -/
theorem layersRiderVanishesAtTheLink (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsRead : publicOf files.pol files.KL layout = .ok publicRecord)
    (requestIsServed : ServesAt publicRecord index request) {link : ℕ}
    (linkIsSmall : link < 25) {place : Place} {tail : HTailF2}
    (placeIsFound : layAt publicRecord link = some place)
    (recordIsFound : VerifiableInference.Desc.First.Look.tlAt publicRecord link = some tail)
    (sent : Sent) (radius : OracleShape → Nat) (weightsOracle : Cb.OMsg Cb.Gl.E)
    (weightsReading : weightsOracle.Msg → Nat → Nat → Cb.Gl.E) (weightRows weightColumns : Nat)
    (extension : Iop.ExtSpec) (witnessPart : Type)
    (messages : (laySg place sent radius weightsOracle).Msg)
    (symbolsPackTheTrace : BaseAt
      (symAt sent.codes (sigListCalls sent radius place.link) (seatCalls sent place.link) tail
        (ownPart messages))
      (restrictedToTheSizes (szOf tail) (theTrace publicRecord index request link))) :
    Cb.Rider.OnCubes
      (layRider place
        (pubAt publicRecord (link / VerifiableInference.Desc.First.Look.stepOf publicRecord)) tail
        sent radius weightsOracle weightsReading weightRows weightColumns extension witnessPart).g
      (layRider place
        (pubAt publicRecord (link / VerifiableInference.Desc.First.Look.stepOf publicRecord)) tail
        sent radius weightsOracle weightsReading weightRows weightColumns extension witnessPart).f
      () messages := by
  have marks :=
    OnBytes.HonestTrace.planMarks_in_scope filesAreInScope filesAreRead publicPartIsRead
  have stepIsTwo : VerifiableInference.Desc.First.Look.stepOf publicRecord = 2 := by
    unfold VerifiableInference.Desc.First.Look.stepOf
    rw [marks.p4]
    rfl
  have linkIsEven : link % 2 = 0 ∧ link ≠ 24 := by
    unfold layAt at placeIsFound
    split at placeIsFound
    · rename_i test
      rw [stepIsTwo, marks.groups] at test
      simpa using test
    · cases placeIsFound
  have groupIsSmall : link / 2 < 12 := by omega
  have linkIsItsGroups : 2 * (link / 2) = link := by omega
  have messagesHoldTheTrace := messagesHoldTheTraceWhereTheSymbolsPackIt publicRecord index request
    (recordAtTheLinkHasThePlansMatrices filesAreInScope filesAreRead publicPartIsRead linkIsSmall
      recordIsFound)
    place sent radius weightsOracle weightsReading weightRows weightColumns messages
    symbolsPackTheTrace
  rw [← linkIsItsGroups] at messagesHoldTheTrace
  rw [stepIsTwo]
  exact layersRiderVanishesAtTheHonestTrace filesAreInScope filesAreRead publicPartIsRead
    requestIsServed groupIsSmall place tail sent radius weightsOracle weightsReading weightRows
    weightColumns extension witnessPart messages messagesHoldTheTrace

/-- **At the head's link the rider's arrays are 0 on their cubes, at every token**, where the
committed symbols are the packing of the honest trace's list 24. -/
theorem headRiderVanishesAtTheLink (filesAreInScope : VerifierAndGoals.InScope files = true)
    (filesAreRead : VerifierAndGoals.readFiles files = .ok settings)
    (publicPartIsRead : publicOf files.pol files.KL layout = .ok publicRecord)
    (requestIsServed : ServesAt publicRecord index request)
    (publicPart : ProofFile.Pub) {givenInstance : ProofFile.Inst}
    (instanceIsTheRequest : ProofFile.instOf givenInstance = some request) (place : Place) (sent : Sent)
    (radius : OracleShape → ℕ) (weightsOracle : Cb.OMsg Cb.Gl.E)
    (weightsReading : weightsOracle.Msg → ℕ → ℕ → Cb.Gl.E) (weightRows weightColumns : ℕ)
    (extension : Iop.ExtSpec) (witnessPart : Type)
    (messages : (laySg place sent radius weightsOracle).Msg)
    (symbolsPackTheTrace : BaseAt
      (symAt sent.codes (sigListCalls sent radius place.link) (seatCalls sent place.link)
        publicRecord.H.tl (ownPart messages))
      (restrictedToTheSizes (szOf publicRecord.H.tl) (theTrace publicRecord index request 24)))
    (token : ℕ) :
    letI := k3SizesAt publicRecord
    letI := k3PolicyAt publicRecord
    letI := rqAt publicPart givenInstance.pub
    Cb.Rider.OnCubes
      (headRider (k3AdrAt publicRecord) place publicRecord.H.tl sent radius weightsOracle
        weightsReading weightRows weightColumns extension witnessPart).g
      (headRider (k3AdrAt publicRecord) place publicRecord.H.tl sent radius weightsOracle
        weightsReading weightRows weightColumns extension witnessPart).f token messages :=
  headRiderVanishesAtTheHonestTrace filesAreInScope filesAreRead publicPartIsRead requestIsServed
    (rqAt publicPart givenInstance.pub)
    (requestAtTheLettersCoversTheSamePositions publicPart instanceIsTheRequest) place
    publicRecord.H.tl sent radius weightsOracle weightsReading weightRows weightColumns extension
    witnessPart messages
    (messagesHoldTheTraceWhereTheSymbolsPackIt publicRecord index request
      (plansOwnRecordHasThePlansMatrices filesAreInScope filesAreRead publicPartIsRead
        (by norm_num : 24 < 25))
      place sent radius weightsOracle weightsReading weightRows weightColumns messages
      symbolsPackTheTrace)
    token

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.attentionRiderVanishesAtTheLink
#print axioms ProofFile.Honest.K3.Term.layersRiderVanishesAtTheLink
#print axioms ProofFile.Honest.K3.Term.headRiderVanishesAtTheLink
