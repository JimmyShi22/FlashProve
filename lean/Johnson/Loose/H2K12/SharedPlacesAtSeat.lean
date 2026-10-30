-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.SharedPlacesAtDescN
import Johnson.Loose.H2K12.OmegaIsSome
import Johnson.Loose.H2K12.SitsAtDescPure
import Johnson.Desc.Laid.ProofFullScope
/-
Johnson/Loose/H2K12/SharedPlacesAtSeat.lean: (L1) IN THE GOALS' SCOPE AND AT LPFD.Full.proofDataAndDecisionOfPublicFiles's RETURN:
THE SEATED SHARED CHAIN's FLAT LIST HAS THE TABLE's PLACES AT split := true. Over the library's
own texts; the half that needs neither the scope nor proofDataAndDecisionOfPublicFiles
(descN_places₂ · split_at_seat | noSplit_at_seat · l1_at_seat · l1_not_one · sharedPre_length)
stands in H2K12/SharedPlacesAtDescN.lean; the four tops stand here.
FACTS ON THE PLAN. NO SOUNDNESS IS CLAIMED. NOTHING ON
HIDING.
  descN_places₂_scope    VerifierAndGoals.InScope S · the description's test on the plan · seatPinnedProof ⇒ the
      list's places = ‹the nine in front, a letter› ++ [⟨2, none, 9, .K12⟩, ⟨2, none, 10, .K12⟩,
      ⟨2, none, 11, .frame⟩]
  sharedPre_length_scope: under the same: (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).length = 9
  l1_in_scope            under the same: placesFitS ((descN …).pull f).shared (sharedPlaces true) =
      true, at every map f of instances
  l1_laid                VerifierAndGoals.InScope S · LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r) ⇒
      ∃ Z N c, the returns ∧ r = ((descN …).pull LPFD.Full.instanceAsPlainRecord).run ∧ placesFitS … = true
FELLOWS: Johnson/Desc/Sound/SharedPlacesFit.lean [not in this library]
(shared_places_fit · shared_places_not_one:
the chain as the seats' texts make it; by its own word it does not say that a written description's
shared chain is that value): the general half is typed twice; the seated half is here alone.
No sorry, no axiom of ours; each theorem has its premises; what each rests on is printed at the file's
end.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- In the goals' scope. -/
theorem descN_places₂_scope {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope S = true)
    (Z : ProofFile.Pub) (mk : ProofFile.LinksBy) (N : H2U.Places4) (c : Chain First.S ProofFile.Cl)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true) :
    (descN o mk guardedProximityTestParts Z N c).shared.blocksInOrder.map (·.place) =
      (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).map (·.place) ++
        [⟨2, none, 9, .K12⟩, ⟨2, none, 10, .K12⟩, ⟨2, none, 11, .frame⟩] := by
  obtain ⟨nO, hO⟩ := omega_some_in_scope hS Z mk N c hp hpin
  rw [descN_places₂, hO]
  rfl

open VerifiableInference.Desc.Shared (placesFitS sharedPlaces)

/-- In the goals' scope. -/
theorem sharedPre_length_scope {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope S = true)
    (Z : ProofFile.Pub) (mk : ProofFile.LinksBy) (N : H2U.Places4) (c : Chain First.S ProofFile.Cl)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true) :
    (sharedPre ProofFile.Cl Z.p.chains (p14N Z N) N).length = 9 := by
  obtain ⟨nO, hO⟩ := omega_some_in_scope hS Z mk N c hp hpin
  exact sharedPre_length o mk Z N c hp nO hO

/-- In the goals' scope, behind any map of instances. -/
theorem l1_in_scope {Xi' : Type} {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles}
    (hS : VerifierAndGoals.InScope S = true) (Z : ProofFile.Pub) (mk : ProofFile.LinksBy) (N : H2U.Places4)
    (c : Chain First.S ProofFile.Cl) (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true) (f : Xi' → ProofFile.Inst) :
    placesFitS ((descN o mk guardedProximityTestParts Z N c).pull f).shared (sharedPlaces true) = true := by
  obtain ⟨nO, hO⟩ := omega_some_in_scope hS Z mk N c hp hpin
  exact l1_at_seat o mk Z N c hp nO hO

/-- At the value that is laid. -/
theorem l1_laid (S : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope S = true) (o : ProofFile.SecondHashFunctionArgument)
    (D : OnBytes.Maker.WholeD) (r : _)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r)) :
    ∃ Z N c, ProofFile.pubPlain o S.pol S.lay S.KL = .ok Z ∧ H2U.placesOfMade Z.made = .ok N ∧
      ProofFile.onlineDescription o S.pol S.lay S.KL = .ok (descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) ∧
      r = ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).pull LPFD.Full.instanceAsPlainRecord).run ∧
      placesFitS ((descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c).pull LPFD.Full.instanceAsPlainRecord).shared
        (sharedPlaces true) = true := by
  obtain ⟨F, hF, hp, _, hs, hr⟩ := LPFD.Full.laidPOf_ok hL
  have hpin := LPFD.asks_written hs
  obtain ⟨Z, N, c, _, hZ, hN, rfl, _⟩ := k12_sits o S.pol S.lay S.KL F hF
  exact ⟨Z, N, c, hZ, hN, hF, hr, l1_in_scope hS Z _ N c hp hpin _⟩

end H2K.JointK

#print axioms H2K.JointK.descN_places₂_scope
#print axioms H2K.JointK.sharedPre_length_scope
#print axioms H2K.JointK.l1_in_scope
#print axioms H2K.JointK.l1_laid
