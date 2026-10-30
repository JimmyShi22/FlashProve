-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/KeyHead.lean: the key file's description and its four
proximity tests, as far as a statement on a test's first member needs them: what plays the part that
the head `P5J.AtMg` plays for the proof file; and, at each of the four places, that the first
sub-protocol of the chain's list at the place stands there and has the declared rounds and oracle
messages of the test's own block. Public facts alone. It imports Mathlib.

  `find_alone`   `find?` returns a sub-protocol that stands at a place alone
  `oracles_any`   the oracle messages of the test's own block do not hang on the type of claims
  `seat_KR`, `seat_KU`, `seat_KO`, `seat_KW`   at `Key.descriptionFromSource X N P`, general in X, N, P: the ranges'
                 test on the first chain's list, the tests on G_u and on G_omega on the shared
                 chain's, the own test on the last chain's
  `key_head`     in the goals' scope, where `protocolDataWellFormed` says yes: the description is `Key.descriptionFromSource X` at
                 the written `rangesNumsFull` and `laterPlacesFull`
                 (Johnson/HB/LLHARD/KB8/Written.lean)

By what. The library's `key_sits_row` (Johnson/Loose/H2K12/SitsRowKey.lean: each entry is in its
list; no other entry of the list bears the kind; the entries' places), `alike_k12`
(Johnson/Desc/K12/Law/SitsKeyChains.lean), `k12_oracles` (Johnson/Desc/K12/FrameLaws.lean).
`key_head`: `theLive_made` (Johnson/Goal/Description/Live.lean), `laidFixed_is`
(Johnson/Desc/Key/SlotIs.lean), `rangesNumbers_in_scope`, `laterPlaces_in_scope`
(Johnson/AtFull/KeyBack/InScope.lean). It is the library's `kseat_name`
(Johnson/Goal/Description/KeySeat.lean) with the places' numbers pinned: that theorem leaves them
under "there are".

Limits.
- "At every job at the place" says nothing on whether any job there is the prover's; who owns a
  fresh table that came earlier is not named. A definition of type `TestJob` at the place
  `Key.rangesParams N` lies in E2E/KeyRangesJob.lean (`rangesTestJob`), which is not in the library;
  nothing here relates a statement to it. This file's writer knows of no written job at the key
  file's three other places.
- The description stands at the constant `Key.fixedDigest` in the place of the public files' digest,
  not at the digest of these files.
- The four places' numbers are the same two written values at all public files in scope: so the
  goals' two named sets are one plan at all four places.
- The source X stands under "there is": it keeps fields of what the makers return. That `protocolDataWellFormed`
  says yes at any files is not shown here; AtFullSide/Top/LiveAtFull.lean and LiveAtPolicies.lean
  show it at the two named sets, in a side library, with that library's limits.
- The full size alone. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Loose.H2K12.SitsRowKey
import Johnson.AtFull.KeyBack.InScope
import Johnson.Goal.Description.KeySeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference
open VerifiableInference.Desc (Block Place Key.descriptionFromSource)
open VerifiableInference.Desc
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open H2K.JointK
open Johnson.KB8 (rangesNumsFull laterPlacesFull)

/-! ## 1 The first sub-protocol of a list at a place -/

/-- Where a sub-protocol of a list stands at a place, and every sub-protocol of the list at that
place is it, `find?` returns it. -/
theorem find_alone {S Cl : Type} (bs : List (Block S Cl)) (pl : Place) (E : Block S Cl)
    (hm : E ∈ bs) (hp : E.place = pl) (only : ∀ B ∈ bs, B.place = pl → B = E) :
    (bs.find? fun b => b.place == pl) = some E := by
  cases hf : bs.find? (fun b => b.place == pl) with
  | none =>
    have := List.find?_eq_none.1 hf E hm
    rw [hp] at this
    exact (this (by simp)).elim
  | some b =>
    have hb : b.place = pl := by simpa using List.find?_some hf
    rw [only b (List.mem_of_find?_eq_some hf) hb]

/-- The oracle messages of the test's own block do not hang on the type of claims, where the block
passes its test on the plan. -/
theorem oracles_any (Cl : Type) (p : P12) (hk : (proximityTestKind guardedProximityTestParts p : Block T12 Unit).planOk = true) :
    (proximityTestKind guardedProximityTestParts p : Block T12 Cl).oracles = (proximityTestKind guardedProximityTestParts p : Block T12 Unit).oracles := by
  rw [VerifiableInference.Desc.K12.k12_oracles guardedProximityTestParts p hk,
    VerifiableInference.Desc.K12.k12_oracles guardedProximityTestParts p
      ((alike_k12 Cl Unit guardedProximityTestParts p).2.2.trans hk)]

/-! ## 2 The four places of the key file's description -/

section Seats
variable (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)

/-- **The ranges' test**, on the first chain. -/
theorem seat_KR (hp : (Key.descriptionFromSource X N P).planOk = true) :
    ∃ b : Block Key.FirstState Key.Claim,
      ((Key.descriptionFromSource X N P).first.blocksInOrder.find? fun b => b.place == (Key.rangesParams N).place) =
        some b ∧
      b.place = (Key.rangesParams N).place ∧
      b.rounds = (proximityTestKind guardedProximityTestParts (Key.rangesParams N) : Block T12 Unit).rounds ∧
      b.oracles = (proximityTestKind guardedProximityTestParts (Key.rangesParams N) : Block T12 Unit).oracles := by
  have R := key_sits_row X N P
  have hpl : (Key.rangesParams N).place = ⟨1, none, 5, .K12⟩ := place_of_p12At _ _
  refine ⟨rngEntry X.Y.k.oneTime N, ?_, ?_, R.ranges.2.1.rounds, ?_⟩
  · rw [hpl]
    exact find_alone _ _ _ R.ranges.1 (rngEntry_place _ _) fun B hB e =>
      R.ranges.2.2 B hB (by rw [e])
  · rw [hpl]
    exact rngEntry_place _ _
  · exact oracles_any Key.Claim _ (R.plans hp).1

/-- **The test on G_u**, on the shared chain. -/
theorem seat_KU :
    ∃ b : Block _root_.Desc.K14.St Key.Claim,
      ((Key.descriptionFromSource X N P).shared.blocksInOrder.find? fun b =>
        b.place == (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).place) = some b ∧
      b.place = (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).place ∧
      b.rounds = (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Block T12 Unit).rounds ∧
      b.oracles = (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Block T12 Unit).oracles := by
  have R := key_sits_row X N P
  have hpl : (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U).place = ⟨2, none, 9, .K12⟩ := place_of_p12At _ _
  refine ⟨keyGu P, ?_, ?_, rfl, rfl⟩
  · rw [hpl]
    refine find_alone _ _ _ R.gu.1 (keyGu_place P) fun B hB e => ?_
    rcases R.sharedOnly B hB (by rw [e]) with rfl | ⟨nO, _, rfl⟩
    · rfl
    · rw [keyOmega_place] at e
      cases e
  · rw [hpl]
    exact keyGu_place P

/-- **The test on G_omega**, on the shared chain, where the plan has a place for it. -/
theorem seat_KO (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    ∃ b : Block _root_.Desc.K14.St Key.Claim,
      ((Key.descriptionFromSource X N P).shared.blocksInOrder.find? fun b => b.place == (pGomega nO).place) = some b ∧
      b.place = (pGomega nO).place ∧
      b.rounds = (proximityTestKind guardedProximityTestParts (pGomega nO) : Block T12 Unit).rounds ∧
      b.oracles = (proximityTestKind guardedProximityTestParts (pGomega nO) : Block T12 Unit).oracles := by
  have R := key_sits_row X N P
  have hpl : (pGomega nO).place = ⟨2, none, 10, .K12⟩ := place_of_p12At _ _
  refine ⟨keyOmega nO, ?_, ?_, rfl, rfl⟩
  · rw [hpl]
    refine find_alone _ _ _ (R.omega nO hO).1 (keyOmega_place nO) fun B hB e => ?_
    rcases R.sharedOnly B hB (by rw [e]) with rfl | ⟨nO', hO', rfl⟩
    · rw [keyGu_place] at e
      cases e
    · obtain rfl : nO' = nO := Option.some.inj (hO'.symm.trans hO)
      rfl
  · rw [hpl]
    exact keyOmega_place nO

/-- **The own test**, on the last chain. -/
theorem seat_KW :
    ∃ b : Block VerifiableInference.Desc.Third.S₃ Key.Claim,
      ((Key.descriptionFromSource X N P).second.blocksInOrder.find? fun b => b.place == (pOwnK P).place) = some b ∧
      b.place = (pOwnK P).place ∧
      b.rounds = (proximityTestKind guardedProximityTestParts (pOwnK P) : Block T12 Unit).rounds ∧
      b.oracles = (proximityTestKind guardedProximityTestParts (pOwnK P) : Block T12 Unit).oracles := by
  have R := key_sits_row X N P
  have hpl : (pOwnK P).place = ⟨3, none, 2, .K12⟩ := place_of_p12At _ _
  refine ⟨ownEntry Key.Claim (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk'), ?_, ?_, rfl, rfl⟩
  · rw [hpl]
    exact find_alone _ _ _ R.own.1 (ownEntry_place _ _) fun B hB e => R.own.2.2 B hB (by rw [e])
  · rw [hpl]
    exact ownEntry_place _ _

end Seats

/-! ## 3 What plays the head's part -/

/-- **Where the three public files are in the goals' scope and the verifier's test `protocolDataWellFormed` says
yes**: the key file's description is `Key.descriptionFromSource` at a source X that the makers return and AT THE TWO
WRITTEN VALUES of the four places' numbers; it passes its test on the plan; and its run is the
decision that the verifier asks. -/
theorem key_head (Z : VerifierAndGoals.PublicFiles) (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) :
    ∃ X₀ m X,
      PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ ∧
      Key.madeAt X₀ Z.lay Key.fixedDigest = .ok m ∧ Key.sourceOf m = .ok X ∧
      Key.descAt X₀ Z.lay Key.fixedDigest = .ok (Key.descriptionFromSource X rangesNumsFull laterPlacesFull) ∧
      (Key.descriptionFromSource X rangesNumsFull laterPlacesFull).planOk = true ∧
      FlashProve.theKeyRun (VerifierAndGoals.asDescriptionFiles Z) =
        ((Key.descriptionFromSource X rangesNumsFull laterPlacesFull).pull Key.keyInstanceOfOutOfDomainSample).run := by
  obtain ⟨K, _, _, hK, _, _⟩ := FlashProve.theLive_made (VerifierAndGoals.asDescriptionFiles Z) hL
  obtain ⟨D, r⟩ := K
  have hK' : (PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay)).bind
      (fun X => Key.keyDataAndDecisionAtFixedDigest X Z.lay) = .ok (D, r) := hK
  cases hX : PlanWritten.publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) with
  | error e =>
    rw [hX] at hK'
    cases hK'
  | ok X₀ =>
    rw [hX] at hK'
    obtain ⟨m, X, N, P, hm, h1, h2, h3, h0, hp, _, _, _, _, hr⟩ :=
      Key.laidFixed_is X₀ Z.lay D r hK'
    obtain rfl : N = rangesNumsFull :=
      Except.ok.inj (h2.symm.trans (Johnson.AtFull.KeyBack.rangesNumbers_in_scope hS hX hm))
    obtain rfl : P = laterPlacesFull :=
      Except.ok.inj (h3.symm.trans (Johnson.AtFull.KeyBack.laterPlaces_in_scope hS hX hm))
    exact ⟨X₀, m, X, rfl, hm, h1, h0, hp, (FlashProve.theKeyRun_ok hK).trans hr⟩

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.find_alone
#print axioms ProofFile.Honest.K12.Light.oracles_any
#print axioms ProofFile.Honest.K12.Light.seat_KR
#print axioms ProofFile.Honest.K12.Light.seat_KU
#print axioms ProofFile.Honest.K12.Light.seat_KO
#print axioms ProofFile.Honest.K12.Light.seat_KW
#print axioms ProofFile.Honest.K12.Light.key_head
