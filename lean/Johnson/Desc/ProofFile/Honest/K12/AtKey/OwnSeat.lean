-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/OwnSeat.lean: the key file's last chain as a list of four
blocks, and its third block as the seat of the own test. Public: no run, no prover. General in what
the description is made of.

  `place_p12At`   the numbers that a place is given bear that place
  `flat_four`     the chain's flat list has four blocks; the first two have no round and no oracle
                  message; the places of the first three
  `pre_own`       the blocks in front of the own test's place are the first two: so the state on
                  entry's fold (`doorKW`, E2E/KeyProverSideOfOwnTest.lean) runs over these
  `decls_own`, `trees_own`   in front of number 2 no round is declared and no tree is sent
  `seat_own`      at a job at the test's numbers the third block is the seat of that job, at
                  `enterOwn` and `leaveOwn`
  `readsOf_nil`   no declared round, no read

By what. `k12_place` (K12/SaysYesK12.lean), `seatOf_inside` (K12/SaysYesSeat.lean). The rest by the
description's text.

Limits. The block's test on the plan is not read here. Nothing on a run. Nothing on completeness,
soundness or hiding.
-/
import E2E.KeyProverSideOfOwnTest
import Johnson.Desc.ProofFile.Honest.K12.SaysYesSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K12.AtKey
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn)
open VerifiableInference.Desc.Key (Source LaterPlaces descriptionFromSource)
open ProofFile.Honest.K12.AtProof (placeW)
open AtPublicFiles.KeyLay (pWK)

/-- The numbers that a place is given bear that place. -/
theorem place_p12At (a : Place) (x : H2U.PlaceNums) : (H2U.proximityTestParametersAt a x).place = a := by
  unfold H2U.proximityTestParametersAt
  split
  · rfl
  · split <;> rfl

variable (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces)

/-- **The last chain has four blocks.** -/
theorem flat_four : ∃ a b c d : Block (descriptionFromSource Xs Nr Pl).S₃ (descriptionFromSource Xs Nr Pl).Cl,
    (descriptionFromSource Xs Nr Pl).second.blocksInOrder = [a, b, c, d] ∧ a.rounds = [] ∧ b.rounds = [] ∧
      a.oracles = [] ∧ b.oracles = [] ∧ a.place = ⟨3, none, 0, .K14⟩ ∧
      b.place = ⟨3, none, 1, .frame⟩ ∧ c.place = placeW := by
  refine ⟨_, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  show ({ (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt placeW Pl.W) : Block T12 Unit).place with
    chain := 3, link := none, piece := 2 } : Place) = placeW
  rw [k12_place, place_p12At]
  rfl

/-- **The blocks in front of the own test's place are the first two.** -/
theorem pre_own : (descriptionFromSource Xs Nr Pl).second.blocksInOrder.takeWhile (·.place != placeW) =
    (descriptionFromSource Xs Nr Pl).second.blocksInOrder.take 2 := by
  obtain ⟨a, b, c, d, hf, -, -, -, -, ha, hb, hc⟩ := flat_four Xs Nr Pl
  have h1 : (a.place != placeW) = true := by
    rw [ha]
    decide
  have h2 : (b.place != placeW) = true := by
    rw [hb]
    decide
  have h3 : (c.place != placeW) = false := by
    rw [hc]
    simp
  rw [hf]
  simp [List.takeWhile, h1, h2, h3]

/-- In front of number 2 no round is declared. -/
theorem decls_own : declsTo (descriptionFromSource Xs Nr Pl).second.blocksInOrder 2 = [] := by
  obtain ⟨a, b, c, d, hf, ra, rb, -, -, -, -, -⟩ := flat_four Xs Nr Pl
  unfold declsTo
  rw [hf]
  simp [ra, rb]

/-- In front of number 2 no tree is sent. -/
theorem trees_own : treesTo (descriptionFromSource Xs Nr Pl).second.blocksInOrder 2 = 0 := by
  obtain ⟨a, b, c, d, hf, -, -, oa, ob, -, -, -⟩ := flat_four Xs Nr Pl
  unfold treesTo
  rw [hf]
  simp [oa, ob]

/-- **At a job at the test's numbers the third block is that job's seat.** -/
theorem seat_own {W X : Type} (J : TestJob W X) (hp : J.p = pWK Pl)
    (blk : Block (descriptionFromSource Xs Nr Pl).S₃ (descriptionFromSource Xs Nr Pl).Cl)
    (hb : (descriptionFromSource Xs Nr Pl).second.blocksInOrder[2]? = some blk) : SeatOf blk J enterOwn leaveOwn := by
  obtain rfl := Option.some.inj hb
  have h := seatOf_inside (Cl := Unit) J enterOwn leaveOwn
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hp]
    show ({ (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt placeW Pl.W) : Block T12 Unit).place with
      chain := 3, link := none, piece := 2 } : Place) = (pWK Pl).place
    rw [k12_place]
    show _ = (H2U.proximityTestParametersAt placeW Pl.W).place
    rw [place_p12At]
    rfl
  · rw [hp]
    rfl
  · rw [hp]
    rfl
  · rw [hp]
    intro s rs gs
    rfl

/-- No declared round, no read. -/
theorem readsOf_nil (chain ft : ℕ) (st : ℕ → ℕ → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) (ds : List Fmt.Drawn) :
    readsOf chain ft st tree [] ds = [] := by
  cases ds <;> rfl

end ProofFile.Honest.K12.AtKey

#print axioms ProofFile.Honest.K12.AtKey.place_p12At
#print axioms ProofFile.Honest.K12.AtKey.flat_four
#print axioms ProofFile.Honest.K12.AtKey.pre_own
#print axioms ProofFile.Honest.K12.AtKey.decls_own
#print axioms ProofFile.Honest.K12.AtKey.trees_own
#print axioms ProofFile.Honest.K12.AtKey.seat_own
#print axioms ProofFile.Honest.K12.AtKey.readsOf_nil
