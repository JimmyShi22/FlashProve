-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/Lookup/LookupSimulatorAtTheBaseProver.lean: AT THE BASE PROVER: NOT THE HONEST PROVER'S FILLING:
the online prover's filling (`onlineFilling`, E2E/TheHonestProver.lean) is this one read through
`tableCoins` (`OnlineProverParts.through`); to carry rows with simulators and the fields of `Owed` through that
reading is other authors'. The kind "lookup" (K3): the lookups' hand-in for their lot of rows with
simulators, at what THE BASE MAKER returns: `ProofFile.Honest.Term.baseMaker files`, the maker `onlineProverFromPublicFiles` at
`ProofFile.Honest.Term.baseFilling files` (E2E/BaseMaker.lean, of other authors): the wide filling
`onlineProverPartsInUse` at `matrixInput`. The twin of LookupSimulatorAtTheTerm.lean, at the stored
tables' own type of randomness. Two definitions; four theorems. "Honest/" stands for
Johnson/Desc/ProofFile/Honest/.

  `lookupFillingAtTheBaseProver`         the lookups' filling there
  `lookupSimulatorLotAtTheBaseProver`    the lookups' lot of rows with simulators there: a closed
                                         term: no index, table randomness, trace or coin is among
                                         its arguments
  `lookupSimulatorLotIsTheSixthLotAtTheBaseProver`
                                         forgetting its simulators gives the sixth of the lots of
                                         `baseFilling files`
  `lookupSimulatorHandInAtTheBaseProver` (a) and (b) of LookupSimulatorAtTheTerm.lean's head, at a
                                         return of `baseMaker files`
  `lookupSimulatorOnHoldsAtTheBaseProver`   On, plainly: at every row of the lot, at every member,
                                         carried block, state and front: so also at a run's own
  `lookupSimulatorHandInIsNotEmptyAtTheBaseProver`   at every set of public files that is in scope
                                         and passes `protocolDataWellFormed` the base maker returns
                                         (`maker_returns_matrix`,
                                         AtFullSide/K1/MakerReturnsBase.lean, of other authors)

Why. The lookups' laws are general in the types of the index and of the randomness and in both
fillings, so they hold at either prover by one call. Whoever carries rows or the fields of `Owed`
through `OnlineProverParts.through` may start from this one.

READ THE HEADS OF LookupSimulatorAtTheTerm.lean AND Honest/K3/Term/LookupSimulatorAtTheHead.lean:
exact is the spender's half alone; fresh is true and empty; On and bud are "true"; `Good` is at A
and B "false".

THE PROOF FILE'S FIFTY PLACES ALONE: the key file's two lookups are not spoken of.

What may be said of this sentence is not this file's to say.

Limits. As there. Nothing on any property of the protocol.
-/
import E2E.BaseMaker
import E2E.Lookup.LookupSimulatorAtTheTerm
import AtFullSide.K1.MakerReturnsBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.Lookup
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Term ProofFile.Honest.Term AtPublicFiles.AtFiles AtPublicFiles.Cut
open AtFullSide.Honest.K3

/-- **The lookups' filling at the base prover.** -/
noncomputable def lookupFillingAtTheBaseProver : Pub → K3.Fill (Local FullSizeMatrix IndexCommitterCoins Inst Cells) :=
  lookupFillingAtWeights matrixInput.weights

/-- **THE LOOKUPS' LOT OF ROWS WITH SIMULATORS AT THE BASE PROVER.** -/
noncomputable def lookupSimulatorLotAtTheBaseProver :
    SLot (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst :=
  lookupSimulatorLot lookupFillingAtTheBaseProver

/-- **Forgetting its simulators gives the sixth of the lots of the base filling.** -/
theorem lookupSimulatorLotIsTheSixthLotAtTheBaseProver (files : VerifierAndGoals.PublicFiles) :
    (baseFilling files).lots[5]? = some lookupSimulatorLotAtTheBaseProver.toHLot := by
  have forgets : lookupSimulatorLotAtTheBaseProver.toHLot =
      HLot.byPub matrixInput.weights fun wt => theLotInst id wt :=
    (lookupSimulatorLotForgets lookupFillingAtTheBaseProver).trans
      (lookupLotByPublicPart matrixInput.weights).symm
  rw [forgets]
  exact lookupLotIsTheSixthLot matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest

/-- **THE LOOKUPS' HAND-IN AT THE BASE PROVER: exact IN IT IS THE SPENDER'S HALF ALONE.** What it
says and does not say: the head. -/
theorem lookupSimulatorHandInAtTheBaseProver (files : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (scope : VerifierAndGoals.InScope files = true) (read : VerifierAndGoals.readFiles files = .ok pp)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (made : baseMaker files = .ok returned)
    (threads : Local FullSizeMatrix IndexCommitterCoins Inst Cells → Thread returned.B returned.F.S₁ returned.F.Cl
      (Local FullSizeMatrix IndexCommitterCoins Inst Cells) (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit Inst)
    (saids : Local FullSizeMatrix IndexCommitterCoins Inst Cells → Nat → Coins returned.B →
      Mid (Local FullSizeMatrix IndexCommitterCoins Inst Cells) Unit → Prop)
    (falls : List (Fall returned.F.S₁)) :
    (baseFilling files).lots[5]? = some lookupSimulatorLotAtTheBaseProver.toHLot ∧
      LookupHandIn returned.F returned.B
        (lookupSimulatorLotAtTheBaseProver.rows returned.Z returned.G) threads saids falls := by
  obtain ⟨publicPart, places, firstChain, lookPlace, head⟩ := P5J.head_of_live files scope read live
  exact ⟨lookupSimulatorLotIsTheSixthLotAtTheBaseProver files,
    lookupSimulatorHandInAtAnyFilling head made lookupFillingAtTheBaseProver threads saids falls⟩

/-- **On, PLAINLY**: at every row of the lot, at every member, carried block, state and front. No
premise: On is "true". -/
theorem lookupSimulatorOnHoldsAtTheBaseProver (publicPart : Pub) (ground : Ground) :
    ∀ row ∈ lookupSimulatorLotAtTheBaseProver.rows publicPart ground,
      ∀ u carried m front, row.On u carried m front :=
  fun row inLot => lookupSimulatorOnHolds lookupFillingAtTheBaseProver publicPart ground row inLot

/-- **IT IS NOT EMPTY**: where the files are in scope and pass the library's test, the base maker
returns. -/
theorem lookupSimulatorHandInIsNotEmptyAtTheBaseProver (files : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) :
    ∃ returned, baseMaker files = .ok returned :=
  ProofFile.Honest.K1.maker_returns_matrix files OnBytes.HonestTrace.Sz.ref openHonest scope live

end AtPublicFiles.Lookup

#print axioms AtPublicFiles.Lookup.lookupFillingAtTheBaseProver
#print axioms AtPublicFiles.Lookup.lookupSimulatorLotAtTheBaseProver
#print axioms AtPublicFiles.Lookup.lookupSimulatorLotIsTheSixthLotAtTheBaseProver
#print axioms AtPublicFiles.Lookup.lookupSimulatorHandInAtTheBaseProver
#print axioms AtPublicFiles.Lookup.lookupSimulatorOnHoldsAtTheBaseProver
#print axioms AtPublicFiles.Lookup.lookupSimulatorHandInIsNotEmptyAtTheBaseProver
