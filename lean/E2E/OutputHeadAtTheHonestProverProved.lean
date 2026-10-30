-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OutputHeadAtTheHonestProverProved.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6 of the online
proof): the six statements of E2E/OutputHeadAtTheHonestProver.lean are proved. AT THE VALUES OF THE
HONEST PROVER (E2E/TheHonestProver.lean), UNDER THE LIBRARY's HYPOTHESIS ON THE FIRST CHAIN AND
WHERE THE MAKER RETURNS: where the kind stands, which side the prover has there, and that the book
of coins lends that side its runs.

WHAT IT IS NOT.
  * It does not say that the verifier accepts, that a part plays or that a round is reached. Of the
    five statements at the kind's border it holds nothing.
  * "The maker returns" (the maker is onlineProverFromPublicFiles, Honest/AtPure.lean; at the honest prover's filling it
    is onlineMaker) and the library's hypothesis on the first chain (P5J.AtMgA: the full size and
    the format's second hash function alone) are premises of the last three theorems. Neither is shown here
    at any files: where the maker does not return, these three hold of nothing.
  * Calls alone: every clause of SideAndBook is proved under
    Johnson/Desc/ProofFile/Honest/K6/Term/.
  * All limits in the heads of E2E/OutputHeadAtTheHonestProver.lean and of
    Honest/K6/Term/Statements.lean hold here.
  * Nothing on soundness or on what a proof hides.

WHAT IT IS. No definition; six theorems; one local instance, the first of the statements' file's
three.

  fillingIsTheValue             the honest prover's online filling is onlineFillingAt at its six
                                values: the two texts unfold to one
  framedProverIsHandedToTheFrame   the online honest prover at a return of the maker is the frame's
                                family at framedProver: the two texts unfold to one
  framedProverKeepsTheSides     that prover has the maker's sides in all three chains, its range and
                                its named index: it is the maker's with two other fields set
  onlineProverIsTheProverAtTheReturn   where the maker returns, under the hypothesis: onlineProver
                                files is onlineProverAt at that return and at the hypothesis's
                                places and first chain
  outputHeadAtTheBaseProver     SideAndBook at every return of the maker at the base filling
  outputHeadAtTheHonestProver   SideAndBook at every return of onlineMaker

CALLED. standsAtOneBorderUnderTheHead, sideIsTheHeadRowAtTheBase, sideIsTheHeadRowAtTheFilling
(Honest/K6/Term/Joined.lean); bookLendsTheKindAtTheBase, stepsReturnAtTheBase,
bookLendsTheKindAtTheFilling, stepsReturnAtTheFilling (Honest/K6/Term/BookLends.lean);
ToldDesc.pureChainAt_of_open
(Johnson/ToldDescR/PureChainOfOpen.lean).
-/
import E2E.OutputHeadAtTheHonestProver
import Johnson.Desc.ProofFile.Honest.K6.Term.Joined
import Johnson.Desc.ProofFile.Honest.K6.Term.BookLends
import Johnson.ToldDescR.PureChainOfOpen

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm.OutputHead
open AtPublicFiles.Bridge AtPublicFiles.Along AtPublicFiles.Committed AtPublicFiles.Cut
open OnBytes.Slice (frS)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest
open ProofFile.Honest.Term (OnlineReturn onlineMaker onlineFilling matrixInput tableCoins)
open ProofFile.Honest.K6 (K6HalfAt)
open ProofFile.Honest.K6.Term
open VerifierAndGoals (PublicFiles)
open P5J (AtMgA TS F0T)

local instance (priority := high) padsOfTheOutputHeadProofs : Nonempty PadZ :=
  pads_nonempty frS 402653181

/-- **The honest prover's online filling is the general one at its six values.** -/
theorem fillingIsTheValue : FillingIsTheValue := fun _ => rfl

/-- **The online honest prover at a return of the maker is the frame's family at framedProver.** -/
theorem framedProverIsHandedToTheFrame : FramedProverIsHandedToTheFrame := fun _ _ _ _ => rfl

/-- **The prover that the online honest prover hands to the frame has the maker's sides in all three
chains, its range of the index and its named index.** -/
theorem framedProverKeepsTheSides : FramedProverKeepsTheSides :=
  fun _ _ => ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **The honest prover's online term is the online prover at the maker's return.** The library's
hypothesis on the first chain and "the maker returns" are premises. -/
theorem onlineProverIsTheProverAtTheReturn (files : PublicFiles) :
    OnlineProverIsTheProverAtTheReturn files := by
  intro returned places firstChain D r x returns h
  obtain ⟨_, _, opened⟩ := h.laid.opened
  unfold onlineProver
  simp only [returns, h.laid.places, ToldDesc.pureChainAt_of_open opened]

/-- **At the base prover**: where the kind stands, which side the prover has there, and that the
kind pays, which in the shared and the last chain holds of nothing. Two premises: the library's
hypothesis on the first chain and "the maker returns at the base filling". -/
theorem outputHeadAtTheBaseProver (files : PublicFiles) : OutputHeadAtTheBaseProver files := by
  intro base places firstChain D r x returns h
  obtain ⟨side, noneShared, noneLast⟩ := sideIsTheHeadRowAtTheBase FullSizeMatrix files D r base.Z places
    firstChain x matrixInput OnBytes.HonestTrace.Sz.ref openHonest base h returns
  obtain ⟨paysFirst, paysShared, paysLast⟩ := bookLendsTheKindAtTheBase FullSizeMatrix files D r base.Z places
    firstChain x matrixInput OnBytes.HonestTrace.Sz.ref openHonest base h returns
  exact ⟨standsAtOneBorderUnderTheHead files D r base.Z places firstChain x h, side, noneShared,
    noneLast, side.1, paysFirst,
    stepsReturnAtTheBase h matrixInput OnBytes.HonestTrace.Sz.ref openHonest returns, paysShared,
    paysLast⟩

/-- **At the honest prover's own return**: the same. Two premises: the hypothesis and "onlineMaker
returns". -/
theorem outputHeadAtTheHonestProver (files : PublicFiles) : OutputHeadAtTheHonestProver files := by
  intro returned places firstChain D r x returns h
  obtain ⟨side, noneShared, noneLast⟩ := sideIsTheHeadRowAtTheFilling FullSizeMatrix FullSizeMatrix (protocolAtFiles files).EncodingRandomness files D r
    returned.Z places firstChain x id (tableCoins files) matrixInput.dummy matrixInput
    OnBytes.HonestTrace.Sz.ref openHonest returned h returns
  obtain ⟨paysFirst, paysShared, paysLast⟩ := bookLendsTheKindAtTheFilling FullSizeMatrix FullSizeMatrix (protocolAtFiles files).EncodingRandomness files
    D r returned.Z places firstChain x id (tableCoins files) matrixInput.dummy matrixInput
    OnBytes.HonestTrace.Sz.ref openHonest returned h returns
  exact ⟨standsAtOneBorderUnderTheHead files D r returned.Z places firstChain x h, side, noneShared,
    noneLast, side.1, paysFirst,
    stepsReturnAtTheFilling h id (tableCoins files) matrixInput.dummy matrixInput
      OnBytes.HonestTrace.Sz.ref openHonest returns, paysShared, paysLast⟩

end AtPublicFiles.AtFiles.HonestTerm.OutputHead

#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.fillingIsTheValue
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.framedProverIsHandedToTheFrame
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.framedProverKeepsTheSides
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.onlineProverIsTheProverAtTheReturn
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.outputHeadAtTheBaseProver
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.outputHeadAtTheHonestProver
