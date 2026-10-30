-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/Lookup/LookupKindPaysAtTheGInScope.lean: AT THE BASE PROVER, AND AT THE TERM. The kind "lookup"
(K3): LookupKindPaysAtTheG.lean's theorems WITH THEIR LETTERS PAID AS FAR AS THEY CAN BE, and THE
MEMBERSHIP THE OTHER WAY. At G at names (`ProofFile.Honest.Term.theGAtBase` | `theGAtTerm`, E2E/TheG.lean,
of other authors). Four theorems, two at each G: joins.

  `everyLookupRowIsLaidAndSeatedInTheGAtBase` | `…AtTerm`   every row of the lookups' lot, at the
                                   return's public part and ground, IS one of the lists of G's first
                                   chain (A and B forgotten), AND THAT LIST HAS A SIDE at G's own
                                   falls. So
                                   `KindPays G .K3` does not pay for nothing: its first clause
                                   speaks of these lists
  `lookupKindPaysAtTheGAtBaseInScope` | `…AtTermInScope`    FROM scope AND `protocolDataWellFormed` ALONE: the
                                   maker returns; there is a head at the return, whose description
                                   is the return's; at EVERY head there, every T and every K that
                                   lays the lookups' lot: `KindPays G .K3` · On · bud
                                   at G's own lists of the kind · the lot's rows are fifty · each is
                                   laid in G and seated

WHAT IS LEFT AT A LETTER, AND WHOSE. T : `ThreadParts returned Wt`: what the three threads take from
outside: bound by "for all"; that a value of that type exists is shown in no file of the lookups. K:
bound by "for all" under "K lays the lookups' lot"; that such a K exists:
`kindRowsWithTheLookupsLotExistAtTheBaseProver` | `…AtTheTerm` (LookupLotIsAmongTheKindsRows.lean).

By what. `baseMaker_returns`, `headAtReturn_baseMaker` (AtFullSide/K1/HeadAtBaseMaker.lean),
`headAtReturn_online` (AtFullSide/K1/HeadAtReturn.lean), `LPFPol.read_of_scope`: of other authors.
`lookupSimulatorHandInIsNotEmptyAtTheTerm` (LookupSimulatorAtTheTerm.lean).
`lookupSimulatorRowIsSeated`, `lookupSimulatorRowsAreFifty`
(Johnson/Desc/ProofFile/Honest/K3/Term/LookupSimulatorAtTheHead.lean).

READ THE HEAD OF THAT LAST FILE: exact in `Good` is THE SPENDER'S HALF ALONE; fresh is TRUE AND
EMPTY; On and bud are "true"; `Good` is at A and B "false". G IS ONE TERM AT A LETTER: a function of
K: that the other kinds' lots in K stand beside simulators that simulate anything is not said.
Nothing here ties G at the base to G at the term.

THE PROOF FILE'S FIFTY PLACES ALONE: the key file's two lookups are not spoken of.

Limits. As there. Nothing on any property of the protocol.
-/
import AtFullSide.K1.HeadAtBaseMaker
import E2E.Lookup.LookupKindPaysAtTheG
import E2E.Lookup.LookupLotIsAmongTheKindsRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtPublicFiles.Lookup
open ProofFile ProofFile.Honest ProofFile.Honest.K3 ProofFile.Honest.K3.Term ProofFile.Honest.Term AtPublicFiles.AtFiles AtPublicFiles.Cut
open AtFullSide.Honest.K3 AtPublicFiles.TheSides AtPublicFiles.TheG
open ProofFile.Honest.FirstThread (HeadAtReturn)
open VerifiableInference.Desc (KindName)
open VerifiableInference.Compilation (KindPays)

variable {files : VerifierAndGoals.PublicFiles} {Wt : Type}

/-! ## 1 At the base prover -/

/-- **EVERY ROW OF THE LOOKUPS' LOT IS LAID IN G AT THE BASE AND SEATED**: the membership the other
way. -/
theorem everyLookupRowIsLaidAndSeatedInTheGAtBase {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (h : HeadAtReturn files returned) (T : ThreadParts returned Wt)
    (K : KindRows (baseFilling files) returned.Z returned.G)
    (ours : lookupSimulatorLotAtTheBaseProver ∈ K.slots.lots) :
    ∀ row ∈ (lookupSimulatorLotAtTheBaseProver).rows returned.Z returned.G,
      ∃ L ∈ (theGAtBase h T K).first, L.bare = row ∧
        ∃ σ, L.side h.description.first.blocksInOrder (theGAtBase h T K).falls₁ = some σ := by
  intro row inLot
  refine ⟨(theLetters h T).first row,
    List.mem_map.2 ⟨row, List.mem_flatMap.2 ⟨_, ours, inLot⟩, rfl⟩, rfl, ?_⟩
  exact lookupSimulatorRowIsSeated h.head (lookupFillingAtTheBaseProver) returned.G _ row inLot

/-- **AT THE BASE, FROM scope AND `protocolDataWellFormed` ALONE: the maker returns; there is a head at the return,
whose description is the return's; and at EVERY head there, every T and every K that lays the
lookups'
lot: `KindPays G .K3`; On; bud; the lot's rows are fifty;
each is laid in G and seated. exact IN `KindPays` IS THE SPENDER'S HALF ALONE.** -/
theorem lookupKindPaysAtTheGAtBaseInScope (files : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) :
    ∃ returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit, baseMaker files = .ok returned ∧
      (∃ h : HeadAtReturn files returned, returned.F = h.description) ∧
      ∀ (h : HeadAtReturn files returned) (Wt : Type) (T : ThreadParts returned Wt)
        (K : KindRows (baseFilling files) returned.Z returned.G),
        lookupSimulatorLotAtTheBaseProver ∈ K.lots →
          KindPays (theGAtBase h T K) KindName.K3 ∧
          (∀ L ∈ (theGAtBase h T K).first, L.place.kind = KindName.K3 →
            ∀ u carried m front, L.On u carried m front) ∧
          (∀ L ∈ (theGAtBase h T K).first, L.place.kind = KindName.K3 →
            ∀ number challenges positions, L.bud number challenges positions) ∧
          ((lookupSimulatorLotAtTheBaseProver).rows returned.Z returned.G).length = 50 ∧
          ∀ row ∈ (lookupSimulatorLotAtTheBaseProver).rows returned.Z returned.G,
            ∃ L ∈ (theGAtBase h T K).first, L.bare = row ∧
              ∃ σ, L.side h.description.first.blocksInOrder (theGAtBase h T K).falls₁ = some σ := by
  obtain ⟨returned, made⟩ := ProofFile.Honest.K1.baseMaker_returns files scope live
  obtain ⟨someHead, sameDescription, -⟩ := ProofFile.Honest.K1.headAtReturn_baseMaker files scope live
      made
  refine ⟨returned, made, ⟨someHead, sameDescription⟩, fun h Wt T K among => ?_⟩
  have ours := lookupLotIsAmongTheSlotsAtTheBaseProver files K among
  exact ⟨lookupKindPaysAtTheGAtBase made h T K ours,
    lookupOnHoldsAtTheListsOfTheGAtBase h T K ours,
    lookupBudHoldsAtTheListsOfTheGAtBase h T K ours,
    lookupSimulatorRowsAreFifty h.head (lookupFillingAtTheBaseProver) returned.G,
    everyLookupRowIsLaidAndSeatedInTheGAtBase h T K ours⟩

/-! ## 2 At the term -/

/-- **EVERY ROW OF THE LOOKUPS' LOT IS LAID IN G AT THE TERM AND SEATED**: the membership the other
way. -/
theorem everyLookupRowIsLaidAndSeatedInTheGAtTerm {returned : OnlineReturn files}
    (h : HeadAtReturn files returned) (T : ThreadParts returned Wt)
    (K : KindRows (onlineFilling files) returned.Z returned.G)
    (ours : lookupSimulatorLotAtTheTerm files ∈ K.slots.lots) :
    ∀ row ∈ (lookupSimulatorLotAtTheTerm files).rows returned.Z returned.G,
      ∃ L ∈ (theGAtTerm h T K).first, L.bare = row ∧
        ∃ σ, L.side h.description.first.blocksInOrder (theGAtTerm h T K).falls₁ = some σ := by
  intro row inLot
  refine ⟨(theLetters h T).first row,
    List.mem_map.2 ⟨row, List.mem_flatMap.2 ⟨_, ours, inLot⟩, rfl⟩, rfl, ?_⟩
  exact lookupSimulatorRowIsSeated h.head (lookupFillingAtTheTerm files) returned.G _ row inLot

/-- **AT THE TERM, FROM scope AND `protocolDataWellFormed` ALONE: the maker returns; there is a head at the return,
whose description is the return's; and at EVERY head there, every T and every K that lays the
lookups'
lot: `KindPays G .K3`; On; bud; the lot's rows are fifty;
each is laid in G and seated. exact IN `KindPays` IS THE SPENDER'S HALF ALONE.** -/
theorem lookupKindPaysAtTheGAtTermInScope (files : VerifierAndGoals.PublicFiles)
    (scope : VerifierAndGoals.InScope files = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) :
    ∃ returned : OnlineReturn files, onlineMaker files = .ok returned ∧
      (∃ h : HeadAtReturn files returned, returned.F = h.description) ∧
      ∀ (h : HeadAtReturn files returned) (Wt : Type) (T : ThreadParts returned Wt)
        (K : KindRows (onlineFilling files) returned.Z returned.G),
        lookupSimulatorLotAtTheTerm files ∈ K.lots →
          KindPays (theGAtTerm h T K) KindName.K3 ∧
          (∀ L ∈ (theGAtTerm h T K).first, L.place.kind = KindName.K3 →
            ∀ u carried m front, L.On u carried m front) ∧
          (∀ L ∈ (theGAtTerm h T K).first, L.place.kind = KindName.K3 →
            ∀ number challenges positions, L.bud number challenges positions) ∧
          ((lookupSimulatorLotAtTheTerm files).rows returned.Z returned.G).length = 50 ∧
          ∀ row ∈ (lookupSimulatorLotAtTheTerm files).rows returned.Z returned.G,
            ∃ L ∈ (theGAtTerm h T K).first, L.bare = row ∧
              ∃ σ, L.side h.description.first.blocksInOrder (theGAtTerm h T K).falls₁ = some σ := by
  obtain ⟨pp, read⟩ := LPFPol.read_of_scope scope
  obtain ⟨returned, made⟩ := lookupSimulatorHandInIsNotEmptyAtTheTerm files scope read live
  obtain ⟨someHead, sameDescription, -⟩ := AtPublicFiles.AtFiles.HonestTerm.headAtReturn_online files scope
      live made
  refine ⟨returned, made, ⟨someHead, sameDescription⟩, fun h Wt T K among => ?_⟩
  have ours := lookupLotIsAmongTheSlotsAtTheTerm files K among
  exact ⟨lookupKindPaysAtTheGAtTerm made h T K ours,
    lookupOnHoldsAtTheListsOfTheGAtTerm h T K ours,
    lookupBudHoldsAtTheListsOfTheGAtTerm h T K ours,
    lookupSimulatorRowsAreFifty h.head (lookupFillingAtTheTerm files) returned.G,
    everyLookupRowIsLaidAndSeatedInTheGAtTerm h T K ours⟩

end AtPublicFiles.Lookup

#print axioms AtPublicFiles.Lookup.everyLookupRowIsLaidAndSeatedInTheGAtBase
#print axioms AtPublicFiles.Lookup.lookupKindPaysAtTheGAtBaseInScope
#print axioms AtPublicFiles.Lookup.everyLookupRowIsLaidAndSeatedInTheGAtTerm
#print axioms AtPublicFiles.Lookup.lookupKindPaysAtTheGAtTermInScope
