-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/E2E/OutputHeadEntryOfRecord.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6): what the
kind hands in for its lot (LotEntry, E2E/TheKOfRecord.lean), and the kind's share and its standing
at the rows theK E apart R wherever E's field k6 is that entry.

WHAT IT IS NOT.
  * NOT ZERO KNOWLEDGE, NOT HIDING: an entry of thirteen, and one share of sixteen, of a conditional
    theorem's premises.
  * E, apart and R are letters: no value of the thirteen entries is laid here; the twelve other
    entries are other files'.
  * The limits of OutputHeadRowAtTheG.lean stand here too. AT THE BASE FILLING.

WHAT IS HERE. One definition and four theorems.
  k6Entry             the entry: the lot headSimulatorLot at the matrices' weights; a lot of the
                      base filling bears its name; it has that lot's sides
  k6Entry_slot        its lot, by name
  k6Laid_atTheK       that lot is among the lots of theK E apart R, where E.k6 is the entry
  k6Share_atTheK      the kind's share at theGOfReturn made h T (theK E apart R): no premise that
                      the lot is laid
  k6Stands_atTheK     a list at the kind's place stands there, with a side

CALLED. headSimulatorLot_fits_the_base_slot (Honest/K6/Term/SlotAtTheFilling.lean), mem_theK
(E2E/TheKOfRecord.lean), k6Share_atTheG, k6Stands_atTheG (OutputHeadRowAtTheG.lean).
-/
import E2E.TheKOfRecord
import AtFullSide.E2E.OutputHeadRowAtTheG

set_option autoImplicit false
set_option maxRecDepth 100000
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtPublicFiles.AtFiles.HonestTerm.OutputHead
open AtPublicFiles.AtFiles
open AtPublicFiles.TheG (ThreadParts theGOfReturn)
open AtPublicFiles.TheSides (KindRows LotEntry TheThirteen LaterRows theK mem_theK)
open ProofFile.Honest (OnlineProverWithDescription Cells ThreadsP ready KindShare)
open ProofFile.Honest.K6 (headSimulatorLot headSimulatorLot_fits_the_base_slot)
open ProofFile.Honest.Term (matrixInput baseMaker baseFilling)
open ProofFile.Honest.FirstThread (HeadAtReturn)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

/-- **What the kind K6 hands in for its lot**, at the base filling. -/
def k6Entry (files : PublicFiles) (Z : ProofFile.Pub) (G : ProofFile.Ground) : LotEntry (baseFilling files) Z G where
  slot := headSimulatorLot (Rc := ProofFile.Honest.IndexCommitterCoins) (X := Unit) matrixInput.weights
  named := rfl
  fit := fun L isALot bearsTheName => by
    obtain rfl := headSimulatorLot_fits_the_base_slot L isALot bearsTheName
    rfl

/-- The entry's lot, by name. -/
theorem k6Entry_slot (files : PublicFiles) (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    (k6Entry files Z G).slot =
      headSimulatorLot (Rc := ProofFile.Honest.IndexCommitterCoins) (X := Unit) matrixInput.weights := rfl

variable {files : PublicFiles} {Wt : Type}

/-- **The kind's lot is among the lots of the K of record**, where the field k6 is the entry. -/
theorem k6Laid_atTheK {Z : ProofFile.Pub} {G : ProofFile.Ground} (E : TheThirteen (baseFilling files) Z G)
    (isTheEntry : E.k6 = k6Entry files Z G) (apart : (E.entries.map (·.slot.name)).Nodup)
    (R : LaterRows (baseFilling files) Z G) :
    headSimulatorLot (Rc := ProofFile.Honest.IndexCommitterCoins) (X := Unit) matrixInput.weights ∈
      (theK E apart R).lots := by
  have laid := mem_theK (e := E.k6) (by simp [TheThirteen.entries]) apart R
  rw [isTheEntry] at laid
  exact laid

/-- CONDITIONAL: in scope; live; the base filling's return; the head at it; E's field k6 is the
entry. **THE KIND's SHARE AT THE K OF RECORD.** -/
theorem k6Share_atTheK
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit}
    (made : baseMaker files = .ok A)
    (h : HeadAtReturn files A) (T : ThreadParts A Wt)
    (E : TheThirteen (baseFilling files) A.Z A.G) (isTheEntry : E.k6 = k6Entry files A.Z A.G)
    (apart : (E.entries.map (·.slot.name)).Nodup) (R : LaterRows (baseFilling files) A.Z A.G)
    (Rel : FullSizeMatrix → ProofFile.Honest.IndexCommitterCoins → ProofFile.Inst → Prop)
    (Th : ∀ w₀ rc ξ, Rel w₀ rc ξ → ∀ k Rd,
      ready A.F A.B ((theGOfReturn made h T (theK E apart R)).prover A.H) w₀ rc ξ k = .ok Rd →
      ThreadsP A.F A.B ((theGOfReturn made h T (theK E apart R)).prover A.H) w₀ rc ξ k Rd) :
    KindShare A (theGOfReturn made h T (theK E apart R)) A.H Rel Th .K6 :=
  k6Share_atTheG scope live made h T (theK E apart R) Rel Th (k6Laid_atTheK E isTheEntry apart R)

/-- CONDITIONAL as k6Share_atTheK. **THE ROW STANDS AT THE K OF RECORD, WITH A SIDE.** -/
theorem k6Stands_atTheK
    (scope : InScope files = true) (live : protocolDataWellFormed (asDescriptionFiles files) = true)
    {A : OnlineProverWithDescription FullSizeMatrix ProofFile.Honest.IndexCommitterCoins Cells Unit Unit}
    (made : baseMaker files = .ok A)
    (h : HeadAtReturn files A) (T : ThreadParts A Wt)
    (E : TheThirteen (baseFilling files) A.Z A.G) (isTheEntry : E.k6 = k6Entry files A.Z A.G)
    (apart : (E.entries.map (·.slot.name)).Nodup) (R : LaterRows (baseFilling files) A.Z A.G) :
    ∃ L ∈ (theGOfReturn made h T (theK E apart R)).first, L.place = IM.k6Place ∧
      ∃ σ, L.side A.F.first.blocksInOrder (theGOfReturn made h T (theK E apart R)).falls₁ = some σ :=
  k6Stands_atTheG scope live made h T (theK E apart R) (k6Laid_atTheK E isTheEntry apart R)

end AtPublicFiles.AtFiles.HonestTerm.OutputHead

#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.k6Entry
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.k6Entry_slot
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.k6Laid_atTheK
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.k6Share_atTheK
#print axioms AtPublicFiles.AtFiles.HonestTerm.OutputHead.k6Stands_atTheK
