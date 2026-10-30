-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/AtTheLetters.lean: the tops of the shared sending (kind K1), of its Script, of its head and of the stored
columns, ended at the names of AtFullSide/Honest/TheLettersFirst.lean: numbers, first, falls₁, thread₁, said₁, OpenFiles, J₁.

  1  first_is_firstParts      first is the parts at the closed Script firstScriptAt
  2  k1_five_at_letters       at every value F of OpenFiles: FiveAtBorderJ at every place of the kind K1, at thread₁, said₁,
                              J₁ h F and falls₁: K1's share of owes₁, yes₁ and carry₁
  3  fix₁_at_letters          each tree of the first chain's Script is fixed by the challenges heard
  4  rootedSides_at_letters   every member that sends a root has a side
  5  stored_at_letters        the base prover has every stored column that the description declares
  6  numberIsPlace_at_letters   NumberIsPlace: the member number b of the first chain stands at the place number b of the
                              written list P5J.At.ps

One call each: k1_five_at_sockets (AtTheSockets.lean), treesFixed_first (FirstScriptFixed.lean), rootedSides_at_sockets,
stored_at_the_base (AtFullSide/Honest/StoredAtTheBase.lean), places_at_mg (Johnson/Loose/H2K12/PlacesAtMg.lean). A value of OpenFiles is not made here:
Johnson/AtFull/Shape/Scope/OpenFilesRun.lean.

Limits.
  * made (the base maker returns) and the head h are hypotheses. In 2: F, a value of OpenFiles: of it the fields seat,
    publicData and shapesToEnd are spent. In 5: scope and live.
  * 2 pays at the 52 members of the kind K1 alone. Each field stands under the thread's invariant in front of the member;
    accepted and next are asked with J₁ in hand; at an input that does not meet the thread's valid all six fields are idle.
  * At the base prover.
  * This file proves nothing about completeness, soundness or hiding.
-/
import AtFullSide.Honest.TheLettersFirst
import AtFullSide.Honest.StoredAtTheBase
import AtFullSide.K1.AtTheSockets
import Johnson.Loose.H2K12.PlacesAtMg

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest.TheLetters
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.FirstThread
open AtFullSide.Honest
open ProofFile.Honest.Term (matrixInput tableCoins baseMaker)
open Johnson.AtFull.Shape Johnson.AtFull.Shape.Scope
open OnBytes (TableKey)
open VerifiableInference.Desc (KindName)

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- The first thread's parts are the parts at the closed Script. -/
theorem first_is_firstParts : first h = ProofFile.Honest.K1.firstParts matrixInput
    OnBytes.HonestTrace.Sz.ref openHonest A h.firstChain (numbers h) := rfl

/-- **K1's share of owes₁, yes₁ and carry₁, at The Letters.** -/
theorem k1_five_at_letters (made : baseMaker Z = .ok A) (F : OpenFiles A)
    (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K1 →
      FiveAtBorderJ (thread₁ h R) (said₁ h R) (J₁ h F)
        (fallsBy (falls₁ h) h.description.first.blocksInOrder) b :=
  k1_five_at_sockets h (numbers h) made F.seat F.publicData F.shapesToEnd R

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **fix₁ at The Letters.** -/
theorem fix₁_at_letters (made : baseMaker Z = .ok A) :
    ∀ b, b ≤ h.firstChain.blocksInOrder.length → ∀ j, j < treesTo h.firstChain.blocksInOrder b →
      (first h).script.fixed (.own j) ≤ roundsTo h.firstChain.blocksInOrder b :=
  ProofFile.Honest.K1.treesFixed_first h.head made

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **rootedSides.** -/
theorem rootedSides_at_letters (made : baseMaker Z = .ok A) :
    rootedAll h.description A.H = true :=
  rootedSides_at_sockets h made

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **The stored columns, at every input.** -/
theorem stored_at_letters (made : baseMaker Z = .ok A) (scope : VerifierAndGoals.InScope Z = true)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (i : FullSizeMatrix) (ri : (protocolAtFiles Z).EncodingRandomness) :
    ∀ d ∈ h.description.roundsDeclaredByBlocks.1 ++ h.description.roundsDeclaredByBlocks.2.1 ++ h.description.roundsDeclaredByBlocks.2.2,
      ∀ t ∈ d.stored, ∀ y, y < 2 ^ t.sh.a →
        ∃ u, A.H.storedWords i (tableCoins Z ri) t.item y = some u ∧ u.length = t.sh.W :=
  stored_at_the_base h made scope live i ri

omit [Inhabited P5J.TS] [Inhabited Desc.K14.St] in
/-- **A number and its place.** -/
theorem numberIsPlace_at_letters : NumberIsPlace h := by
  intro b blk hb
  have e := H2K12.places_at_mg h.head.toAtMg
  rw [← e, List.getElem?_map, hb]
  rfl

end AtFullSide.Honest.TheLetters

#print axioms AtFullSide.Honest.TheLetters.first_is_firstParts
#print axioms AtFullSide.Honest.TheLetters.k1_five_at_letters
#print axioms AtFullSide.Honest.TheLetters.fix₁_at_letters
#print axioms AtFullSide.Honest.TheLetters.rootedSides_at_letters
#print axioms AtFullSide.Honest.TheLetters.stored_at_letters
#print axioms AtFullSide.Honest.TheLetters.numberIsPlace_at_letters
