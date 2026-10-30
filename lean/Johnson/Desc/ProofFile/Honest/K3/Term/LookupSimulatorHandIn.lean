-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupSimulatorHandIn.lean: AT ANY FILLING. The kind "lookup"
(K3): what a kind's author hands in for its lot of rows with simulators (`lookupSimulatorLot`,
LookupSimulatorLot.lean), in the form in which the rule for `Owed` takes it row by row
(`file_owed_rows`, Honest/Thread/Rows.lean). Two structures of sentences; two theorems: joins.
General in the lookups' filling F. "Honest/" stands for Johnson/Desc/ProofFile/Honest/.

  `LookupRowHandIn`   WHAT IS HANDED IN AT ONE ROW, at a description, a book, threads, what is said
                      and falls: eight sentences:
      `placeIsOfTheKind`   the row's place is of the kind K3
      `placeIsABlocks`     it is a sub-protocol's of the first chain          (`seat₁` of the rule)
      `good`               `Good` at the side of the row as laid, at the `pre` of its place, at the
                           first chain's face and numbers, at the book and the description's order
                           of places, at the row's own On and bud              (`hand₁`)
      `budHolds`           bud at every number, challenges and positions      (so `BudDebts.bud₁`)
      `onFollows`          On from every thread and every `Said`               (`on₁`)
      `neverStops`         no part of the row has a stop, public or private
      `simulatorsReadTheirCoinsAlone`   no simulator of the row reads anything but its own coins
      `partsReadNothingShown`   no part of the row reads anything of what has been shown before it
  `LookupHandIn`      WHAT IS HANDED IN FOR A LIST OF ROWS: four sentences:
      `rowsAreFifty`       the rows are fifty
      `placesAreDistinct`  no two of them are at one place
      `everyBlockOfTheKindHasARow`   at the place of every sub-protocol of the kind K3 in the
                           description's first chain there is one of them
      `atEveryRow`         `LookupRowHandIn` at each
  `lookupSimulatorHandInAtTheHead`    `LookupHandIn` at the description of the library's hypothesis
                      at the full size (`P5J.F0T`, Johnson/P5J/AtTerm.lean), at a book as a letter
  `lookupSimulatorHandInAtAReturn`    the same at a value of `OnlineProverWithDescription` (Honest/AtPure.lean) whose
                      public part and description are the hypothesis's: at its own fields
The threads, what is said and the falls are letters: nothing is asked of them.

READ THE HEAD OF LookupSimulatorAtTheHead.lean: exact (a field of `Good`) is the spender's half
alone; fresh is true and empty; On and bud are "true"; `Good` is at A and B "false".

Hypotheses that remain. head: `P5J.AtMgA`. ownNoCoin: `LookupsOwnNoCoin` at the book. In the second:
the two equations on that value. All three are shown at whatever the maker `onlineProverFromPublicFiles` returns, at any
filling, in AtFullSide/Honest/K3/LookupSimulatorAtAnyFilling.lean.

THE PROOF FILE'S FIFTY PLACES ALONE: the key file's two lookups are not spoken of.

Limits. As in the heads of the files named. The two structures are definitions: records of
sentences, none of the library's goals. That F is the filling whose lot a prover's filling lays is
not asked here: LookupLotReadThrough.lean. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPure
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKindHandsIn
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupPartsReadNothingShown
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupSimulatorReadsItsCoinsAlone

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain FileDescription)

variable {files : VerifierAndGoals.PublicFiles} {description : OnBytes.Maker.WholeD} {proofRun : LPFD.Full.RunPF}
  {publicPart : ProofFile.Pub} {places : H2U.Places4} {firstChain : Chain P5J.TS ProofFile.Cl}
  {lookPlace : VerifiableInference.Desc.First.Look.Place} {W₀ Rc Tr X₀ X : Type}

/-- **WHAT IS HANDED IN AT ONE ROW.** A record of sentences: the head says what each is for. -/
structure LookupRowHandIn (Fd : FileDescription Inst) (Bk : ProverCoinCounts)
    (threads : Local W₀ Rc Inst Tr →
      Thread Bk Fd.S₁ Fd.Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)
    (saids : Local W₀ Rc Inst Tr → Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (falls : List (Fall Fd.S₁))
    (row : Unlettered (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst) : Prop where
  placeIsOfTheKind : row.place.kind = .K3
  placeIsABlocks : Fd.first.blocksInOrder.any (fun b => b.place == row.place) = true
  good : ∀ σ, (row.lay threads saids Fd.first.blocksInOrder).side Fd.first.blocksInOrder falls = some σ →
    ∃ A₁ B₁, Good (preOf 0 0 (earlierOf Fd 0) Fd.first.blocksInOrder row.place) .own σ Bk (orderOf Fd) 0 0
      A₁ B₁ (row.lay threads saids Fd.first.blocksInOrder).On (row.lay threads saids Fd.first.blocksInOrder).bud
  budHolds : ∀ number challenges positions, row.bud number challenges positions
  onFollows : ∀ w border depth,
    OnFromS (threads w) (saids w) (row.lay threads saids Fd.first.blocksInOrder) border depth
  neverStops : ∀ v before own, rowStopAt v row.half.parts before own = none
  simulatorsReadTheirCoinsAlone : ∀ pair ∈ row.row, ReadsItsCoinsAlone pair.2
  partsReadNothingShown : ∀ part ∈ row.half.parts, part.readsNoneSeen

/-- **WHAT IS HANDED IN FOR A LIST OF ROWS.** A record of sentences. -/
structure LookupHandIn (Fd : FileDescription Inst) (Bk : ProverCoinCounts)
    (rows : List (Unlettered (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst))
    (threads : Local W₀ Rc Inst Tr →
      Thread Bk Fd.S₁ Fd.Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)
    (saids : Local W₀ Rc Inst Tr → Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (falls : List (Fall Fd.S₁)) : Prop where
  rowsAreFifty : rows.length = 50
  placesAreDistinct : (rows.map (·.place)).Nodup
  everyBlockOfTheKindHasARow :
    ∀ b ∈ Fd.first.blocksInOrder, b.place.kind = .K3 → ∃ row ∈ rows, row.place = b.place
  atEveryRow : ∀ row ∈ rows, LookupRowHandIn Fd Bk threads saids falls row

/-- **THE LOOKUPS' HAND-IN AT THE HEAD'S OWN DESCRIPTION, UNDER TWO PREMISES; exact IN IT IS THE
SPENDER'S HALF ALONE**: under the head, at a book under the premise. -/
theorem lookupSimulatorHandInAtTheHead
    (head : P5J.AtMgA OnBytes.secondHashFunction files description proofRun publicPart places firstChain
      lookPlace)
    (Bk : ProverCoinCounts) (ownNoCoin : LookupsOwnNoCoin Bk publicPart) (ground : Ground)
    (F : Pub → K3.Fill (Local W₀ Rc Inst Tr))
    (threads : Local W₀ Rc Inst Tr →
      Thread Bk (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain).S₁
        (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain).Cl (Local W₀ Rc Inst Tr)
        (Local W₀ Rc Inst Tr) X Inst)
    (saids : Local W₀ Rc Inst Tr → Nat → Coins Bk → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (falls : List (Fall (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain).S₁)) :
    LookupHandIn (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain) Bk
      ((lookupSimulatorLot F).rows publicPart ground) threads saids falls where
  rowsAreFifty := lookupSimulatorRowsAreFifty head F ground
  placesAreDistinct := lookupRowsStandAtDistinctPlaces F publicPart ground
  everyBlockOfTheKindHasARow := lookupEveryBlockOfTheKindHasARow head F ground
  atEveryRow := fun row inLot =>
    { placeIsOfTheKind := lookupRowPlaceIsOfTheKind F publicPart ground row inLot
      placeIsABlocks := by
        obtain ⟨σ, seated⟩ := lookupSimulatorRowIsSeated head F ground [] row inLot
        unfold Side.seated at seated
        obtain ⟨b, found, _⟩ := Option.map_eq_some_iff.1 seated
        have atPlace : b.place = row.place := by simpa using List.find?_some found
        exact List.any_eq_true.2 ⟨b, List.mem_of_find?_eq_some found, beq_iff_eq.2 atPlace⟩
      good := hand_of_seated row threads saids firstChain.blocksInOrder
        (lookupSimulatorIsGood head .own F ground Bk _ ownNoCoin 0 0 falls row inLot _)
      budHolds := lookupSimulatorBudHolds F publicPart ground row inLot
      onFollows := fun w border depth =>
        (lookupOnAndBudHoldEverywhere F publicPart ground row inLot).1 (threads w) (saids w)
          threads saids firstChain.blocksInOrder border depth
      neverStops := lookupSimulatorNeverStops F publicPart ground row inLot
      simulatorsReadTheirCoinsAlone :=
        lookupSimulatorReadsItsCoinsAlone F publicPart ground row inLot
      partsReadNothingShown := lookupRowReadsNothingShown F publicPart ground row inLot }

/-- **THE SAME AT A VALUE OF `OnlineProverWithDescription`**, at its own description, book, public part and ground.
Conditional on the head, on the two equations and on the premise on its book. -/
theorem lookupSimulatorHandInAtAReturn
    (head : P5J.AtMgA OnBytes.secondHashFunction files description proofRun publicPart places firstChain
      lookPlace)
    (returned : OnlineProverWithDescription W₀ Rc Tr X₀ X) (samePublicPart : returned.Z = publicPart)
    (sameDescription : returned.F = P5J.F0T OnBytes.secondHashFunction publicPart places firstChain)
    (ownNoCoin : LookupsOwnNoCoin returned.B publicPart)
    (F : Pub → K3.Fill (Local W₀ Rc Inst Tr))
    (threads : Local W₀ Rc Inst Tr →
      Thread returned.B returned.F.S₁ returned.F.Cl (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X
        Inst)
    (saids : Local W₀ Rc Inst Tr → Nat → Coins returned.B → Mid (Local W₀ Rc Inst Tr) X → Prop)
    (falls : List (Fall returned.F.S₁)) :
    LookupHandIn returned.F returned.B ((lookupSimulatorLot F).rows returned.Z returned.G) threads
      saids falls := by
  obtain ⟨AZ, AG, AF, AB, AH, Areaders, Arows⟩ := returned
  dsimp only at ownNoCoin samePublicPart sameDescription threads saids falls ⊢
  subst samePublicPart sameDescription
  exact lookupSimulatorHandInAtTheHead head AB ownNoCoin AG F threads saids falls

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.LookupRowHandIn
#print axioms ProofFile.Honest.K3.Term.LookupHandIn
#print axioms ProofFile.Honest.K3.Term.lookupSimulatorHandInAtTheHead
#print axioms ProofFile.Honest.K3.Term.lookupSimulatorHandInAtAReturn
