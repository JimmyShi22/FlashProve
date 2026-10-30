-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/Lookup/LookupKindPaysAtTheG.lean: AT THE BASE PROVER, AND AT THE TERM. The kind "lookup" (K3):
AT G AT NAMES (`AtPublicFiles.TheG.theG h T K`, E2E/TheG.lean, of other authors), at its two named values
`ProofFile.Honest.Term.theGAtBase` (over a return of `baseMaker files`, E2E/BaseMaker.lean) and
`ProofFile.Honest.Term.theGAtTerm` (over a return of `onlineMaker files`, E2E/TheHonestProver.lean): the
letters are the three chains' threads, the rows those that the kinds lay: OTHER AUTHORS' PROPOSITION
BY ITS NAME, `VerifiableInference.Compilation.KindPays G .K3` (Johnson/T3/OwedOfKinds.lean); and, AT THE
SAME LISTS, the membership, On and bud. Eight theorems, four at each G: calls.

  `lookupListsOfTheGAtBaseAreTheLotsRows` | `…AtTerm…`   THE MEMBERSHIP: forgetting A and B, every
                                   list of G's first chain at a place of the kind K3 is a row of the
                                   lookups' lot there, at the return's public part and ground:
                                   simulators, On and bud too
  `lookupOnHoldsAtTheListsOfTheGAtBase` | `…AtTerm`      On, plainly, AT THESE LISTS
  `lookupBudHoldsAtTheListsOfTheGAtBase` | `…AtTerm`     bud AT THESE LISTS
  `lookupKindPaysAtTheGAtBase` | `…AtTerm`               `KindPays G .K3`

The lookups' lot: at the base `lookupSimulatorLotAtTheBaseProver`
(LookupSimulatorAtTheBaseProver.lean); at the term `lookupSimulatorLotAtTheTerm files`
(LookupLotAtTheTerm.lean).

THE ONE PREMISE THAT IS A CHOICE: `ours`: that lot is one of the lots of `K.slots`. It is for
whoever fills K to show; it is shown in no file of the lookups. The others: `made`, the return (in
the fourth alone); h, the head at that return; T, what the threads take from outside: a letter.

NO LAW OVER COINS IS CARRIED THROUGH A READING HERE. The lookups' laws are general in the types of
the index and of the randomness and in the filling: `Good` at either G is an instance of one theorem
(`lookupKindIsGoodAtTheHead`, Johnson/Desc/ProofFile/Honest/K3/Term/LookupKindIsGood.lean), not a
crossing. What is read through at the term is a lot and lists of sides: equations between
definitions.

READ THE HEAD OF Johnson/Desc/ProofFile/Honest/K3/Term/LookupSimulatorAtTheHead.lean: exact in
`Good` is THE SPENDER'S HALF ALONE; fresh is TRUE AND EMPTY; On and bud are "true"; `Good` is at A
and B "false". G IS ONE TERM AT A LETTER: a function of K: that the other kinds' lots in K stand
beside simulators that simulate anything is not said.

THE PROOF FILE'S FIFTY PLACES ALONE: the key file's two lookups are not spoken of.

Limits. As there. Nothing on any property of the protocol.
-/
import E2E.TheG
import Johnson.T3.OwedOfKinds
import E2E.Lookup.LookupSimulatorAtTheBaseProver
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKindIsGood
import Johnson.Desc.ProofFile.Honest.K3.Term.OnlyLookupsLayRowsAtLookupPlaces
import Johnson.Desc.ProofFile.Honest.K3.Term.OnlyLookupsLayRowsAtLookupPlacesReadThrough

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

/-- **THE MEMBERSHIP AT G AT THE BASE**: forgetting A and B, every list of G's first chain at a
place of
the kind K3 is a row of the lookups' lot there. -/
theorem lookupListsOfTheGAtBaseAreTheLotsRows {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (h : HeadAtReturn files returned) (T : ThreadParts returned Wt)
    (K : KindRows (baseFilling files) returned.Z returned.G)
    (ours : lookupSimulatorLotAtTheBaseProver ∈ K.slots.lots) :
    ∀ L ∈ (theGAtBase h T K).first, L.place.kind = KindName.K3 →
      L.bare ∈ (lookupSimulatorLotAtTheBaseProver).rows returned.Z returned.G := by
  intro L inFirst ofKind
  obtain ⟨row, inRows, rfl⟩ := List.mem_map.1 inFirst
  exact onlyLookupsLayRowsAtLookupPlaces matrixInput OnBytes.secondHashFunction
    OnBytes.HonestTrace.Sz.ref openHonest returned.Z
    returned.G K.slots.lots K.slots.lots_fit ours row inRows ofKind

/-- **On, PLAINLY, AT THE OWN LISTS OF G AT THE BASE OF THE KIND K3.** On is "true" there. -/
theorem lookupOnHoldsAtTheListsOfTheGAtBase {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (h : HeadAtReturn files returned) (T : ThreadParts returned Wt)
    (K : KindRows (baseFilling files) returned.Z returned.G)
    (ours : lookupSimulatorLotAtTheBaseProver ∈ K.slots.lots) :
    ∀ L ∈ (theGAtBase h T K).first, L.place.kind = KindName.K3 →
      ∀ u carried m front, L.On u carried m front :=
  fun L inFirst ofKind =>
    lookupSimulatorOnHolds (lookupFillingAtTheBaseProver) returned.Z returned.G L.bare
      (lookupListsOfTheGAtBaseAreTheLotsRows h T K ours L inFirst ofKind)

/-- **bud AT THE OWN LISTS OF G AT THE BASE OF THE KIND K3.** bud is "true" there. -/
theorem lookupBudHoldsAtTheListsOfTheGAtBase {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (h : HeadAtReturn files returned) (T : ThreadParts returned Wt)
    (K : KindRows (baseFilling files) returned.Z returned.G)
    (ours : lookupSimulatorLotAtTheBaseProver ∈ K.slots.lots) :
    ∀ L ∈ (theGAtBase h T K).first, L.place.kind = KindName.K3 →
      ∀ number challenges positions, L.bud number challenges positions :=
  fun L inFirst ofKind =>
    lookupSimulatorBudHolds (lookupFillingAtTheBaseProver) returned.Z returned.G L.bare
      (lookupListsOfTheGAtBaseAreTheLotsRows h T K ours L inFirst ofKind)

/-- **`KindPays (theGAtBase h T K) .K3`, BY THAT NAME: exact IN IT IS THE SPENDER'S HALF ALONE.** -/
theorem lookupKindPaysAtTheGAtBase {returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (made : baseMaker files = .ok returned) (h : HeadAtReturn files returned)
    (T : ThreadParts returned Wt) (K : KindRows (baseFilling files) returned.Z returned.G)
    (ours : lookupSimulatorLotAtTheBaseProver ∈ K.slots.lots) :
    KindPays (theGAtBase h T K) KindName.K3 :=
  have isGood := lookupKindIsGoodAtTheHead h.head returned.B
    (lookupsOwnNoCoinAtAnyFilling h.head made) returned.G (lookupFillingAtTheBaseProver) (theGAtBase
        h T K)
    (lookupListsOfTheGAtBaseAreTheLotsRows h T K ours)
  ⟨isGood.first, isGood.shared, isGood.last⟩

/-! ## 2 At the term -/

/-- **THE MEMBERSHIP AT G AT THE TERM**: forgetting A and B, every list of G's first chain at a
place of
the kind K3 is a row of the lookups' lot there. -/
theorem lookupListsOfTheGAtTermAreTheLotsRows {returned : OnlineReturn files}
    (h : HeadAtReturn files returned) (T : ThreadParts returned Wt)
    (K : KindRows (onlineFilling files) returned.Z returned.G)
    (ours : lookupSimulatorLotAtTheTerm files ∈ K.slots.lots) :
    ∀ L ∈ (theGAtTerm h T K).first, L.place.kind = KindName.K3 →
      L.bare ∈ (lookupSimulatorLotAtTheTerm files).rows returned.Z returned.G := by
  intro L inFirst ofKind
  obtain ⟨row, inRows, rfl⟩ := List.mem_map.1 inFirst
  exact onlyLookupsLayRowsAtLookupPlacesReadThrough matrixInput OnBytes.secondHashFunction
    OnBytes.HonestTrace.Sz.ref openHonest id (tableCoins files) matrixInput.dummy returned.Z
    returned.G K.slots.lots K.slots.lots_fit ours row inRows ofKind

/-- **On, PLAINLY, AT THE OWN LISTS OF G AT THE TERM OF THE KIND K3.** On is "true" there. -/
theorem lookupOnHoldsAtTheListsOfTheGAtTerm {returned : OnlineReturn files}
    (h : HeadAtReturn files returned) (T : ThreadParts returned Wt)
    (K : KindRows (onlineFilling files) returned.Z returned.G)
    (ours : lookupSimulatorLotAtTheTerm files ∈ K.slots.lots) :
    ∀ L ∈ (theGAtTerm h T K).first, L.place.kind = KindName.K3 →
      ∀ u carried m front, L.On u carried m front :=
  fun L inFirst ofKind =>
    lookupSimulatorOnHolds (lookupFillingAtTheTerm files) returned.Z returned.G L.bare
      (lookupListsOfTheGAtTermAreTheLotsRows h T K ours L inFirst ofKind)

/-- **bud AT THE OWN LISTS OF G AT THE TERM OF THE KIND K3.** bud is "true" there. -/
theorem lookupBudHoldsAtTheListsOfTheGAtTerm {returned : OnlineReturn files}
    (h : HeadAtReturn files returned) (T : ThreadParts returned Wt)
    (K : KindRows (onlineFilling files) returned.Z returned.G)
    (ours : lookupSimulatorLotAtTheTerm files ∈ K.slots.lots) :
    ∀ L ∈ (theGAtTerm h T K).first, L.place.kind = KindName.K3 →
      ∀ number challenges positions, L.bud number challenges positions :=
  fun L inFirst ofKind =>
    lookupSimulatorBudHolds (lookupFillingAtTheTerm files) returned.Z returned.G L.bare
      (lookupListsOfTheGAtTermAreTheLotsRows h T K ours L inFirst ofKind)

/-- **`KindPays (theGAtTerm h T K) .K3`, BY THAT NAME: exact IN IT IS THE SPENDER'S HALF ALONE.** -/
theorem lookupKindPaysAtTheGAtTerm {returned : OnlineReturn files}
    (made : onlineMaker files = .ok returned) (h : HeadAtReturn files returned)
    (T : ThreadParts returned Wt) (K : KindRows (onlineFilling files) returned.Z returned.G)
    (ours : lookupSimulatorLotAtTheTerm files ∈ K.slots.lots) :
    KindPays (theGAtTerm h T K) KindName.K3 :=
  have isGood := lookupKindIsGoodAtTheHead h.head returned.B
    (lookupsOwnNoCoinAtAnyFilling h.head made) returned.G (lookupFillingAtTheTerm files) (theGAtTerm
        h T K)
    (lookupListsOfTheGAtTermAreTheLotsRows h T K ours)
  ⟨isGood.first, isGood.shared, isGood.last⟩

end AtPublicFiles.Lookup

#print axioms AtPublicFiles.Lookup.lookupListsOfTheGAtBaseAreTheLotsRows
#print axioms AtPublicFiles.Lookup.lookupOnHoldsAtTheListsOfTheGAtBase
#print axioms AtPublicFiles.Lookup.lookupBudHoldsAtTheListsOfTheGAtBase
#print axioms AtPublicFiles.Lookup.lookupKindPaysAtTheGAtBase
#print axioms AtPublicFiles.Lookup.lookupListsOfTheGAtTermAreTheLotsRows
#print axioms AtPublicFiles.Lookup.lookupOnHoldsAtTheListsOfTheGAtTerm
#print axioms AtPublicFiles.Lookup.lookupBudHoldsAtTheListsOfTheGAtTerm
#print axioms AtPublicFiles.Lookup.lookupKindPaysAtTheGAtTerm
