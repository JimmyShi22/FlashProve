-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/OnlyLookupsLayRowsAtLookupPlaces.lean: AT THE WIDE FILLING AS
IT IS, THE INDEX A LETTER. The kind "lookup" (K3): THE ONE PREMISE OF `lookupKindHandsIn`
(`OnlyLookupsAtLookupPlaces`, LookupKindHandsIn.lean) IS PAID at sides that are laid from lots of
rows with simulators whose sides are, as one list, the sides that the lots of the wide filling
`onlineProverPartsInUse` (Honest/K1/Law/WSideAtFill.lean) lay, and AMONG WHICH IS THE LOOKUPS' OWN LOT.
Theorems; no definition. "Honest/" stands for Johnson/Desc/ProofFile/Honest/.

  `lookupRowsSidesAreAllOfTheKind`  the sides of the lookups' rows are all at places of the kind K3
  `onlyLookupsLayRowsAtLookupPlaces`   of the rows of such lots, those at a place of the kind K3 are
                                  rows of the lookups' lot: simulators, On and bud too
  `onlyLookupsAtLookupPlacesAtLaidSides`   so `OnlyLookupsAtLookupPlaces` holds at whatever sides
                                  have, as the lists of their first chain, rows of these lots with
                                  parameters A and B set (`laid`)

What follows from it: LookupKindIsGood.lean.

By what: a count. Of the sides that the filling's lots lay, those at a place of the kind K3 are the
lookups' rows' sides, as lists (`lookupRowsHalvesAmongTheLots`,
LookupHalvesAmongTheLotsOfTheWideFilling.lean). The lookups' own lot, which is among the lots, lays
just as many, all at such places (`lookupRowPlaceIsOfTheKind`, LookupKindHandsIn.lean). So the lots
before it and behind it lay none.

The premises on the lots and the sides, and who meets them. `fit`: the rows' sides are, as one list,
the sides that the filling's lots lay: an equation of lists, not of lots. `ours`:
`lookupSimulatorLot` at `lookupFillingAtWeights` is one of the lots. `laid`: forgetting A and B,
each list of the sides' first chain is a row of these lots. All three are the choice of whoever lays
the sides as one term:
`AtPublicFiles.TheSides.RowSlots` (E2E/TheSides.lean, of other authors) has the first as a field.

THE PROOF FILE'S FIFTY PLACES ALONE: the key file's two lookups are not spoken of.

Limits. As in LookupKindHandsIn.lean's head: exact in `Good` is the spender's half alone; fresh is
true and empty; `Good` is at A and B "false". Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupHalvesAmongTheLotsOfTheWideFilling
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKindHandsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain KindName)

/-- The sides of the lookups' rows are all at places of the kind K3. No premise. -/
theorem lookupRowsSidesAreAllOfTheKind {V W X Pb : Type} (F : Pub → Fill W) (publicPart : Pub)
    (ground : Ground) :
    (((lookupSimulatorLot (V := V) (X := X) (Pb := Pb) F).rows publicPart ground).map
        (·.half)).filter (fun h => h.place.kind == KindName.K3) =
      ((lookupSimulatorLot (V := V) (X := X) (Pb := Pb) F).rows publicPart ground).map
        (·.half) := by
  refine List.filter_eq_self.2 fun half inHalves => ?_
  obtain ⟨row, inLot, rfl⟩ := List.mem_map.1 inHalves
  simpa using lookupRowPlaceIsOfTheKind F publicPart ground row inLot

variable {W₀ : Type}

/-- **OF THE ROWS OF SUCH LOTS, THOSE AT A PLACE OF THE KIND K3 ARE ROWS OF THE LOOKUPS' LOT.** -/
theorem onlyLookupsLayRowsAtLookupPlaces (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (publicPart : Pub) (ground : Ground)
    (slots : List (SLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit Inst))
    (fit : (rowsOfLots publicPart ground slots).map (·.half) =
      firstOf publicPart ground (onlineProverPartsInUse I o S O).lots)
    (ours : lookupSimulatorLot (lookupFillingAtWeights I.weights) ∈ slots) :
    ∀ row ∈ rowsOfLots publicPart ground slots, row.place.kind = KindName.K3 →
      row ∈ (lookupSimulatorLot (lookupFillingAtWeights I.weights)).rows publicPart ground := by
  obtain ⟨before, behind, rfl⟩ := List.append_of_mem ours
  have split : rowsOfLots publicPart ground
      (before ++ lookupSimulatorLot (lookupFillingAtWeights I.weights) :: behind) =
      rowsOfLots publicPart ground before ++
        ((lookupSimulatorLot (lookupFillingAtWeights I.weights)).rows publicPart ground ++
          rowsOfLots publicPart ground behind) := by
    unfold rowsOfLots
    rw [List.flatMap_append, List.flatMap_cons]
  have tie := lookupRowsHalvesAmongTheLots (Pb := Inst) I o S O publicPart ground
  rw [← fit, split, List.map_append, List.map_append, List.filter_append, List.filter_append,
    lookupRowsSidesAreAllOfTheKind] at tie
  have lengths := congrArg List.length tie
  rw [List.length_append, List.length_append] at lengths
  have noneBefore : ((rowsOfLots publicPart ground before).map (·.half)).filter
      (fun h => h.place.kind == KindName.K3) = [] := List.length_eq_zero_iff.1 (by omega)
  have noneBehind : ((rowsOfLots publicPart ground behind).map (·.half)).filter
      (fun h => h.place.kind == KindName.K3) = [] := List.length_eq_zero_iff.1 (by omega)
  intro row inRows ofKind
  rw [split] at inRows
  have isOfKind : (row.half.place.kind == KindName.K3) = true := by simpa using ofKind
  rcases List.mem_append.1 inRows with inBefore | inRest
  · have impossible : row.half ∈ ((rowsOfLots publicPart ground before).map (·.half)).filter
        (fun h => h.place.kind == KindName.K3) :=
      List.mem_filter.2 ⟨List.mem_map.2 ⟨row, inBefore, rfl⟩, isOfKind⟩
    rw [noneBefore] at impossible
    cases impossible
  · rcases List.mem_append.1 inRest with inOurs | inBehind
    · exact inOurs
    · have impossible : row.half ∈ ((rowsOfLots publicPart ground behind).map (·.half)).filter
          (fun h => h.place.kind == KindName.K3) :=
        List.mem_filter.2 ⟨List.mem_map.2 ⟨row, inBehind, rfl⟩, isOfKind⟩
      rw [noneBehind] at impossible
      cases impossible

variable {files : VerifierAndGoals.PublicFiles} {description : OnBytes.Maker.WholeD} {proofRun : LPFD.Full.RunPF}
  {publicPart : ProofFile.Pub} {places : H2U.Places4} {firstChain : Chain P5J.TS ProofFile.Cl}
  {lookPlace : VerifiableInference.Desc.First.Look.Place} {Ky X₀ : Type}

/-- **THE ONE PREMISE ON THE LISTS HOLDS AT SIDES LAID FROM SUCH LOTS.** -/
theorem onlyLookupsAtLookupPlacesAtLaidSides {Bk : ProverCoinCounts} (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (ground : Ground)
    (slots : List (SLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Unit Inst))
    (fit : (rowsOfLots publicPart ground slots).map (·.half) =
      firstOf publicPart ground (onlineProverPartsInUse I o S O).lots)
    (ours : lookupSimulatorLot (lookupFillingAtWeights I.weights) ∈ slots)
    (G : Sides (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain) Bk W₀ IndexCommitterCoins Ky Cells X₀ Unit)
    (laid : ∀ L ∈ G.first, L.bare ∈ rowsOfLots publicPart ground slots) :
    OnlyLookupsAtLookupPlaces G
      ((lookupSimulatorLot (lookupFillingAtWeights I.weights)).rows publicPart ground) :=
  fun L inFirst ofKind =>
    onlyLookupsLayRowsAtLookupPlaces I o S O publicPart ground slots fit ours L.bare
      (laid L inFirst) ofKind

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupRowsSidesAreAllOfTheKind
#print axioms ProofFile.Honest.K3.Term.onlyLookupsLayRowsAtLookupPlaces
#print axioms ProofFile.Honest.K3.Term.onlyLookupsAtLookupPlacesAtLaidSides
