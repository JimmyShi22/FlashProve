-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/OnlyLookupsLayRowsAtLookupPlacesReadThrough.lean: AT THE WIDE
FILLING READ THROUGH, THE INDEX AND THE TWO READERS LETTERS. The kind "lookup" (K3): the twin of
OnlyLookupsLayRowsAtLookupPlaces.lean at the filling `OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S
O)`: of the rows of lots of rows with simulators whose sides are, as one list, the sides that this
filling's lots lay, and among which is the lookups' own lot, those at a place of the kind K3 are
rows of the lookups' lot: simulators, On and bud too. Two theorems. It is a sentence on lists of
rows and sides: no law over coins is carried through a reading. "Honest/" stands for
Johnson/Desc/ProofFile/Honest/.

  `rowsAtLookupPlacesAreOneLotsByACount`   THE COUNT, general in the lots, the one lot and the list
                                  of sides: where the rows' sides are that list (`fit`), of that
                                  list the sides at a place of the kind K3 are the one lot's rows'
                                  sides (`tie`), all rows of the one lot are at such places, and the
                                  one lot is among the lots: every row at such a place is the one
                                  lot's
  `onlyLookupsLayRowsAtLookupPlacesReadThrough`   at the filling read through, at
                                  `lookupSimulatorLot` at `lookupFillingThrough`

By what. Lengths of lists alone. The tie: `lookupRowsHalvesAmongTheLotsReadThrough`
(LookupHalvesAmongTheLots.lean). `lookupRowPlaceIsOfTheKind` (LookupKindHandsIn.lean).

THE PROOF FILE'S FIFTY PLACES ALONE: the key file's two lookups are not spoken of.

Limits. Sentences on lists. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupHalvesAmongTheLots
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKindHandsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (KindName)

/-- **THE COUNT.** General in the lots, the one lot and the list of sides. -/
theorem rowsAtLookupPlacesAreOneLotsByACount {V W X Pb : Type} (publicPart : Pub) (ground : Ground)
    (slots : List (SLot V W X Pb)) (oneLot : SLot V W X Pb) (sides : List (Placed V W X))
    (fit : (rowsOfLots publicPart ground slots).map (·.half) = sides)
    (tie : sides.filter (fun h => h.place.kind == KindName.K3) =
      (oneLot.rows publicPart ground).map (·.half))
    (allOfTheKind : ∀ row ∈ oneLot.rows publicPart ground, row.place.kind = KindName.K3)
    (among : oneLot ∈ slots) :
    ∀ row ∈ rowsOfLots publicPart ground slots, row.place.kind = KindName.K3 →
      row ∈ oneLot.rows publicPart ground := by
  obtain ⟨before, behind, rfl⟩ := List.append_of_mem among
  have split : rowsOfLots publicPart ground (before ++ oneLot :: behind) =
      rowsOfLots publicPart ground before ++
        (oneLot.rows publicPart ground ++ rowsOfLots publicPart ground behind) := by
    unfold rowsOfLots
    rw [List.flatMap_append, List.flatMap_cons]
  have allKept : ((oneLot.rows publicPart ground).map (·.half)).filter
      (fun h => h.place.kind == KindName.K3) = (oneLot.rows publicPart ground).map (·.half) := by
    refine List.filter_eq_self.2 fun half inHalves => ?_
    obtain ⟨row, inLot, rfl⟩ := List.mem_map.1 inHalves
    simpa using allOfTheKind row inLot
  rw [← fit, split, List.map_append, List.map_append, List.filter_append, List.filter_append,
    allKept] at tie
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
  · rcases List.mem_append.1 inRest with inOneLot | inBehind
    · exact inOneLot
    · have impossible : row.half ∈ ((rowsOfLots publicPart ground behind).map (·.half)).filter
          (fun h => h.place.kind == KindName.K3) :=
        List.mem_filter.2 ⟨List.mem_map.2 ⟨row, inBehind, rfl⟩, isOfKind⟩
      rw [noneBehind] at impossible
      cases impossible

/-- **AT THE FILLING READ THROUGH: OF THE ROWS OF SUCH LOTS, THOSE AT A PLACE OF THE KIND K3 ARE
ROWS OF
THE LOOKUPS' LOT.** -/
theorem onlyLookupsLayRowsAtLookupPlacesReadThrough {W₀ W₀' Rc' : Type} (I : WiderIn W₀)
    (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins)
    (d' : W₀') (publicPart : Pub) (ground : Ground)
    (slots : List (SLot (Local W₀' Rc' Inst Cells) (Local W₀' Rc' Inst Cells) Unit Inst))
    (fit : (rowsOfLots publicPart ground slots).map (·.half) =
      firstOf publicPart ground (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)).lots)
    (ours : lookupSimulatorLot (lookupFillingThrough I.weights g rd) ∈ slots) :
    ∀ row ∈ rowsOfLots publicPart ground slots, row.place.kind = KindName.K3 →
      row ∈ (lookupSimulatorLot (lookupFillingThrough I.weights g rd)).rows publicPart ground :=
  rowsAtLookupPlacesAreOneLotsByACount publicPart ground slots _ _ fit
    (lookupRowsHalvesAmongTheLotsReadThrough I o S O g rd d' publicPart ground)
    (fun row inLot => lookupRowPlaceIsOfTheKind _ publicPart ground row inLot) ours

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.rowsAtLookupPlacesAreOneLotsByACount
#print axioms ProofFile.Honest.K3.Term.onlyLookupsLayRowsAtLookupPlacesReadThrough
