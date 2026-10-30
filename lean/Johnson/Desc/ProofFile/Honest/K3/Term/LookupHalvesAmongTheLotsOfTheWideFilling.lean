-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupHalvesAmongTheLotsOfTheWideFilling.lean: AT THE WIDE
FILLING AS IT IS, THE INDEX A LETTER: nothing is read through. The kind "lookup" (K3): THE TIE
BETWEEN THE PROVER'S SIDES AND THE LOOKUPS' ROWS, AS AN EQUATION OF LISTS IN THE FILLING'S ORDER: of
all the sides that the thirteen lots of `onlineProverPartsInUse` (Honest/K1/Law/WSideAtFill.lean) lay,
those at a place of the kind K3 are the sides of the lookups' rows, in their order: none beside,
none of another lot. Theorems; no definition. No premise but, in the last, that the maker returns.
"Honest/" stands for Johnson/Desc/ProofFile/Honest/.

  `sidesOfOneKindAmongPairsAsTheyAre`   general: of the sides that a list of lots lays, each lot
                                  with a kind and laying sides of that kind alone, those of one kind
                                  are the sides of the lots of that kind, in order
  `lookupHalvesAmongTheLots`      THE EQUATION at the wide filling
  `lookupRowsHalvesAmongTheLots`  the same with the right side written as the halves of the rows of
                                  `lookupSimulatorLot` at `lookupFillingAtWeights`
  `lookupHalvesAtAReturnOfTheWideFilling`   at whatever `onlineProverFromPublicFiles` returns at the wide filling: of the
                                  returned prover's first list the sides at a place of the kind K3
                                  are these rows' halves at the return's public part and ground

The twin at that filling read through: LookupHalvesAmongTheLots.lean. That no two rows are at one
place: `lookupRowsStandAtDistinctPlaces` (LookupKindHandsIn.lean).

By what. `fillPairs_lots`, `fillPairs_kinds` (Honest/Law/FillPairs.lean, of other authors);
`lookupPairIsTheOnlyOneOfItsKind` (LookupHalvesAmongTheLots.lean); `lookupLotByPublicPart`
(LookupLotReadThrough.lean); `lookupSimulatorLotForgets` (LookupSimulatorLot.lean); `atPure_ok`
(Honest/AtPureLaw.lean).

Limits. Equations between definitions: nothing on what a side sends. Nothing on any property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupHalvesAmongTheLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (KindName)

section
variable {V W X : Type}

/-- **Of the sides that a list of lots lays, those of one kind are the sides of the lots of that
kind, in order.** `alone`: each lot lays sides of its own kind alone. -/
theorem sidesOfOneKindAmongPairsAsTheyAre (publicPart : Pub) (ground : Ground) (kind : KindName) :
    ∀ (pairs : List (HLot V W X × KindName)),
      (∀ r ∈ pairs, ∀ x ∈ r.1.halves publicPart ground, x.place.kind = r.2) →
      (firstOf publicPart ground (pairs.map (·.1))).filter (fun h => h.place.kind == kind) =
        firstOf publicPart ground ((pairs.filter fun r => r.2 == kind).map (·.1))
  | [], _ => rfl
  | r :: pairs, alone => by
    have rest := sidesOfOneKindAmongPairsAsTheyAre publicPart ground kind pairs
      fun q inPairs => alone q (List.mem_cons_of_mem _ inPairs)
    have here := alone r List.mem_cons_self
    unfold firstOf at rest ⊢
    rw [List.map_cons, List.flatMap_cons, List.filter_append, rest]
    by_cases same : r.2 = kind
    · rw [List.filter_cons_of_pos (by simpa using same), List.map_cons, List.flatMap_cons,
        List.filter_eq_self.2 fun h inHalves => by simpa using (here h inHalves).trans same]
    · rw [List.filter_cons_of_neg (by simpa using same),
        List.filter_eq_nil_iff.2 fun h inHalves => by
          simpa using fun e => same ((here h inHalves).symm.trans e),
        List.nil_append]

end

variable {W₀ : Type}

/-- **THE TIE AT THE WIDE FILLING, AS AN EQUATION OF LISTS IN THE FILLING'S ORDER.** -/
theorem lookupHalvesAmongTheLots (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz)
    (O : OnlineProverArguments) (publicPart : Pub) (ground : Ground) :
    (firstOf publicPart ground (onlineProverPartsInUse I o S O).lots).filter
        (fun h => h.place.kind == KindName.K3) =
      (rowLotAt (lookupFillingAtWeights I.weights)).halves publicPart ground := by
  rw [fillPairs_lots, sidesOfOneKindAmongPairsAsTheyAre publicPart ground .K3 (fillPairs I o S O)
    (fillPairs_kinds I o S O publicPart ground), lookupPairIsTheOnlyOneOfItsKind,
    ← lookupLotByPublicPart]
  exact List.append_nil _

/-- **The same, its right side the sides of the lookups' rows with simulators.** -/
theorem lookupRowsHalvesAmongTheLots {Pb : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (publicPart : Pub) (ground : Ground) :
    (firstOf publicPart ground (onlineProverPartsInUse I o S O).lots).filter
        (fun h => h.place.kind == KindName.K3) =
      ((lookupSimulatorLot (Pb := Pb) (lookupFillingAtWeights I.weights)).rows publicPart
        ground).map (·.half) := by
  rw [lookupHalvesAmongTheLots, ← lookupSimulatorLotForgets (Pb := Pb)]
  rfl

/-- **AT WHATEVER THE MAKER RETURNS AT THE WIDE FILLING: THE PROVER'S SIDES AT THE PLACES OF THE
KIND
K3 ARE THE LOOKUPS' ROWS' SIDES**, as lists. Its one premise: the return. -/
theorem lookupHalvesAtAReturnOfTheWideFilling {Pb : Type} (I : WiderIn W₀) (o older : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (pol lay KL : ByteArray)
    {returned : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (made : onlineProverFromPublicFiles older pol lay KL (onlineProverPartsInUse I o S O) = .ok returned) :
    returned.H.first.filter (fun h => h.place.kind == KindName.K3) =
      ((lookupSimulatorLot (Pb := Pb) (lookupFillingAtWeights I.weights)).rows returned.Z
        returned.G).map (·.half) := by
  rw [(atPure_ok made).2.2.2.2.2.2.2.1]
  exact lookupRowsHalvesAmongTheLots I o S O returned.Z returned.G

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.sidesOfOneKindAmongPairsAsTheyAre
#print axioms ProofFile.Honest.K3.Term.lookupHalvesAmongTheLots
#print axioms ProofFile.Honest.K3.Term.lookupRowsHalvesAmongTheLots
#print axioms ProofFile.Honest.K3.Term.lookupHalvesAtAReturnOfTheWideFilling
