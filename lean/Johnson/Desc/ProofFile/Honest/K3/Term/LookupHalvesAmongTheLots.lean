-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupHalvesAmongTheLots.lean: AT THE WIDE FILLING, THE INDEX
A LETTER, AS IT IS AND READ THROUGH. The kind "lookup" (K3): THE TIE BETWEEN THE PROVER'S SIDES AND
THE LOOKUPS' ROWS, AS AN EQUATION OF LISTS IN THE FILLING'S ORDER: of all the sides that the
thirteen lots of `onlineProverPartsInUse` (Honest/K1/Law/WSideAtFill.lean) lay, those at a place of the
kind K3 are the sides of the lookups' rows, in their order: none twice, none beside, none of another
lot. Theorems; no definition. No premise. "Honest/" stands for Johnson/Desc/ProofFile/Honest/.

  `sidesOfOneKindAmongPairs`      general: of the sides that a list of lots lays, each lot with a
                                  kind and laying sides of that kind alone, those of one kind are
                                  the sides of the lots of that kind, in order. Also where each lot
                                  is read through: a side read through keeps its place
  `lookupPairIsTheOnlyOneOfItsKind`   of the thirteen pairs (`fillPairs`, Honest/Law/FillPairs.lean)
                                  the lookups' is the one of the kind K3
  `lookupHalvesAmongTheLotsReadThrough`   THE EQUATION at the filling read through `Local.thru g rd`
  `lookupRowsHalvesAmongTheLotsReadThrough`   the same with the right side written as the halves of
                                  the rows of `lookupSimulatorLot`

It is weaker than the equation of lots (`lookupLotIsTheSixthLotReadThrough`,
LookupLotReadThrough.lean), which it uses, in that it speaks of sides at one public part and ground;
it is stronger in that it speaks of ALL the lots: no other lot lays a side at a place of the kind
K3.

By what. `fillPairs_lots`, `fillPairs_kinds` (Honest/Law/FillPairs.lean, of other authors).
`lookupLotByPublicPartReadThrough`. `lookupSimulatorLotForgets` (LookupSimulatorLot.lean).

Limits. Equations between definitions: nothing on what a side sends. Nothing on any property of the
protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.FillPairs
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupLotReadThrough
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupSimulatorLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (KindName)

section
variable {V V' W W' X : Type}

/-- **Of the sides that a list of lots lays, read through, those of one kind are the sides of the
lots of that kind, in order.** `alone`: each lot lays sides of its own kind alone. -/
theorem sidesOfOneKindAmongPairs (see : V' → V) (reader : W' → W) (publicPart : Pub)
    (ground : Ground) (kind : KindName) :
    ∀ (pairs : List (HLot V W X × KindName)),
      (∀ r ∈ pairs, ∀ x ∈ r.1.halves publicPart ground, x.place.kind = r.2) →
      (firstOf publicPart ground (pairs.map fun r => r.1.thru see reader)).filter
          (fun h => h.place.kind == kind) =
        firstOf publicPart ground ((pairs.filter fun r => r.2 == kind).map fun r =>
          r.1.thru see reader)
  | [], _ => rfl
  | r :: pairs, alone => by
    have rest := sidesOfOneKindAmongPairs see reader publicPart ground kind pairs
      fun q inPairs => alone q (List.mem_cons_of_mem _ inPairs)
    have here : ∀ h ∈ (r.1.thru see reader).halves publicPart ground, h.place.kind = r.2 := by
      intro h inHalves
      obtain ⟨x, inLot, rfl⟩ := List.mem_map.1 inHalves
      exact alone r List.mem_cons_self x inLot
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

variable {W₀ W₀' Rc' : Type}

/-- **Of the thirteen pairs the lookups' is the one of the kind K3.** -/
theorem lookupPairIsTheOnlyOneOfItsKind (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ((fillPairs I o S O).filter fun r => r.2 == KindName.K3) =
      [(HLot.byPub I.weights fun wt => theLotInst id wt, KindName.K3)] :=
  rfl

/-- **THE TIE, AS AN EQUATION OF LISTS IN THE FILLING'S ORDER**: of all the sides that the lots of
the wide filling, read through, lay, those at a place of the kind K3 are the lookups' own. -/
theorem lookupHalvesAmongTheLotsReadThrough (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d' : W₀')
    (publicPart : Pub) (ground : Ground) :
    (firstOf publicPart ground (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)).lots).filter
        (fun h => h.place.kind == KindName.K3) =
      (rowLotAt (lookupFillingThrough I.weights g rd)).halves publicPart ground := by
  have lots : (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)).lots =
      (fillPairs I o S O).map fun r => r.1.thru (Local.thru g rd) (Local.thru g rd) := by
    show (onlineProverPartsInUse I o S O).lots.map (HLot.thru (Local.thru g rd) (Local.thru g rd)) = _
    rw [fillPairs_lots, List.map_map]
    rfl
  rw [lots, sidesOfOneKindAmongPairs (Local.thru g rd) (Local.thru g rd) publicPart ground .K3
    (fillPairs I o S O) (fillPairs_kinds I o S O publicPart ground),
    lookupPairIsTheOnlyOneOfItsKind, ← lookupLotByPublicPartReadThrough]
  exact List.append_nil _

/-- **The same, its right side the sides of the lookups' rows with simulators.** -/
theorem lookupRowsHalvesAmongTheLotsReadThrough {Pb : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins) (d' : W₀')
    (publicPart : Pub) (ground : Ground) :
    (firstOf publicPart ground (OnlineProverParts.through g rd d' (onlineProverPartsInUse I o S O)).lots).filter
        (fun h => h.place.kind == KindName.K3) =
      ((lookupSimulatorLot (Pb := Pb) (lookupFillingThrough I.weights g rd)).rows publicPart
        ground).map (·.half) := by
  rw [lookupHalvesAmongTheLotsReadThrough, ← lookupSimulatorLotForgets (Pb := Pb)]
  rfl

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.sidesOfOneKindAmongPairs
#print axioms ProofFile.Honest.K3.Term.lookupPairIsTheOnlyOneOfItsKind
#print axioms ProofFile.Honest.K3.Term.lookupHalvesAmongTheLotsReadThrough
#print axioms ProofFile.Honest.K3.Term.lookupRowsHalvesAmongTheLotsReadThrough
