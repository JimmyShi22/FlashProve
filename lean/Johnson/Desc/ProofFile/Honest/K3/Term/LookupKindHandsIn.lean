-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupKindHandsIn.lean: AT ANY FILLING. The kind "lookup"
(K3): the lookups' hand-in READ FROM THE OTHER SIDE: not "at every row of the lookups' lot", but "at
every list of parts, of a description's three chains, that is at a place of the kind K3". Under the
library's hypothesis at the full size, `P5J.AtMgA`. One definition of a premise; theorems. General
in the lookups' filling F, in the book under `LookupsOwnNoCoin`, and in the lists G.

  `lookupRowPlaceIsOfTheKind`     a row of the lot is at a place of the kind K3. No premise
  `lookupRowsStandAtDistinctPlaces`   no two rows of the lot are at one place. No premise
                                  (`sites_nodup`, Honest/K3/Law/Coverage.lean)
  `lookupEveryBlockOfTheKindHasARow`   at the place of every sub-protocol of the kind K3 in the
                                  first chain there is a row of the lot (`look_has_site`,
                                  Honest/K3/Law/Thread/CoverageAtHead.lean; there are fifty such
                                  sub-protocols: `looks_fifty`, the same file)
  `noLookupPlaceInTheLaterChains` at every description that `onlineDescription` makes and that passes the
                                  tests on the plan: no sub-protocol of the shared or of the second
                                  chain is at a place of the kind K3 (`shared_fits_descPure`,
                                  Johnson/ToldDescR/PlacesAtTable.lean; `last_places_descPure`,
                                  Johnson/ToldDescR/LastPlaces.lean)
  `lookupLetteredRowIsGood`       `Good` at the side of EVERY list with parameters (`Lettered`,
                                  Honest/Rule.lean) that, its A and B forgotten, is a row of the
                                  lot: whatever its A and B are, so also at lists whose A and B are
                                  "false"
  `OnlyLookupsAtLookupPlaces`     THE ONE PREMISE ON THE LISTS G, by name (below)
  `lookupKindHandsIn`             at every list of G.first, G.shared and G.second at a place of the
                                  kind K3, at every side of it: `Good`, at the `pre` of its place,
                                  at its chain's face and numbers, at the list's own On and bud: the
                                  premises `hand₁`, `hand₂`, `hand₃` of `file_owed_rows`
                                  (Honest/Thread/Rows.lean), cut down to the kind K3. In the shared
                                  and the second chain it holds because no such list has a side

THE ONE PREMISE ON G, AND WHO HOLDS IT. It says nothing of a lookup: it says that nobody else lays a
list at a lookup's place. A list of G.first at a place of the kind K3 is, its A and B forgotten, a
row of the lookups' lot. Where G.first is laid of the lots of a filling, that is: no OTHER lot of
the filling has a side at a place of the kind K3. It falls to the file that lists the wide
filling's lots with their kinds (for ten of them: `FirstFill.widerKinds`,
Honest/Thread/FirstFill.lean; for the closings' and the proximity test's: `closeLotAt_kinds`,
`proxLotAt_kinds`).

AT WHAT THE MAKER RETURNS. `lookupKindHandsIn` stands at a book as a letter and at the description
`P5J.F0T` of the hypothesis. At whatever `onlineProverFromPublicFiles` returns, under the hypothesis, the book is the
return's (`lookupsOwnNoCoinAtAnyFilling`, AtFullSide/Honest/K3/LookupSimulatorAtAnyFilling.lean) and
that description is the return's (`makers_ahead_at_atPure`, AtFullSide/K14/MakersBookOne.lean).

READ THE HEAD OF LookupSimulatorAtTheHead.lean: exact is the spender's half alone; fresh is true and
empty; On and bud are "true"; `Good` is at A and B "false".

THE PROOF FILE'S FIFTY PLACES ALONE: the key file's two lookups are not spoken of.

Limits. Conditional on the head, on the premise on the book and on the one premise on G, which is
shown here at no G. Nothing on any property of the protocol.
-/
import Johnson.P5J.AtTerm
import Johnson.Desc.ProofFile.Honest.Owed
import Johnson.ToldDescR.PlacesAtTable
import Johnson.ToldDescR.LastPlaces
import Johnson.Desc.ProofFile.Honest.K3.Law.LotOfSite
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CoverageAtHead
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupSimulatorAtTheHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open ProofFile.Honest.K3.Law ProofFile.Honest.K3.Law.AtThr

variable {files : VerifierAndGoals.PublicFiles} {description : OnBytes.Maker.WholeD} {proofRun : LPFD.Full.RunPF}
  {publicPart : ProofFile.Pub} {places : H2U.Places4} {firstChain : Chain P5J.TS ProofFile.Cl}
  {lookPlace : VerifiableInference.Desc.First.Look.Place}

section
variable {V W X Pb : Type}

/-- **A row of the lot is at a place of the kind K3.** No premise. -/
theorem lookupRowPlaceIsOfTheKind (F : Pub → Fill W) (publicPart : Pub) (ground : Ground)
    (row : Unlettered V W X Pb) (inLot : row ∈ (lookupSimulatorLot F).rows publicPart ground) :
    row.place.kind = .K3 := by
  obtain ⟨s, hs, rfl⟩ := lookupSimulatorRowOfLot F publicPart ground row inLot
  exact (spot_of_site publicPart s hs).1

/-- **No two rows of the lot are at one place.** No premise. -/
theorem lookupRowsStandAtDistinctPlaces (F : Pub → Fill W) (publicPart : Pub) (ground : Ground) :
    (((lookupSimulatorLot (V := V) (X := X) (Pb := Pb) F).rows publicPart ground).map
      (·.place)).Nodup := by
  have places : ((lookupSimulatorLot (V := V) (X := X) (Pb := Pb) F).rows publicPart ground).map
      (·.place) = (lookSites publicPart).map (·.at_.place) := by
    show ((lookSites publicPart).map fun s =>
      lookupSimulatorRow (V := V) (X := X) (Pb := Pb) (F publicPart) s).map (·.place) = _
    rw [List.map_map]
    rfl
  rw [places]
  exact sites_nodup publicPart

/-- **At the place of every sub-protocol of the kind K3 in the first chain there is a row of the
lot.** -/
theorem lookupEveryBlockOfTheKindHasARow
    (head : P5J.AtMgA OnBytes.secondHashFunction files description proofRun publicPart places firstChain
      lookPlace)
    (F : Pub → Fill W) (ground : Ground) :
    ∀ b ∈ firstChain.blocksInOrder, b.place.kind = .K3 →
      ∃ row ∈ (lookupSimulatorLot (V := V) (X := X) (Pb := Pb) F).rows publicPart ground,
        row.place = b.place := by
  intro b inChain ofKind
  obtain ⟨s, hs, e⟩ := look_has_site head b inChain ofKind
  exact ⟨lookupSimulatorRow (F publicPart) s, List.mem_map.2 ⟨s, hs, rfl⟩, e⟩

/-- **`Good` AT EVERY LIST WITH PARAMETERS THAT IS, ITS A AND B FORGOTTEN, A ROW OF THE LOT.** -/
theorem lookupLetteredRowIsGood
    (head : P5J.AtMgA OnBytes.secondHashFunction files description proofRun publicPart places firstChain
      lookPlace)
    (φ : Face V W Pb) (F : Pub → Fill W) (ground : Ground) (Bk : ProverCoinCounts) (order : List Place)
    (ownNoCoin : LookupsOwnNoCoin Bk publicPart) (chain firstTree : Nat)
    (falls : List (Fall P5J.TS)) (L : Lettered Bk P5J.TS ProofFile.Cl V W X Pb)
    (inLot : L.bare ∈ (lookupSimulatorLot F).rows publicPart ground)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) :
    ∀ σ, L.side firstChain.blocksInOrder falls = some σ →
      ∃ A' B', Good pre φ σ Bk order chain firstTree A' B' L.On L.bud :=
  lookupSimulatorIsGood head φ F ground Bk order ownNoCoin chain firstTree falls L.bare inLot pre

end

variable {W₀ Rc Ky Tr X₀ X : Type}

/-- No place of the shared chain's table is of the kind K3. -/
theorem noLookupPlaceInTheSharedTable (split : Bool) :
    ∀ p ∈ ToldDesc.sharedList split, p.kind ≠ KindName.K3 := by
  cases split <;> decide

/-- No place of the second chain's table is of the kind K3. -/
theorem noLookupPlaceInTheLastTable : ∀ p ∈ ToldDesc.fourPlaces, p.kind ≠ KindName.K3 := by
  decide

/-- **No sub-protocol of the shared or of the second chain is at a place of the kind K3**, at every
description that `onlineDescription` makes and that passes the tests on the plan. -/
theorem noLookupPlaceInTheLaterChains {o : SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {Fd : FileDescription Inst} (made : onlineDescription o pol lay KL = .ok Fd) (plan : Fd.planOk = true) :
    (∀ b ∈ Fd.shared.blocksInOrder, b.place.kind ≠ .K3) ∧ ∀ b ∈ Fd.second.blocksInOrder, b.place.kind ≠ .K3 := by
  obtain ⟨_, N, -, -, fits, -⟩ := ToldDesc.shared_fits_descPure made plan
  rw [← ToldDesc.sharedList_eq] at fits
  have shared : Fd.shared.blocksInOrder.map (·.place) = ToldDesc.sharedList N.O.isSome := eq_of_beq fits
  have second := ToldDesc.last_places_descPure made
  exact ⟨fun b inChain => noLookupPlaceInTheSharedTable _ b.place
      (shared ▸ List.mem_map.2 ⟨b, inChain, rfl⟩),
    fun b inChain => noLookupPlaceInTheLastTable b.place
      (second ▸ List.mem_map.2 ⟨b, inChain, rfl⟩)⟩

/-- A list that has a side is at the place of a sub-protocol of the chain. -/
theorem sideIsAtABlocksPlace {Bk : ProverCoinCounts} {S Cl V W Y Pb : Type} (L : Lettered Bk S Cl V W Y Pb)
    (blocks : List (Block S Cl)) (falls : List (Fall S)) (σ : Side S Cl V W Y Pb)
    (side : L.side blocks falls = some σ) : ∃ b ∈ blocks, b.place = L.place := by
  unfold Lettered.side Side.seated at side
  obtain ⟨b, found, _⟩ := Option.map_eq_some_iff.1 side
  exact ⟨b, List.mem_of_find?_eq_some found, by simpa using List.find?_some found⟩

/-- **THE ONE PREMISE ON THE LISTS**: nobody else lays a list at a lookup's place.
See this file's head. -/
def OnlyLookupsAtLookupPlaces {Bk : ProverCoinCounts}
    (G : Sides (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain) Bk W₀ Rc Ky Tr X₀ X)
    (lookupRows : List (Unlettered (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X Inst)) : Prop :=
  ∀ L ∈ G.first, L.place.kind = .K3 → L.bare ∈ lookupRows

/-- **THE KIND "LOOKUP" HANDS IN, UNDER THREE PREMISES**: `Good` at every list of the three chains
at a place of the kind
K3. Conditional on the head, on the premise on the book and on the one premise on the lists. -/
theorem lookupKindHandsIn
    (head : P5J.AtMgA OnBytes.secondHashFunction files description proofRun publicPart places firstChain
      lookPlace) (Bk : ProverCoinCounts)
    (ownNoCoin : LookupsOwnNoCoin Bk publicPart) (ground : Ground)
    (F : Pub → Fill (Local W₀ Rc Inst Tr))
    (G : Sides (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain) Bk W₀ Rc Ky Tr X₀ X)
    (only : OnlyLookupsAtLookupPlaces G ((lookupSimulatorLot F).rows publicPart ground)) :
    (∀ L ∈ G.first, L.place.kind = .K3 →
      ∀ σ, L.side (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain).first.blocksInOrder G.falls₁ = some σ
          →
        ∃ A' B', Good (preOf 0 0 (earlierOf (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain) 0)
            (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain).first.blocksInOrder L.place) .own σ Bk
          (orderOf (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain)) 0 0 A' B' L.On L.bud) ∧
    (∀ L ∈ G.shared, L.place.kind = .K3 →
      ∀ σ, L.side (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain).shared.blocksInOrder G.falls₂ = some
          σ →
        ∃ A' B', Good (preOf 1 0 (earlierOf (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain) 1)
            (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain).shared.blocksInOrder L.place) .shared σ Bk
          (orderOf (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain)) 1 0 A' B' L.On L.bud) ∧
    ∀ L ∈ G.second, L.place.kind = .K3 →
      ∀ σ, L.side (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain).second.blocksInOrder G.falls₃ = some
          σ →
        ∃ A' B', Good (preOf 2 (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain).lastChainFirstTreeNumber
            (earlierOf (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain) 2)
            (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain).second.blocksInOrder L.place) .own σ Bk
          (orderOf (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain)) 2
          (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain).lastChainFirstTreeNumber A' B' L.On L.bud :=
  ⟨fun L inFirst ofKind =>
      lookupLetteredRowIsGood head .own F ground Bk _ ownNoCoin 0 0 G.falls₁ L
        (only L inFirst ofKind) _,
    fun L _ ofKind σ side => by
      obtain ⟨b, inChain, e⟩ := sideIsAtABlocksPlace L _ _ σ side
      exact absurd (e ▸ ofKind)
        ((noLookupPlaceInTheLaterChains head.laid.value head.laid.planOk).1 b inChain),
    fun L _ ofKind σ side => by
      obtain ⟨b, inChain, e⟩ := sideIsAtABlocksPlace L _ _ σ side
      exact absurd (e ▸ ofKind)
        ((noLookupPlaceInTheLaterChains head.laid.value head.laid.planOk).2 b inChain)⟩

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.lookupRowPlaceIsOfTheKind
#print axioms ProofFile.Honest.K3.Term.lookupRowsStandAtDistinctPlaces
#print axioms ProofFile.Honest.K3.Term.lookupEveryBlockOfTheKindHasARow
#print axioms ProofFile.Honest.K3.Term.lookupLetteredRowIsGood
#print axioms ProofFile.Honest.K3.Term.noLookupPlaceInTheSharedTable
#print axioms ProofFile.Honest.K3.Term.noLookupPlaceInTheLastTable
#print axioms ProofFile.Honest.K3.Term.noLookupPlaceInTheLaterChains
#print axioms ProofFile.Honest.K3.Term.sideIsAtABlocksPlace
#print axioms ProofFile.Honest.K3.Term.OnlyLookupsAtLookupPlaces
#print axioms ProofFile.Honest.K3.Term.lookupKindHandsIn
