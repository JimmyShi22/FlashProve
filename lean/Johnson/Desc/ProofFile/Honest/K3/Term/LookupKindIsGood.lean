-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/LookupKindIsGood.lean: AT ANY FILLING. The kind "lookup" (K3):
WHAT THE RULE FOR `Owed` TAKES FOR ITS FIELD `good`, CUT TO THE PLACES OF THE KIND K3, AS ONE NAMED
RECORD, at sides G over a description and a book: the three clauses `hand₁`, `hand₂`, `hand₃` of
`file_owed_rows` (Honest/Thread/Rows.lean), each cut by "the list's place is of the kind K3". One
structure; two theorems. "Honest/" stands for Johnson/Desc/ProofFile/Honest/.

  `LookupKindIsGood`             the record: `first`, `shared`, `last`: the text of the three
                                 conclusions of `lookupKindHandsIn` (LookupKindHandsIn.lean), with
                                 the description and the book as letters
  `lookupKindIsGoodAtTheHead`    at the description of the library's hypothesis `P5J.AtMgA`: under
                                 the head, the premise on the book and the one premise on the lists
  `lookupKindIsGoodAtAReturn`    the same at a value of `OnlineProverWithDescription`, at its own description, book,
                                 public part and ground

READ THE HEAD OF LookupSimulatorAtTheHead.lean: exact in `Good` is THE SPENDER'S HALF ALONE; fresh
is TRUE AND EMPTY; On and bud are "true"; `Good` is at A and B "false". The clauses `shared` and
`last` hold because no sub-protocol of these two chains is of the kind K3.

THE PROOF FILE'S FIFTY PLACES ALONE: the key file's two lookups are not spoken of.

Limits. A record of sentences and two calls. Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPure
import Johnson.Desc.ProofFile.Honest.K3.Term.LookupKindHandsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (Chain FileDescription KindName)

variable {W₀ Rc Ky Tr X₀ X : Type}

/-- **`Good` AT EVERY LIST OF THE THREE CHAINS AT A PLACE OF THE KIND K3: exact IN IT IS THE
SPENDER'S
HALF ALONE.** The faces, numbers and `pre` are the rule's own at each chain. -/
structure LookupKindIsGood (Fd : FileDescription Inst) (Bk : ProverCoinCounts)
    (G : Sides Fd Bk W₀ Rc Ky Tr X₀ X) : Prop where
  /-- the first chain -/
  first : ∀ L ∈ G.first, L.place.kind = KindName.K3 →
    ∀ σ, L.side Fd.first.blocksInOrder G.falls₁ = some σ →
      ∃ A' B', Good (preOf 0 0 (earlierOf Fd 0) Fd.first.blocksInOrder L.place) .own σ Bk (orderOf Fd) 0 0
        A' B' L.On L.bud
  /-- the shared chain -/
  shared : ∀ L ∈ G.shared, L.place.kind = KindName.K3 →
    ∀ σ, L.side Fd.shared.blocksInOrder G.falls₂ = some σ →
      ∃ A' B', Good (preOf 1 0 (earlierOf Fd 1) Fd.shared.blocksInOrder L.place) .shared σ Bk (orderOf Fd)
        1 0 A' B' L.On L.bud
  /-- the last chain -/
  last : ∀ L ∈ G.second, L.place.kind = KindName.K3 →
    ∀ σ, L.side Fd.second.blocksInOrder G.falls₃ = some σ →
      ∃ A' B', Good (preOf 2 Fd.lastChainFirstTreeNumber (earlierOf Fd 2) Fd.second.blocksInOrder L.place) .own σ Bk
        (orderOf Fd) 2 Fd.lastChainFirstTreeNumber A' B' L.On L.bud

variable {files : VerifierAndGoals.PublicFiles} {description : OnBytes.Maker.WholeD} {proofRun : LPFD.Full.RunPF}
  {publicPart : ProofFile.Pub} {places : H2U.Places4} {firstChain : Chain P5J.TS ProofFile.Cl}
  {lookPlace : VerifiableInference.Desc.First.Look.Place}

/-- **The record at the head's own description, UNDER THREE PREMISES.** -/
theorem lookupKindIsGoodAtTheHead
    (head : P5J.AtMgA OnBytes.secondHashFunction files description proofRun publicPart places firstChain
      lookPlace)
    (Bk : ProverCoinCounts) (ownNoCoin : LookupsOwnNoCoin Bk publicPart) (ground : Ground)
    (F : Pub → Fill (Local W₀ Rc Inst Tr))
    (G : Sides (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain) Bk W₀ Rc Ky Tr X₀ X)
    (only : OnlyLookupsAtLookupPlaces G ((lookupSimulatorLot F).rows publicPart ground)) :
    LookupKindIsGood (P5J.F0T OnBytes.secondHashFunction publicPart places firstChain) Bk G :=
  have handsIn := lookupKindHandsIn head Bk ownNoCoin ground F G only
  ⟨handsIn.1, handsIn.2.1, handsIn.2.2⟩

/-- **The same at a value of `OnlineProverWithDescription`**, at its own description, book, public part and ground. -/
theorem lookupKindIsGoodAtAReturn
    (head : P5J.AtMgA OnBytes.secondHashFunction files description proofRun publicPart places firstChain
      lookPlace)
    (returned : OnlineProverWithDescription W₀ Rc Tr X₀ X) (samePublicPart : returned.Z = publicPart)
    (sameDescription : returned.F = P5J.F0T OnBytes.secondHashFunction publicPart places firstChain)
    (ownNoCoin : LookupsOwnNoCoin returned.B publicPart)
    (F : Pub → Fill (Local W₀ Rc Inst Tr)) (G : Sides returned.F returned.B W₀ Rc Ky Tr X₀ X)
    (only : ∀ L ∈ G.first, L.place.kind = KindName.K3 →
      L.bare ∈ (lookupSimulatorLot F).rows returned.Z returned.G) :
    LookupKindIsGood returned.F returned.B G := by
  obtain ⟨AZ, AG, AF, AB, AH, Areaders, Arows⟩ := returned
  dsimp only at ownNoCoin samePublicPart sameDescription G only ⊢
  subst samePublicPart sameDescription
  exact lookupKindIsGoodAtTheHead head AB ownNoCoin AG F G only

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.LookupKindIsGood
#print axioms ProofFile.Honest.K3.Term.lookupKindIsGoodAtTheHead
#print axioms ProofFile.Honest.K3.Term.lookupKindIsGoodAtAReturn
