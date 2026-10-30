-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstFoldAt.lean: THE FOLD FACTS BESIDE THE SHARED TABLE's CONSTANT, AT A
PROOF FILE's SEAT, FROM ONE OWED SENTENCE AND FIVE CLOSED TESTS. A composition: no proof of its own.

  Sh.foldFacts_of_owed₀   ReachOwed … L → TestsFar … L → FoldFacts (planAt …) (openAt₀ …)
  Sh.foldFacts_of_owed    the same at Sh.openAt (the cells' three at the release's configuration's)
HOW. Sh.foldFacts_at (Johnson/Desc/K14/Law/SharedConstFar.lean) called; its first two premises by
bookFacts_of_tests (Johnson/Desc/K14/Law/BookFactsOfTests.lean).
WHAT IS NOT HERE. No law. ReachOwed (Johnson/Desc/K14/Law/SharedConstReachOwed.lean: a Prop by def).
That the five tests accept.
What is not claimed. No soundness of a verifier; no level.

-/
import Johnson.Desc.K14.Law.SharedConstFar
import Johnson.Desc.K14.Law.SharedConstReachOwed
import Johnson.Desc.K14.Law.SharedConstHeldAt
import Johnson.Desc.K14.Law.BookFactsOfTests

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open OnBytes.Means (Words wordsOn)
open Johnson.Pack
open _root_.Run.PQ (CK)
open Cb Cb.Ood Blocks Cb.Pv Cb.Pv.Lin Cb.Bridge
open VerifiableInference.Desc (Block Strs Wit FileDescription First.S Grows)
open VerifiableInference.Desc.ChainEnd (untestedL Exact)
open VerifiableInference.Desc.K1 (sendPiece sampledAt shapeAt shapesOf condPort errPort seedEntry
  seedMaps)
open VerifiableInference.Desc.First (Meaning Numbers ModelPart Pub pubSets openSets start)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu Seat.onGomega)
open VerifiableInference.Desc.K12.Coin
open Desc.K14.Law.Fence
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0 PayPub)
open H2K.First (batOneOk)
open VerifiableInference.Desc.K13.Law (EvalAt laidOf wSitsItem wSitsMore)
open VerifiableInference.Desc.Third (P₁₄)

open VerifiableInference.OnPublicFiles (kcReq)

namespace Sh

variable {Cells Tok : Type} (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4)
  (B' : ProofFile.SecondSeat) (cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl)
  (L : VerifiableInference.Desc.K12.Door.Laid)

/-- **FoldFacts at the seat, from the one owed sentence and the five closed tests.** -/
theorem foldFacts_of_owed₀ (c₀ : Cells) (matC : Cells → Nat → Nat → GE)
    (held : ((ixOf2 (planAt Z N (seatF o Z N B' cF)).Q.par.S.fold 0 2852142980 (rankLib (planAt Z N
        (seatF o Z N B' cF)).Q.par.S.fold)).Row × Fin (planAt Z N (seatF o Z N B'
        cF)).Q.par.S.fold.index.code.ell → GE) → Option Cells)
    (O₁ : Open₁ Cells Tok (planAt Z N (seatF o Z N B' cF)).Q) (hR : ReachOwed o Z N B' cF L) (hF :
        TestsFar o Z N B' cF L) :
    FoldFacts (planAt Z N (seatF o Z N B' cF)) (openAt₀ o Z N B' cF c₀ matC held O₁) :=
  foldFacts_at o Z N B' cF c₀ matC held O₁ L hF
    (fun p hr hz hm => (VerifiableInference.Desc.K14.Law.bookFacts_of_tests p.2 (hR p hr hz hm).1
      (hR p hr hz hm).2.1 (hR p hr hz hm).2.2.1).1)
    (fun p hr hz hm => (VerifiableInference.Desc.K14.Law.bookFacts_of_tests p.2 (hR p hr hz hm).1
      (hR p hr hz hm).2.1 (hR p hr hz hm).2.2.1).2)
    (fun p hr hz hm => (hR p hr hz hm).2.2.2.1) (fun p hr hz hm => (hR p hr hz hm).2.2.2.2)

/-- The same at Sh.openAt. -/
theorem foldFacts_of_owed (hfs : fullShapeB (planAt Z N (seatF o Z N B' cF)).Q.par.S = true) (pp :
    Inst.Model.ScalesAndPolicy)
    (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) numsFull pp))
    (O₁ : Open₁ (kcReq numsFull pp E).conf.I Tok (planAt Z N (seatF o Z N B' cF)).Q)
    (hR : ReachOwed o Z N B' cF L) (hF : TestsFar o Z N B' cF L) :
    FoldFacts (planAt Z N (seatF o Z N B' cF)) (openAt o Z N B' cF hfs pp E O₁) :=
  foldFacts_of_owed₀ o Z N B' cF L _ _ _ O₁ hR hF

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.foldFacts_of_owed₀
#print axioms Desc.K14.Law.Sh.foldFacts_of_owed
