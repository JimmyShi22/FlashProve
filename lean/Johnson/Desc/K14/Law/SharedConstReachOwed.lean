-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstReachOwed.lean: A STATEMENT THAT IS OWED FOR K14's LAW, AS A
PROPOSITION BY def: NO PROOF HERE. The fold facts beside the shared table's constant
(Johnson/Desc/K14/Law/SharedConstFold.lean) come down, at a proof file's seat, to five facts on
EVERY REACHED LAST STATE OF THE FIRST CHAIN that bears no mark (Sh.foldFacts_at,
Johnson/Desc/K14/Law/SharedConstFar.lean; bookFacts_of_tests,
Johnson/Desc/K14/Law/BookFactsOfTests.lean). Here the five in one sentence, each as the test with
code or the equation in which another file's list of fold facts bears it.

  Sh.ReachOwed o Z N B' cF L     at every p with EndAt₁ (seatF o Z N B' cF) p, WHOSE PUBLIC INSTANCE
       IS A TYPED INSTANCE's (the constant's own R at the seat, both halves), and no mark:
       the book numbers its trees from 0 (K12.Door.atFirstBook 0) · the book fits (bookFitsB) · the
       book has as many places as the statement has messages · the statement's codes are the
       parameters' · the book's places are the first of the written list L's (atFirstSeats L)
  Sh.ReachInScopeOwed o    THE SENTENCE THAT IS OWED: ReachOwed for all letters THAT THE FILES TIE:
      in
      the
       goals' scope, where the written data are laid, at the Z, N, c of which the verifier makes its
       IOP as written in Lean, and at the list L that is laid of the first chain's own sendings at
       the first chain's codes. (At letters that nothing ties ReachOwed is false: any chain, any
       list.) THE SECOND HASH FUNCTION o IS A LETTER: other files' laws in scope stand at
       OnBytes.secondHashFunction alone: at another o the sentence stays owed.
What is not claimed. That it holds. Nothing on soundness.

-/
import Johnson.Desc.K14.Law.SharedConstOpenAt
import Johnson.Desc.K12.Door.DoorBools
import Johnson.Desc.Sound.BookTests
import Johnson.Desc.K12.Door.LaidAt
import Johnson.Loose.H2K12.DescN
import Johnson.Desc.Laid.ProofFullLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

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

open Johnson.Desc.First.Walk.Tied (EndAt₁)

namespace Sh

/-- OWED: the five facts at every reached last state of the first chain that bears no mark and whose
public part is a typed instance's. -/
def ReachOwed (o : ProofFile.SecondHashFunctionArgument) (Z : ProofFile.Pub) (N : H2U.Places4) (B' : ProofFile.SecondSeat)
    (cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl)
    (L : VerifiableInference.Desc.K12.Door.Laid) : Prop :=
  ∀ p : ProofFile.InstPub × First.S, EndAt₁ (seatF o Z N B' cF) p →
    (∃ z : LPFD.Full.XF × RecFull, p.1 = (LPFD.Full.instanceAsPlainRecord z).pub) → p.2.failed = none →
    VerifiableInference.Desc.K12.Door.atFirstBook 0 p.2 = true ∧ bookFitsB p.2.book = true ∧
      p.2.book.place.size = p.2.st.oracles.size ∧
      p.2.st.codes = (planAt Z N (seatF o Z N B' cF)).Q.codes ∧
      VerifiableInference.Desc.K12.Door.atFirstSeats L p.2 = true

/-- **OWED**: the five facts, at the letters that the files tie. -/
def ReachInScopeOwed (o : ProofFile.SecondHashFunctionArgument) : Prop :=
  ∀ (S : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF)
    (Z : ProofFile.Pub) (N : H2U.Places4) (c : VerifiableInference.Desc.Chain First.S ProofFile.Cl)
    (L : VerifiableInference.Desc.K12.Door.Laid), VerifierAndGoals.InScope S = true →
    LPFD.Full.proofDataAndDecisionOfPublicFiles o S.pol S.lay S.KL = .ok (D, r) →
    ProofFile.onlineDescription o S.pol S.lay S.KL =
      .ok (H2K.JointK.descN o ProofFile.pureRoad.links guardedProximityTestParts Z N c) →
    ProofFile.pureRoad.pub o S.pol S.lay S.KL = .ok Z → H2U.placesOfMade Z.made = .ok N →
    VerifiableInference.Desc.K12.Door.laidAtCodes Z.first.codes Z.made.proof.1 = some L →
    ReachOwed o Z N (H2K.JointK.secondN guardedProximityTestParts Z N) c L

end Sh

end Desc.K14.Law
