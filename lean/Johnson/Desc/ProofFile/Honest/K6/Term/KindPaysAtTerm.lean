-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Term/KindPaysAtTerm.lean: THE OUTPUT HEAD's OWN ROUNDS (the kind K6
of the online proof): UNDER THE LIBRARY's HYPOTHESIS ON THE FIRST CHAIN, AND WHERE THE HONEST
PROVER's ONLINE MAKER RETURNS, THE KIND PAYS, in the form in which every kind states it
(Honest/K5/Law/KindPaysAtTerm.lean has the same statements for the kind K5), so that the payments of
all kinds can be joined alike.

WHAT IT IS NOT.
  * "A kind pays" (KindPays, Honest/Law/ReadyOfSides.lean) says that the frame's set-up routine
    chainSteps returns at the members at which the kind's sides stand. It does not say that a part
    plays, that a round is reached or that a verifier accepts.
  * The hypothesis (P5J.AtMgA: the full size and the format's second hash function alone) and "onlineMaker
    returns" (E2E/TheHonestProver.lean) are premises; in the last theorem the hypothesis gives way
    to three tests on the public files. That the maker returns is shown here at no files: where it
    does not, every theorem from kindPaysAtTheTerm on holds of nothing.
  * In the shared and the last chain the kind pays for want of sides: these two hold of nothing.
  * Nothing on soundness, completeness as a whole, or what a proof hides.

WHAT IT IS. No definition; eleven theorems.

  headPairIsTheOnlyOne     of the thirteen lots of the base filling the head's is the only one of
                           the kind K6. No premise
  headLotHasOneSide        under the hypothesis, at any return of the maker onlineProverFromPublicFiles, the filling a
                           letter: the head's lot lays one side: the row headRow at the kind's place
  kindPaysAtTheTerm        **every side of the kind in the first chain of the maker's prover pays**,
                           at the hypothesis's description. By the crossing that serves all kinds
                           (kindPays_online, Honest/Law/KindPaysOnline.lean)
  senderAtTheTerm          against emptiness: a member of the first chain stands at the kind's
                           place, and what a search of the prover's first chain finds first at that
                           place is the row, by name
  sideAtTheTerm            so a side of the kind stands in the prover's first chain, at a member's
                           place
  kindPaysAtTheReturn      the same payment at the description that the maker returned
  kindPaysAtTheFamily      and at the description that the online provers stand over
  kindPaysAtTheFramedProver   and at the prover that the online provers hand to the frame
  kindPaysShared, kindPaysLast   the two later chains, for want of sides
  paysWhereTheFilesPass    without the hypothesis: where the public files are in scope, can be read
                           and pass the library's test, at every return of the maker

CALLED. Of the kinds' common files: pair_only (Honest/Law/FillPairs.lean); kindPays_online,
kindPays_proverAt, online_desc_at_head, kindPays_online_shared_none, kindPays_online_second_none
(Honest/Law/KindPaysOnline.lean). Of this kind's: headRowPaysAtAnyBook
(Honest/K6/Term/BookLends.lean); sideAtTheFilling (Honest/K6/Term/SideAtFilling.lean);
headLot_through (Honest/K6/Term/RowThrough.lean); headLot_one_half (Honest/K6/Law/HalfAtSixKinds.lean);
k6_member_there (Honest/K6/Law/FrontScalars.lean). Of the library: head_ground_at_head,
atPure_at_laid_ground, atPure_at_laid, P5J.head_exists_at_name, P5J.owed_of_live.
-/
import Johnson.Desc.ProofFile.Honest.Law.KindPaysOnline
import Johnson.Desc.ProofFile.Honest.K6.Term.BookLends
import Johnson.P5J.HeadExistsAtName
import Johnson.Goal.Skeleton.OwedOfLive

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K6.Term
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain KindName)
open P5J (AtMgA TS F0T)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open ProofFile.Honest.Term (OnlineReturn onlineMaker matrixInput tableCoins onlineLot kindPays_online
  kindPays_proverAt online_desc_at_head kindPays_online_shared_none kindPays_online_second_none)

/-! ## 1 The head's lot -/

/-- **Of the thirteen lots of the base filling the head's is the only one of the kind K6.** No
premise. -/
theorem headPairIsTheOnlyOne {W₀ : Type} (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∀ M, (M, KindName.K6) ∈ fillPairs I o S O → M = headLotAt I.weights :=
  pair_only I o S O
    (show (headLotAt I.weights, KindName.K6) ∈ widerPairs I o S O from
      .tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.tail _ (.head _)))))))))
    (by decide)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : Pub} {Np : H2U.Places4}
  {cF : Chain TS Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The head's lot lays one side: the row, at the kind's place.** The filling and the reader of
the committed digits are letters. Two premises: the library's hypothesis on the first chain and "the
maker returns". -/
theorem headLotHasOneSide (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {W₀ Rc X₀ : Type}
    {P : OnlineProverParts W₀ Rc Cells X₀ Unit} {A : OnlineProverWithDescription W₀ Rc Cells X₀ Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) (weights : Pub → W₀ → Weights) :
    (headLotAt (Rc := Rc) weights).halves A.Z A.G =
      [⟨IM.k6Place, headRow (headWit' id (weights Zp) Zp A.G) (headNumbers Zp) IM.k6Place⟩] := by
  obtain ⟨G, ground⟩ := head_ground_at_head h
  obtain ⟨publicPart, sameGround, -⟩ := atPure_at_laid_ground h.laid ground hA
  rw [publicPart, sameGround]
  exact headLot_one_half h ground fun Z' G' => headWit' id (weights Zp) Z' G'

/-! ## 2 At the honest prover's online maker -/

/-- **The kind K6 pays at the maker's return**: every side of the kind in the first chain of the
maker's prover pays. It is not acceptance. Two premises: the library's hypothesis on the first chain
and "onlineMaker returns". -/
theorem kindPaysAtTheTerm (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) :
    KindPays A.B 0 (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder A.H.first KindName.K6 := by
  refine kindPays_online hA (L := headLotAt matrixInput.weights) (fun side isSide => ?_)
    (headPairIsTheOnlyOne _ _ _ _)
  have readThrough : onlineLot Z (headLotAt matrixInput.weights) =
      headLotAt fun Z' index => matrixInput.weights Z' (id index) :=
    headLot_through id (tableCoins Z) matrixInput.weights
  rw [readThrough, headLotHasOneSide h hA] at isSide
  rw [List.mem_singleton.1 isSide]
  exact headRowPaysAtAnyBook _ _ _ Z D r Zp Np cF x _ A _ h hA

/-- **Against emptiness: the kind's sender stands there, by name.** A member of the description's
first chain stands at the kind's place, and what a search at that place in the first chain of the
maker's prover finds first is the row. The same two premises. -/
theorem senderAtTheTerm (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) :
    (∃ member ∈ (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder, member.place = IM.k6Place) ∧
      A.H.first.find? (fun side => side.place == IM.k6Place) =
        some (headSide id matrixInput Zp A.G) :=
  ⟨k6_member_there h, (sideAtTheFilling h id (tableCoins Z) matrixInput.dummy matrixInput
    OnBytes.HonestTrace.Sz.ref openHonest hA).1⟩

/-- **So a side of the kind stands in the first chain of the maker's prover, at the place of a
member of the description's list.** The same two premises. -/
theorem sideAtTheTerm (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) :
    ∃ side ∈ A.H.first, ∃ member ∈ (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder,
      member.place = side.place ∧ side.place = IM.k6Place ∧ side.place.kind = KindName.K6 := by
  obtain ⟨⟨member, isMember, atPlace⟩, found⟩ := senderAtTheTerm h hA
  exact ⟨_, List.mem_of_find?_eq_some found, member, isMember, atPlace, rfl, rfl⟩

/-- **The same payment at the description that the maker returned.** The same two premises. -/
theorem kindPaysAtTheReturn (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) : KindPays A.B 0 A.F.first.blocksInOrder A.H.first KindName.K6 := by
  rw [(atPure_at_laid h.laid hA).2]
  exact kindPaysAtTheTerm h hA

/-- **At the description that the online provers stand over**: at the places and the first chain
that onlineProver reads off the maker's public part. The same two premises, and that these two are
read. -/
theorem kindPaysAtTheFamily (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) {places : H2U.Places4} {firstChain : Chain TS Cl}
    (placesRead : H2U.placesOfMade A.Z.made = .ok places)
    (chainRead : ProofFile.onlineFirstChainAt A.Z = .ok firstChain) :
    KindPays A.B 0 (descZ A.Z places firstChain).first.blocksInOrder A.H.first KindName.K6 := by
  rw [(online_desc_at_head h hA placesRead chainRead).1]
  exact kindPaysAtTheTerm h hA

/-- **At the prover that the online provers hand to the frame**: the maker's, read through a
committer, which leaves its first chain as it is. The same two premises. -/
theorem kindPaysAtTheFramedProver (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) {Seed Column : Type}
    (committer : Committer FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Seed Column Inst OnBytes.TableKey) (item : Nat) :
    KindPays A.B 0 (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder (committer.proverAt item A.H).first
      KindName.K6 :=
  kindPays_proverAt committer item (kindPaysAtTheTerm h hA)

/-- **The kind pays at the shared chain, for want of sides**: it holds of nothing. The same two
premises. -/
theorem kindPaysShared (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) : KindPays A.B 1 A.F.shared.blocksInOrder A.H.shared KindName.K6 :=
  kindPays_online_shared_none h hA (by decide)

/-- **The kind pays at the last chain, for want of sides**: it holds of nothing. One premise:
"onlineMaker returns". -/
theorem kindPaysLast {A : OnlineReturn Z} (hA : onlineMaker Z = .ok A) :
    KindPays A.B 2 A.F.second.blocksInOrder A.H.second KindName.K6 :=
  kindPays_online_second_none hA (by decide)

/-- **Without the hypothesis, at every return of the maker**: where the public files are in scope,
can be read and pass the library's test, the kind pays at the return, and a side of the kind stands
in the prover's first chain at a member's place. It is not acceptance. That the maker returns is a
premise and is not shown here. -/
theorem paysWhereTheFilesPass (Z : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (inScope : VerifierAndGoals.InScope Z = true) (read : VerifierAndGoals.readFiles Z = .ok pp)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) {A : OnlineReturn Z}
    (hA : onlineMaker Z = .ok A) :
    KindPays A.B 0 A.F.first.blocksInOrder A.H.first KindName.K6 ∧
      ∃ side ∈ A.H.first, ∃ member ∈ A.F.first.blocksInOrder,
        member.place = side.place ∧ side.place = IM.k6Place := by
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_exists_at_name Z inScope read live (P5J.owed_of_live live)
  refine ⟨kindPaysAtTheReturn h hA, ?_⟩
  rw [(atPure_at_laid h.laid hA).2]
  obtain ⟨side, isSide, member, isMember, samePlace, atPlace, -⟩ := sideAtTheTerm h hA
  exact ⟨side, isSide, member, isMember, samePlace, atPlace⟩

end ProofFile.Honest.K6.Term

#print axioms ProofFile.Honest.K6.Term.headPairIsTheOnlyOne
#print axioms ProofFile.Honest.K6.Term.headLotHasOneSide
#print axioms ProofFile.Honest.K6.Term.kindPaysAtTheTerm
#print axioms ProofFile.Honest.K6.Term.senderAtTheTerm
#print axioms ProofFile.Honest.K6.Term.sideAtTheTerm
#print axioms ProofFile.Honest.K6.Term.kindPaysAtTheReturn
#print axioms ProofFile.Honest.K6.Term.kindPaysAtTheFamily
#print axioms ProofFile.Honest.K6.Term.kindPaysAtTheFramedProver
#print axioms ProofFile.Honest.K6.Term.kindPaysShared
#print axioms ProofFile.Honest.K6.Term.kindPaysLast
#print axioms ProofFile.Honest.K6.Term.paysWhereTheFilesPass
