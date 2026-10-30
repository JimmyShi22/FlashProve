-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/IndexLotAtHeadStatement.lean: UNDER THE LIBRARY's HEAD, THE
KIND's SECOND LOT, AT THE VERY LETTERS AT WHICH `IndexTieOfOwn` (IndexTieOfOwnStatement.lean of this
folder) TAKES IT (but for ch: a letter here, the head's thread's chain there), AND THE WHOLE-MESSAGE
TEXT OF MESSAGE NUMBER 4 OF THE OPENING's SENDING (`K1.msgTxt`, Honest/K1/ScriptLots.lean, a file
that is not in this library) ANSWER ALIKE WHEREVER BOTH ANSWER, UNDER ONE
PUBLIC TEST ON THE BOOK AT WRITTEN NUMBERS. A STATEMENT ALONE: one definition of a proposition; no
definition of another kind. NOTHING IS PROVED IN THIS FILE, and it is none of the library's goals: a
lemma's statement.

  `IndexLotAgreesAtHead`  the head · the opening · TWO EQUATIONS ON THE JOB J: its numbers are the
                          opening's at the description's own ground (`K1.firstPar`), its rides those
                          of the opening's fold (`K1.rideOf`, `K1.firstFold`,
                          Honest/K1/PlaceJob.lean): the job that `K1.lotHalves` (there) lays at the
                          first place meets both by its text · the test `entryRunIs`
                          (Honest/Small/EntryRunIs.lean): the book's second spending entry for
                          ⟨`IM.k11Place`, 1⟩ has the owner ⟨⟨1, some 0, 1, K1⟩, 0⟩, the start 8659
                          in the extension field and the count 1. Then: wherever the lot and the
                          text both answer, they answer alike

THE NUMBERS. 8659 is 8647 + 12: where the entries of message 4's mask row begin among the sender's
own elements, and how many segments in front of segment 24 leave a row. The first is had in
IndexKeyWritten.lean of this folder, the second in another group of authors' `indexTakes_head`
(Honest/K4/Law/W/IndexTakes.lean; this library may not hold it).

WHAT IT IS NOT. That any book passes the test is not said. That a Script's message of the lot's
number is that text is not said: it is `OwnMsgs` at the sender's lot. Other kinds spend of the same
message: that the merge's one entry is no other part's is the book's own test
(LotsOnceStatement.lean of this folder draws it from the frame's authors' law). ONE LETTER ch STANDS
FOR THE SPENDER's CHAIN AND THE SENDER's. The count in the test is idle here. No lot is laid.

Limits. The full size and the format's second hash function, as the head has them. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.IndexLotKeyStatement
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob
import Johnson.Desc.ProofFile.Honest.K4.Lot.IndexNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.FillP1 (fvsAt)
open Johnson.Desc.First.Walk.Tied (rowsBefore)
open ProofFile.Honest.K1 (SendJob msgTxt)
open ProofFile.Honest.K4.Lot (k4IndexRows k4IndexNum)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

/-- **The statement.** Not proved here; a lemma's statement, none of the library's goals. -/
def IndexLotAgreesAtHead : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : OnBytes.Maker.WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub)
    (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) (x : First.Look.Place) (Bs : ProofFile.PureBase)
    (base : List (Block S ProofFile.Cl)) (_ : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (_ : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (Bk : ProverCoinCounts) (W₀ Rc Tr X : Type) (ch : Nat)
    (claims : ProofFile.Inst → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (W Y : Type)
    (wit : Local W₀ Rc ProofFile.Inst Tr → W) (J : SendJob W Y) (own₀ : Y) (sf : Nat),
    J.P = K1.firstPar Bs.G₀.first (K1.gpOf Zp) → J.ride = K1.rideOf (K1.firstFold Bs.G₀.first) →
    entryRunIs (spentE Bk ⟨IM.k11Place, 1⟩) 1 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ ⟨sf, 8659⟩ ⟨0, 1⟩ = true →
    ∀ k w hd hd' mask row place y y',
      (k11IndexLot Bk (Rc := Rc) (Tr := Tr) X ch IM.k11Place (_root_.K11.parOf Zp Bs.G₀) claims
        weights (k4IndexNum Zp) (rowsBefore (fvsAt Zp) 24 % k4IndexRows Zp)
        (rowsBefore (fvsAt Zp) 24 / k4IndexRows Zp)).txt k w hd mask row place = some y →
      msgTxt ch wit J own₀ 4 k w hd' mask row place = some y' → y' = y

end ProofFile.Honest.K11
