-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerSharedJointCountClosed.lean: k14_shared_joint_count
(Johnson/Desc/K14/Law/LedgerSharedJointCount.lean: THE FORM of the field shared_joint_count at
plTablesR's own second places, THE DATA AT DP.at frS.P.T.a OUTRIGHT, slots := 2 ^ depthReq, links :=
P5J.fullLinks) WITH ITS LETTERS N₁ | Mg₁ (the structure's Nn | MQ) LAID AT P5J.At.N Zp cF |
P5J.mgAtAll hAtMgA, AND smp₁ · ms₁ · Tok · pp · E AT P5J.At.*'s TERMS; THE SAME PAYERS CALLED AS IN
k14_field_e_closed, AT THAT DATA. It is not itself the field that the proof file's top
spends: that field's meaning is spelled MQ, which is one theorem away from mgAtAll (mgAt_is_mq), not
one unfolding. The join is made in Johnson/Desc/K14/Law/LedgerAtFree.lean (k14_at_free).
BY THE FILE's OWN LINES: OF
k14_shared_joint_count's SIXTEEN PREMISES FOURTEEN ARE STRUCK AND TWO COME IN: PAID (A LEAN TERM):
SEVEN (hI hV h3 hO hJ hRd hFar) · TRADED, NOT DISCHARGED: TWO (hpinS · hpinF: projections of ONE
STRONGER test, madePinnedAt, which comes in. It follows from the yes of one of the proof file's
entry tests, madeRow (Johnson/Desc/Laid/ProofAsks.lean), by PlanWritten.pinnedAt_of_row
(Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean); P5J.pins_of_laid makes that call) · MOVED INTO
hAtMgA: FIVE (hZs hlaid hpub hNp hdesc) · STAND: hn · hR. A COUNT OF NAMES IS NO MEASURE: hAtMgA
IS 21 FIELDS UNDER ONE NAME. A LETTER LAID: Ld := LFull: its tie to the files («laidAtCodes … =
some LFull») is no binder here; if LFull were not that list hR would be false at the honest run and
this theorem idle; its payers lie (laid_written · laid_in_scope, under the pin): not called here.

THE STATEMENT IS MADE BY PROGRAM: k14_shared_joint_count's own binders, in its own words, with the
letters of the maps laid in and the paid premises struck. THE PROOF: the lines in front, then ONE
CALL of k14_shared_joint_count by named arguments.
LETTERS LAID (8): Tok · pp · E · N₁ · ms₁ · smp₁ · Mg₁ · Ld.
PREMISES STRUCK (14): hZs · hpub · hNp · hdesc · hlaid · h3 · hRd · hFar · hI · hV · hJ · hO · hpinS
· hpinF.
LETTERS THAT FALL, BOUND BY THE LINES IN FRONT OF THE CALL (0): none.
LETTERS AND PREMISES THAT COME IN (3): xLook · hAtMgA · hMadePinnedP1.
What is not claimed. EVERY BINDER THAT STANDS IS A PREMISE OR A LETTER. That the premises can
be met together: NO MEMBER IS SHOWN. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.LedgerSharedJointCount
import Johnson.P5J.LettersAt
import Johnson.P5J.DecFree
import Johnson.P5J.MgAtAll
import Johnson.Desc.K14.Law.SharedConstCodesAt
import Johnson.Flat.Last.WSitsOpenAtAll
import Johnson.Desc.K14.Law.LedgerReadsAll
import Johnson.Desc.K14.Law.SharedConstFarPaid
import Johnson.Desc.K14.Law.LedgerMap16
import Johnson.Desc.AtSeats.ShJointAtAll
import Johnson.Desc.K14.Law.LedgerMap16b
import Johnson.Desc.K14.Law.LedgerMap16c
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws
import Johnson.Desc.AtSeats.ShHWAtAll
import Johnson.Desc.AtSeats.ShCodesOfRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law
open VerifiableInference.Desc.Sound (LettersReadBelow ocEndReadsBelow pinJT)
open VerifiableInference.Desc.K13.Law (WRow evalLaidB wSitsB wSeatB wSitsItem)
open OnBytes.Means (wordsOn)
open VerifiableInference.Desc (Strs)
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


/-- **The form of the field RowsTiedR.shared_joint_count, its Nn | MQ as letters laid at At.N | mgAtAll, with the payers called.** -/
theorem k14_shared_joint_count_closed
    (rdNA : ℕ → ℕ)
    (rdNB : ℕ → ℕ)
    (Zp : ProofFile.Pub)
    (cF : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl)
    (oL : ProofFile.SecondHashFunctionArgument)
    (Zs : VerifierAndGoals.PublicFiles)
    (rP : LPFD.Full.RunPF)
    (Np : H2U.Places4)
    (dW :
        (Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
              (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs)).conf.I)
          P5J.At.Tok MsgT))
    (wEnd :
        (Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
              (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs)).conf.I)
          P5J.At.Tok MsgT))
    (hR : Desc.K14.Law.Sh.ReachOwed oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
        VerifiableInference.Desc.K13.Law.LFull)
    (DP : WholeD)
    (e₁ : (i : ℕ) → (ds : List RDT) →
        ((gS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
            ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
            ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
            ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np).XiPub
          ×
          (gS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
            ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
            ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
            ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np).S₁)
        × (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₁ 0).E.Str →
        Iop.Tr (uLT (ckP .two) ds) →
        (Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
              (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs)).conf.I)
          P5J.At.Tok MsgT)
        →
        (Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
              (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs)).conf.I)
          P5J.At.Tok MsgT))
    (e₂ : (i : ℕ) → (ds : List RDT) →
        (((gS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np).XiPub
            ×
            (gS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np).S₁)
          ×
          (gS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
            ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
            ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
            ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np).S₂)
        × (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₂ 0).E.Str →
        Iop.Tr (uLT (ckP .two) ds) →
        (Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
              (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs)).conf.I)
          P5J.At.Tok MsgT)
        →
        (Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
              (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs)).conf.I)
          P5J.At.Tok MsgT))
    (e₃ : (i : ℕ) → (ds : List RDT) →
        (((gS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np).XiPub
            ×
            (gS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np).S₁
            ×
            (gS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np).S₂)
          ×
          (gS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
            ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
            ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
            ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np).S₃)
        ×
        (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₃
          (gS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
            ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
            ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst)
            ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns)
            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
            Np).lastChainFirstTreeNumber).E.Str
        → Iop.Tr (uLT (ckP .two) ds) →
        (Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
              (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs)).conf.I)
          P5J.At.Tok MsgT)
        →
        (Wit
          ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
              (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs)).conf.I)
          P5J.At.Tok MsgT))
    (depthReq : ℕ)
    (hn : (2 ^ depthReq) ≤ 64)
    (xLook : VerifiableInference.Desc.First.Look.Place)
    (hAtMgA : P5J.AtMgA oL Zs (DP.at frS.P.T.a) rP Zp Np cF xLook)
    (hMadePinnedP1 : VerifiableInference.PlanWritten.madePinnedAt Zp.p.X.P Zp.p.chains.made
        Zp.first Zp.made = true) :
    ∀ MgS ML PLm, EachLawsBN
      (keyAt Prod.snd (DP.at frS.P.T.a).t₁
        (atDesc
          (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
            (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (piecesAt (ckP .two)
            (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
              (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (DP.at frS.P.T.a)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.first.asBare)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.front.map
              VerifiableInference.Desc.Block.asBare ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.links.flatMap
              VerifiableInference.Desc.Link.blocksInOrder ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.back.map
              VerifiableInference.Desc.Block.asBare ++
              [(fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.last.asBare])
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.first.asBare)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.front.map
              VerifiableInference.Desc.Block.asBare ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.links.flatMap
              VerifiableInference.Desc.Link.blocksInOrder ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.back.map
              VerifiableInference.Desc.Block.asBare ++
              [(fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.last.asBare])
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.first.asBare)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.front.map
              VerifiableInference.Desc.Block.asBare ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.links.flatMap
              VerifiableInference.Desc.Link.blocksInOrder ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.back.map
              VerifiableInference.Desc.Block.asBare ++
              [(fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.last.asBare])
            (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂
        (atDesc
          (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
            (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (piecesAt (ckP .two)
            (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
              (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (DP.at frS.P.T.a)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.first.asBare)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.front.map
              VerifiableInference.Desc.Block.asBare ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.links.flatMap
              VerifiableInference.Desc.Link.blocksInOrder ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.back.map
              VerifiableInference.Desc.Block.asBare ++
              [(fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.last.asBare])
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.first.asBare)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.front.map
              VerifiableInference.Desc.Block.asBare ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.links.flatMap
              VerifiableInference.Desc.Link.blocksInOrder ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.back.map
              VerifiableInference.Desc.Block.asBare ++
              [(fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.last.asBare])
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.first.asBare)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.front.map
              VerifiableInference.Desc.Block.asBare ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.links.flatMap
              VerifiableInference.Desc.Link.blocksInOrder ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.back.map
              VerifiableInference.Desc.Block.asBare ++
              [(fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.last.asBare])
            (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).l₂)
      (P5J.plTablesR
        (atDesc
          (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
            (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (piecesAt (ckP .two)
            (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
              (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (DP.at frS.P.T.a)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.first.asBare)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.front.map
              VerifiableInference.Desc.Block.asBare ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.links.flatMap
              VerifiableInference.Desc.Link.blocksInOrder ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.back.map
              VerifiableInference.Desc.Block.asBare ++
              [(fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.last.asBare])
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.first.asBare)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.front.map
              VerifiableInference.Desc.Block.asBare ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.links.flatMap
              VerifiableInference.Desc.Link.blocksInOrder ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.back.map
              VerifiableInference.Desc.Block.asBare ++
              [(fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.last.asBare])
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.first.asBare)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.front.map
              VerifiableInference.Desc.Block.asBare ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.links.flatMap
              VerifiableInference.Desc.Link.blocksInOrder ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.back.map
              VerifiableInference.Desc.Block.asBare ++
              [(fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.last.asBare])
            (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd))
        ((fun a => (a.1, a.2))) (P5J.At.N Zp cF) (P5J.mgAtAll hAtMgA) P5J.fullLinks
        ((VerifiableInference.Desc.First.flatPlaces true P5J.fullLinks true))
        ((Desc.K14.Law.Fence.numbersSh
            (Desc.K14.Law.Sh.t₁
              (Desc.K14.Law.ShPlan.mk
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                  Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np))
                (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                  Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
                (Desc.K14.Law.rad2At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (Desc.K14.Law.rad5At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                Johnson.G.dryProofFull.2.1 2))
            (Desc.K14.Law.Sh.layU
              (Desc.K14.Law.ShPlan.mk
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                  Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np))
                (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                  Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
                (Desc.K14.Law.rad2At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (Desc.K14.Law.rad5At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                Johnson.G.dryProofFull.2.1 2))
            (Desc.K14.Law.Sh.layO
              (Desc.K14.Law.ShPlan.mk
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                  Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np))
                (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                  Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
                (Desc.K14.Law.rad2At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (Desc.K14.Law.rad5At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                Johnson.G.dryProofFull.2.1 2))
            (0, 0) (0, 0)))
        MgS ML
        (Desc.K14.Law.Sh.pm
          (Desc.K14.Law.ShPlan.mk (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
              (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
              Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
            (Desc.K14.Law.rad2At 2
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
            (Desc.K14.Law.rad5At 2
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
            Johnson.G.dryProofFull.2.1 2)
          (Desc.K14.Law.ShOpen.mk (P₀ := ProofFile.InstPub)
            (P₁ := ProofFile.InstPub × VerifiableInference.Desc.First.S)
            (Cells :=
              ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                  (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                  (P5J.At.EAt Zs)).conf.I))
            (Tok := P5J.At.Tok)
            (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
            (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
            ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                  Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)))
              ▸ P5J.At.smp Zp)
            (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.fullLinks (P5J.mgAtAll hAtMgA)
            (VerifiableInference.Desc.K13.whereOf Zp)
            ((Desc.K14.Law.Sh.openAt₀
                (Cells :=
                  ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                      (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                      (P5J.At.EAt Zs)).conf.I))
                (Tok := P5J.At.Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                (fun _ _ => 0)
                (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                (Desc.K14.Law.heldFull
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                  (Desc.K14.Law.full_index
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                    (Desc.K14.Law.full_of_shape map14_hx
                      (Desc.K14.Law.written_in_scope hAtMgA.scope
                        hAtMgA.laid.pub
                        (VerifiableInference.PlanWritten.sized_of_made
                          hMadePinnedP1)
                        (VerifiableInference.PlanWritten.first_of_made
                          hMadePinnedP1)
                        (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                          hAtMgA.laid.value hAtMgA.laid.planOk
                          hAtMgA.laid.data hAtMgA.laid.asks)
                        map14_hx).shape))
                  OnBytes.Flat.numsFull
                  (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs))
                ⟨(P5J.At.N Zp cF), P5J.fullLinks, (P5J.mgAtAll hAtMgA),
                  ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                      (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                      (fieldF oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                        (ProofFile.startS Zp) cF Zp.p.chains
                        (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                        (VerifiableInference.Desc.K12.Seat.tests Np)))
                    ▸ P5J.At.smp Zp),
                  (P5J.At.ms Zp Zs.lay)⟩).R)
            (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
            (Desc.K14.Law.heldFull
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
              (Desc.K14.p14Of Zp.p.chains
                (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
              (Desc.K14.Law.full_index
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                (Desc.K14.Law.full_of_shape map14_hx
                  (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                    (VerifiableInference.PlanWritten.sized_of_made hMadePinnedP1)
                    (VerifiableInference.PlanWritten.first_of_made hMadePinnedP1)
                    (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                      hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                    map14_hx).shape))
              OnBytes.Flat.numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
              (P5J.At.EAt Zs))))
        PLm true
        (stepAt
          (Desc.K14.Law.Sh.nums
            (Desc.K14.Law.ShPlan.mk
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np))
              (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
              (Desc.K14.Law.rad2At 2
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (Desc.K14.Law.rad5At 2
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              Johnson.G.dryProofFull.2.1 2)
            (Desc.K14.Law.ShOpen.mk (P₀ := ProofFile.InstPub)
              (P₁ := ProofFile.InstPub × VerifiableInference.Desc.First.S)
              (Cells :=
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs)).conf.I))
              (Tok := P5J.At.Tok)
              (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
              ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                  (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                  (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                    Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)))
                ▸ P5J.At.smp Zp)
              (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.fullLinks (P5J.mgAtAll hAtMgA)
              (VerifiableInference.Desc.K13.whereOf Zp)
              ((Desc.K14.Law.Sh.openAt₀
                  (Cells :=
                    ((VerifiableInference.OnPublicFiles.kcReq
                        OnBytes.Flat.numsFull
                        (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                        (P5J.At.EAt Zs)).conf.I))
                  (Tok := P5J.At.Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                  (fun _ _ => 0)
                  (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                  (Desc.K14.Law.heldFull
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                    (Desc.K14.Law.full_index
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                      (Desc.K14.Law.full_of_shape map14_hx
                        (Desc.K14.Law.written_in_scope hAtMgA.scope
                          hAtMgA.laid.pub
                          (VerifiableInference.PlanWritten.sized_of_made
                            hMadePinnedP1)
                          (VerifiableInference.PlanWritten.first_of_made
                            hMadePinnedP1)
                          (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                            hAtMgA.laid.value hAtMgA.laid.planOk
                            hAtMgA.laid.data hAtMgA.laid.asks)
                          map14_hx).shape))
                    OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs))
                  ⟨(P5J.At.N Zp cF), P5J.fullLinks, (P5J.mgAtAll hAtMgA),
                    ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                        (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                        (fieldF oL ProofFile.pureRoad.links Zp
                          ((H2K.JointK.sharedN Zp Np).lot)
                          ((H2K.JointK.sharedN Zp Np).start)
                          ((H2K.JointK.sharedN Zp Np).ended)
                          ((H2K.JointK.sharedN Zp Np).okInst)
                          ((H2K.JointK.sharedN Zp Np).fileOk)
                          ((H2K.JointK.sharedN Zp Np).standIns)
                          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                          (ProofFile.startS Zp) cF Zp.p.chains
                          (Desc.K14.p14Of Zp.p.chains
                            (Desc.K14.beforePointOf Np))
                          (VerifiableInference.Desc.K12.Seat.tests Np)))
                      ▸ P5J.At.smp Zp),
                    (P5J.At.ms Zp Zs.lay)⟩).R)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                      (VerifiableInference.PlanWritten.sized_of_made
                        hMadePinnedP1)
                      (VerifiableInference.PlanWritten.first_of_made
                        hMadePinnedP1)
                      (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                        hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                      map14_hx).shape))
                OnBytes.Flat.numsFull
                (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs))))
          (Desc.K14.Law.Sh.mg
            (Desc.K14.Law.ShPlan.mk
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np))
              (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
              (Desc.K14.Law.rad2At 2
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (Desc.K14.Law.rad5At 2
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              Johnson.G.dryProofFull.2.1 2)
            (Desc.K14.Law.ShOpen.mk (P₀ := ProofFile.InstPub)
              (P₁ := ProofFile.InstPub × VerifiableInference.Desc.First.S)
              (Cells :=
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs)).conf.I))
              (Tok := P5J.At.Tok)
              (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
              ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                  (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                  (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                    Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)))
                ▸ P5J.At.smp Zp)
              (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.fullLinks (P5J.mgAtAll hAtMgA)
              (VerifiableInference.Desc.K13.whereOf Zp)
              ((Desc.K14.Law.Sh.openAt₀
                  (Cells :=
                    ((VerifiableInference.OnPublicFiles.kcReq
                        OnBytes.Flat.numsFull
                        (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                        (P5J.At.EAt Zs)).conf.I))
                  (Tok := P5J.At.Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                  (fun _ _ => 0)
                  (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                  (Desc.K14.Law.heldFull
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                    (Desc.K14.Law.full_index
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                      (Desc.K14.Law.full_of_shape map14_hx
                        (Desc.K14.Law.written_in_scope hAtMgA.scope
                          hAtMgA.laid.pub
                          (VerifiableInference.PlanWritten.sized_of_made
                            hMadePinnedP1)
                          (VerifiableInference.PlanWritten.first_of_made
                            hMadePinnedP1)
                          (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                            hAtMgA.laid.value hAtMgA.laid.planOk
                            hAtMgA.laid.data hAtMgA.laid.asks)
                          map14_hx).shape))
                    OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs))
                  ⟨(P5J.At.N Zp cF), P5J.fullLinks, (P5J.mgAtAll hAtMgA),
                    ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                        (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                        (fieldF oL ProofFile.pureRoad.links Zp
                          ((H2K.JointK.sharedN Zp Np).lot)
                          ((H2K.JointK.sharedN Zp Np).start)
                          ((H2K.JointK.sharedN Zp Np).ended)
                          ((H2K.JointK.sharedN Zp Np).okInst)
                          ((H2K.JointK.sharedN Zp Np).fileOk)
                          ((H2K.JointK.sharedN Zp Np).standIns)
                          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                          (ProofFile.startS Zp) cF Zp.p.chains
                          (Desc.K14.p14Of Zp.p.chains
                            (Desc.K14.beforePointOf Np))
                          (VerifiableInference.Desc.K12.Seat.tests Np)))
                      ▸ P5J.At.smp Zp),
                    (P5J.At.ms Zp Zs.lay)⟩).R)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                      (VerifiableInference.PlanWritten.sized_of_made
                        hMadePinnedP1)
                      (VerifiableInference.PlanWritten.first_of_made
                        hMadePinnedP1)
                      (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                        hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                      map14_hx).shape))
                OnBytes.Flat.numsFull
                (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs))))
          (Desc.K14.Law.Sh.pm
            (Desc.K14.Law.ShPlan.mk
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np))
              (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
              (Desc.K14.Law.rad2At 2
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (Desc.K14.Law.rad5At 2
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              Johnson.G.dryProofFull.2.1 2)
            (Desc.K14.Law.ShOpen.mk (P₀ := ProofFile.InstPub)
              (P₁ := ProofFile.InstPub × VerifiableInference.Desc.First.S)
              (Cells :=
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs)).conf.I))
              (Tok := P5J.At.Tok)
              (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
              ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                  (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                  (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                    Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)))
                ▸ P5J.At.smp Zp)
              (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.fullLinks (P5J.mgAtAll hAtMgA)
              (VerifiableInference.Desc.K13.whereOf Zp)
              ((Desc.K14.Law.Sh.openAt₀
                  (Cells :=
                    ((VerifiableInference.OnPublicFiles.kcReq
                        OnBytes.Flat.numsFull
                        (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                        (P5J.At.EAt Zs)).conf.I))
                  (Tok := P5J.At.Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                  (fun _ _ => 0)
                  (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                  (Desc.K14.Law.heldFull
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                    (Desc.K14.Law.full_index
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                      (Desc.K14.Law.full_of_shape map14_hx
                        (Desc.K14.Law.written_in_scope hAtMgA.scope
                          hAtMgA.laid.pub
                          (VerifiableInference.PlanWritten.sized_of_made
                            hMadePinnedP1)
                          (VerifiableInference.PlanWritten.first_of_made
                            hMadePinnedP1)
                          (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                            hAtMgA.laid.value hAtMgA.laid.planOk
                            hAtMgA.laid.data hAtMgA.laid.asks)
                          map14_hx).shape))
                    OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs))
                  ⟨(P5J.At.N Zp cF), P5J.fullLinks, (P5J.mgAtAll hAtMgA),
                    ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                        (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                        (fieldF oL ProofFile.pureRoad.links Zp
                          ((H2K.JointK.sharedN Zp Np).lot)
                          ((H2K.JointK.sharedN Zp Np).start)
                          ((H2K.JointK.sharedN Zp Np).ended)
                          ((H2K.JointK.sharedN Zp Np).okInst)
                          ((H2K.JointK.sharedN Zp Np).fileOk)
                          ((H2K.JointK.sharedN Zp Np).standIns)
                          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                          (ProofFile.startS Zp) cF Zp.p.chains
                          (Desc.K14.p14Of Zp.p.chains
                            (Desc.K14.beforePointOf Np))
                          (VerifiableInference.Desc.K12.Seat.tests Np)))
                      ▸ P5J.At.smp Zp),
                    (P5J.At.ms Zp Zs.lay)⟩).R)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                      (VerifiableInference.PlanWritten.sized_of_made
                        hMadePinnedP1)
                      (VerifiableInference.PlanWritten.first_of_made
                        hMadePinnedP1)
                      (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                        hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                      map14_hx).shape))
                OnBytes.Flat.numsFull
                (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs))))
          (Desc.K14.Law.Sh.own
            (Desc.K14.Law.ShPlan.mk
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np))
              (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
              (Desc.K14.Law.rad2At 2
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (Desc.K14.Law.rad5At 2
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              Johnson.G.dryProofFull.2.1 2)
            (Desc.K14.Law.ShOpen.mk (P₀ := ProofFile.InstPub)
              (P₁ := ProofFile.InstPub × VerifiableInference.Desc.First.S)
              (Cells :=
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs)).conf.I))
              (Tok := P5J.At.Tok)
              (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
              ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                  (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                  (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                    Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)))
                ▸ P5J.At.smp Zp)
              (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.fullLinks (P5J.mgAtAll hAtMgA)
              (VerifiableInference.Desc.K13.whereOf Zp)
              ((Desc.K14.Law.Sh.openAt₀
                  (Cells :=
                    ((VerifiableInference.OnPublicFiles.kcReq
                        OnBytes.Flat.numsFull
                        (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                        (P5J.At.EAt Zs)).conf.I))
                  (Tok := P5J.At.Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                  (fun _ _ => 0)
                  (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                  (Desc.K14.Law.heldFull
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                    (Desc.K14.Law.full_index
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                      (Desc.K14.Law.full_of_shape map14_hx
                        (Desc.K14.Law.written_in_scope hAtMgA.scope
                          hAtMgA.laid.pub
                          (VerifiableInference.PlanWritten.sized_of_made
                            hMadePinnedP1)
                          (VerifiableInference.PlanWritten.first_of_made
                            hMadePinnedP1)
                          (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                            hAtMgA.laid.value hAtMgA.laid.planOk
                            hAtMgA.laid.data hAtMgA.laid.asks)
                          map14_hx).shape))
                    OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs))
                  ⟨(P5J.At.N Zp cF), P5J.fullLinks, (P5J.mgAtAll hAtMgA),
                    ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                        (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                        (fieldF oL ProofFile.pureRoad.links Zp
                          ((H2K.JointK.sharedN Zp Np).lot)
                          ((H2K.JointK.sharedN Zp Np).start)
                          ((H2K.JointK.sharedN Zp Np).ended)
                          ((H2K.JointK.sharedN Zp Np).okInst)
                          ((H2K.JointK.sharedN Zp Np).fileOk)
                          ((H2K.JointK.sharedN Zp Np).standIns)
                          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                          (ProofFile.startS Zp) cF Zp.p.chains
                          (Desc.K14.p14Of Zp.p.chains
                            (Desc.K14.beforePointOf Np))
                          (VerifiableInference.Desc.K12.Seat.tests Np)))
                      ▸ P5J.At.smp Zp),
                    (P5J.At.ms Zp Zs.lay)⟩).R)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                      (VerifiableInference.PlanWritten.sized_of_made
                        hMadePinnedP1)
                      (VerifiableInference.PlanWritten.first_of_made
                        hMadePinnedP1)
                      (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                        hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                      map14_hx).shape))
                OnBytes.Flat.numsFull
                (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs))))
          true
          (atDesc
            (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
              (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (piecesAt (ckP .two)
              (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np))
              (DP.at frS.P.T.a)
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.first.asBare)
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.front.map
                VerifiableInference.Desc.Block.asBare ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                  (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.links.flatMap
                VerifiableInference.Desc.Link.blocksInOrder ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.back.map
                VerifiableInference.Desc.Block.asBare ++
                [(fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.last.asBare])
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                  (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.first.asBare)
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.front.map
                VerifiableInference.Desc.Block.asBare ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                  (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.links.flatMap
                VerifiableInference.Desc.Link.blocksInOrder ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.back.map
                VerifiableInference.Desc.Block.asBare ++
                [(fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).shared.last.asBare])
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                  (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.first.asBare)
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.front.map
                VerifiableInference.Desc.Block.asBare ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                  (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.links.flatMap
                VerifiableInference.Desc.Link.blocksInOrder ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.back.map
                VerifiableInference.Desc.Block.asBare ++
                [(fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).second.last.asBare])
              (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂
          (atDesc
            (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
              (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (piecesAt (ckP .two)
              (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np))
              (DP.at frS.P.T.a)
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.first.asBare)
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.front.map
                VerifiableInference.Desc.Block.asBare ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                  (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.links.flatMap
                VerifiableInference.Desc.Link.blocksInOrder ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.back.map
                VerifiableInference.Desc.Block.asBare ++
                [(fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.last.asBare])
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                  (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.first.asBare)
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.front.map
                VerifiableInference.Desc.Block.asBare ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                  (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.links.flatMap
                VerifiableInference.Desc.Link.blocksInOrder ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.back.map
                VerifiableInference.Desc.Block.asBare ++
                [(fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).shared.last.asBare])
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                  (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.first.asBare)
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.front.map
                VerifiableInference.Desc.Block.asBare ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                  (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.links.flatMap
                VerifiableInference.Desc.Link.blocksInOrder ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.back.map
                VerifiableInference.Desc.Block.asBare ++
                [(fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).second.last.asBare])
              (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).l₂
          (extOf
            (Desc.K14.Law.Sh.nums
              (Desc.K14.Law.ShPlan.mk
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                  Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np))
                (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                  Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
                (Desc.K14.Law.rad2At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (Desc.K14.Law.rad5At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                Johnson.G.dryProofFull.2.1 2)
              (Desc.K14.Law.ShOpen.mk (P₀ := ProofFile.InstPub)
                (P₁ := ProofFile.InstPub × VerifiableInference.Desc.First.S)
                (Cells :=
                  ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                      (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                      (P5J.At.EAt Zs)).conf.I))
                (Tok := P5J.At.Tok)
                (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0)
                (fun a => (a.1, a.2))
                ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                    (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                    (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                      cF Zp.p.chains
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                      (VerifiableInference.Desc.K12.Seat.tests Np)))
                  ▸ P5J.At.smp Zp)
                (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.fullLinks (P5J.mgAtAll hAtMgA)
                (VerifiableInference.Desc.K13.whereOf Zp)
                ((Desc.K14.Law.Sh.openAt₀
                    (Cells :=
                      ((VerifiableInference.OnPublicFiles.kcReq
                          OnBytes.Flat.numsFull
                          (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol
                            Zs.KL)
                          (P5J.At.EAt Zs)).conf.I))
                    (Tok := P5J.At.Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    cF (fun _ _ => 0)
                    (Desc.K14.Law.matN (frS.toDecR frZ 402653181)
                      OnBytes.Flat.numsFull)
                    (Desc.K14.Law.heldFull
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                      (Desc.K14.p14Of Zp.p.chains
                        (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                      (Desc.K14.Law.full_index
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np)).par.S
                        (Desc.K14.Law.full_of_shape map14_hx
                          (Desc.K14.Law.written_in_scope hAtMgA.scope
                            hAtMgA.laid.pub
                            (VerifiableInference.PlanWritten.sized_of_made
                              hMadePinnedP1)
                            (VerifiableInference.PlanWritten.first_of_made
                              hMadePinnedP1)
                            (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                              hAtMgA.laid.value hAtMgA.laid.planOk
                              hAtMgA.laid.data hAtMgA.laid.asks)
                            map14_hx).shape))
                      OnBytes.Flat.numsFull
                      (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                      (P5J.At.EAt Zs))
                    ⟨(P5J.At.N Zp cF), P5J.fullLinks, (P5J.mgAtAll hAtMgA),
                      ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                          (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                          (fieldF oL ProofFile.pureRoad.links Zp
                            ((H2K.JointK.sharedN Zp Np).lot)
                            ((H2K.JointK.sharedN Zp Np).start)
                            ((H2K.JointK.sharedN Zp Np).ended)
                            ((H2K.JointK.sharedN Zp Np).okInst)
                            ((H2K.JointK.sharedN Zp Np).fileOk)
                            ((H2K.JointK.sharedN Zp Np).standIns)
                            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                            (ProofFile.startS Zp) cF Zp.p.chains
                            (Desc.K14.p14Of Zp.p.chains
                              (Desc.K14.beforePointOf Np))
                            (VerifiableInference.Desc.K12.Seat.tests Np)))
                        ▸ P5J.At.smp Zp),
                      (P5J.At.ms Zp Zs.lay)⟩).R)
                (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                (Desc.K14.Law.heldFull
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                  (Desc.K14.Law.full_index
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                    (Desc.K14.Law.full_of_shape map14_hx
                      (Desc.K14.Law.written_in_scope hAtMgA.scope
                        hAtMgA.laid.pub
                        (VerifiableInference.PlanWritten.sized_of_made
                          hMadePinnedP1)
                        (VerifiableInference.PlanWritten.first_of_made
                          hMadePinnedP1)
                        (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                          hAtMgA.laid.value hAtMgA.laid.planOk
                          hAtMgA.laid.data hAtMgA.laid.asks)
                        map14_hx).shape))
                  OnBytes.Flat.numsFull
                  (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs))))
            (atDesc
              (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np))
              (piecesAt (ckP .two)
                (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                  Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np))
                (DP.at frS.P.T.a)
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.first.asBare)
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.front.map
                  VerifiableInference.Desc.Block.asBare ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.links.flatMap
                  VerifiableInference.Desc.Link.blocksInOrder ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.back.map
                  VerifiableInference.Desc.Block.asBare ++
                  [(fieldF oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                      (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                      (Desc.K14.p14Of Zp.p.chains
                        (Desc.K14.beforePointOf Np))
                      (VerifiableInference.Desc.K12.Seat.tests
                        Np)).first.last.asBare])
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).shared.first.asBare)
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).shared.front.map
                  VerifiableInference.Desc.Block.asBare ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests
                      Np)).shared.links.flatMap
                  VerifiableInference.Desc.Link.blocksInOrder ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).shared.back.map
                  VerifiableInference.Desc.Block.asBare ++
                  [(fieldF oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                      (fun s => s) (ProofFile.startS Zp) cF
                      Zp.p.chains
                      (Desc.K14.p14Of Zp.p.chains
                        (Desc.K14.beforePointOf Np))
                      (VerifiableInference.Desc.K12.Seat.tests
                        Np)).shared.last.asBare])
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).second.first.asBare)
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).second.front.map
                  VerifiableInference.Desc.Block.asBare ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests
                      Np)).second.links.flatMap
                  VerifiableInference.Desc.Link.blocksInOrder ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).second.back.map
                  VerifiableInference.Desc.Block.asBare ++
                  [(fieldF oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                      (fun s => s) (ProofFile.startS Zp) cF
                      Zp.p.chains
                      (Desc.K14.p14Of Zp.p.chains
                        (Desc.K14.beforePointOf Np))
                      (VerifiableInference.Desc.K12.Seat.tests
                        Np)).second.last.asBare])
                (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂
            (atDesc
              (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np))
              (piecesAt (ckP .two)
                (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                  Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np))
                (DP.at frS.P.T.a)
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.first.asBare)
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.front.map
                  VerifiableInference.Desc.Block.asBare ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.links.flatMap
                  VerifiableInference.Desc.Link.blocksInOrder ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.back.map
                  VerifiableInference.Desc.Block.asBare ++
                  [(fieldF oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                      (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                      (Desc.K14.p14Of Zp.p.chains
                        (Desc.K14.beforePointOf Np))
                      (VerifiableInference.Desc.K12.Seat.tests
                        Np)).first.last.asBare])
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).shared.first.asBare)
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).shared.front.map
                  VerifiableInference.Desc.Block.asBare ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests
                      Np)).shared.links.flatMap
                  VerifiableInference.Desc.Link.blocksInOrder ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).shared.back.map
                  VerifiableInference.Desc.Block.asBare ++
                  [(fieldF oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                      (fun s => s) (ProofFile.startS Zp) cF
                      Zp.p.chains
                      (Desc.K14.p14Of Zp.p.chains
                        (Desc.K14.beforePointOf Np))
                      (VerifiableInference.Desc.K12.Seat.tests
                        Np)).shared.last.asBare])
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).second.first.asBare)
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).second.front.map
                  VerifiableInference.Desc.Block.asBare ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests
                      Np)).second.links.flatMap
                  VerifiableInference.Desc.Link.blocksInOrder ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).second.back.map
                  VerifiableInference.Desc.Block.asBare ++
                  [(fieldF oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                      (fun s => s) (ProofFile.startS Zp) cF
                      Zp.p.chains
                      (Desc.K14.p14Of Zp.p.chains
                        (Desc.K14.beforePointOf Np))
                      (VerifiableInference.Desc.K12.Seat.tests
                        Np)).second.last.asBare])
                (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).l₂
            (Desc.K14.Law.Sh.ex
              (Desc.K14.Law.ShPlan.mk
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                  Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np))
                (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                  Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
                (Desc.K14.Law.rad2At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (Desc.K14.Law.rad5At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                Johnson.G.dryProofFull.2.1 2)
              (Desc.K14.Law.ShOpen.mk (P₀ := ProofFile.InstPub)
                (P₁ := ProofFile.InstPub × VerifiableInference.Desc.First.S)
                (Cells :=
                  ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                      (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                      (P5J.At.EAt Zs)).conf.I))
                (Tok := P5J.At.Tok)
                (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0)
                (fun a => (a.1, a.2))
                ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                    (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                    (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                      cF Zp.p.chains
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                      (VerifiableInference.Desc.K12.Seat.tests Np)))
                  ▸ P5J.At.smp Zp)
                (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.fullLinks (P5J.mgAtAll hAtMgA)
                (VerifiableInference.Desc.K13.whereOf Zp)
                ((Desc.K14.Law.Sh.openAt₀
                    (Cells :=
                      ((VerifiableInference.OnPublicFiles.kcReq
                          OnBytes.Flat.numsFull
                          (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol
                            Zs.KL)
                          (P5J.At.EAt Zs)).conf.I))
                    (Tok := P5J.At.Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    cF (fun _ _ => 0)
                    (Desc.K14.Law.matN (frS.toDecR frZ 402653181)
                      OnBytes.Flat.numsFull)
                    (Desc.K14.Law.heldFull
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                      (Desc.K14.p14Of Zp.p.chains
                        (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                      (Desc.K14.Law.full_index
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np)).par.S
                        (Desc.K14.Law.full_of_shape map14_hx
                          (Desc.K14.Law.written_in_scope hAtMgA.scope
                            hAtMgA.laid.pub
                            (VerifiableInference.PlanWritten.sized_of_made
                              hMadePinnedP1)
                            (VerifiableInference.PlanWritten.first_of_made
                              hMadePinnedP1)
                            (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                              hAtMgA.laid.value hAtMgA.laid.planOk
                              hAtMgA.laid.data hAtMgA.laid.asks)
                            map14_hx).shape))
                      OnBytes.Flat.numsFull
                      (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                      (P5J.At.EAt Zs))
                    ⟨(P5J.At.N Zp cF), P5J.fullLinks, (P5J.mgAtAll hAtMgA),
                      ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                          (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                          (fieldF oL ProofFile.pureRoad.links Zp
                            ((H2K.JointK.sharedN Zp Np).lot)
                            ((H2K.JointK.sharedN Zp Np).start)
                            ((H2K.JointK.sharedN Zp Np).ended)
                            ((H2K.JointK.sharedN Zp Np).okInst)
                            ((H2K.JointK.sharedN Zp Np).fileOk)
                            ((H2K.JointK.sharedN Zp Np).standIns)
                            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                            (ProofFile.startS Zp) cF Zp.p.chains
                            (Desc.K14.p14Of Zp.p.chains
                              (Desc.K14.beforePointOf Np))
                            (VerifiableInference.Desc.K12.Seat.tests Np)))
                        ▸ P5J.At.smp Zp),
                      (P5J.At.ms Zp Zs.lay)⟩).R)
                (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                (Desc.K14.Law.heldFull
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                  (Desc.K14.Law.full_index
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                    (Desc.K14.Law.full_of_shape map14_hx
                      (Desc.K14.Law.written_in_scope hAtMgA.scope
                        hAtMgA.laid.pub
                        (VerifiableInference.PlanWritten.sized_of_made
                          hMadePinnedP1)
                        (VerifiableInference.PlanWritten.first_of_made
                          hMadePinnedP1)
                        (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                          hAtMgA.laid.value hAtMgA.laid.planOk
                          hAtMgA.laid.data hAtMgA.laid.asks)
                        map14_hx).shape))
                  OnBytes.Flat.numsFull
                  (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs)))
              (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₂
                0))))
        (((Desc.K14.Law.Sh.openAt₀
              (Cells :=
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs)).conf.I))
              (Tok := P5J.At.Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
              (fun _ _ => 0)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hAtMgA.scope
                      hAtMgA.laid.pub
                      (VerifiableInference.PlanWritten.sized_of_made
                        hMadePinnedP1)
                      (VerifiableInference.PlanWritten.first_of_made
                        hMadePinnedP1)
                      (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                        hAtMgA.laid.value hAtMgA.laid.planOk hAtMgA.laid.data
                        hAtMgA.laid.asks)
                      map14_hx).shape))
                OnBytes.Flat.numsFull
                (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs))
              ⟨(P5J.At.N Zp cF), P5J.fullLinks, (P5J.mgAtAll hAtMgA),
                ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                    (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                    (fieldF oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                      (ProofFile.startS Zp) cF Zp.p.chains
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                      (VerifiableInference.Desc.K12.Seat.tests Np)))
                  ▸ P5J.At.smp Zp),
                (P5J.At.ms Zp Zs.lay)⟩).R))).on₂
      (P5J.plTablesR
        (atDesc
          (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
            (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (piecesAt (ckP .two)
            (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
              (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (DP.at frS.P.T.a)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.first.asBare)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.front.map
              VerifiableInference.Desc.Block.asBare ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.links.flatMap
              VerifiableInference.Desc.Link.blocksInOrder ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.back.map
              VerifiableInference.Desc.Block.asBare ++
              [(fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.last.asBare])
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.first.asBare)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.front.map
              VerifiableInference.Desc.Block.asBare ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.links.flatMap
              VerifiableInference.Desc.Link.blocksInOrder ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.back.map
              VerifiableInference.Desc.Block.asBare ++
              [(fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.last.asBare])
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.first.asBare)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.front.map
              VerifiableInference.Desc.Block.asBare ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.links.flatMap
              VerifiableInference.Desc.Link.blocksInOrder ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.back.map
              VerifiableInference.Desc.Block.asBare ++
              [(fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.last.asBare])
            (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd))
        ((fun a => (a.1, a.2))) (P5J.At.N Zp cF) (P5J.mgAtAll hAtMgA) P5J.fullLinks
        ((VerifiableInference.Desc.First.flatPlaces true P5J.fullLinks true))
        ((Desc.K14.Law.Fence.numbersSh
            (Desc.K14.Law.Sh.t₁
              (Desc.K14.Law.ShPlan.mk
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                  Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np))
                (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                  Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
                (Desc.K14.Law.rad2At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (Desc.K14.Law.rad5At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                Johnson.G.dryProofFull.2.1 2))
            (Desc.K14.Law.Sh.layU
              (Desc.K14.Law.ShPlan.mk
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                  Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np))
                (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                  Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
                (Desc.K14.Law.rad2At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (Desc.K14.Law.rad5At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                Johnson.G.dryProofFull.2.1 2))
            (Desc.K14.Law.Sh.layO
              (Desc.K14.Law.ShPlan.mk
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                  Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np))
                (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                  Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
                (Desc.K14.Law.rad2At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (Desc.K14.Law.rad5At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                Johnson.G.dryProofFull.2.1 2))
            (0, 0) (0, 0)))
        MgS ML
        (Desc.K14.Law.Sh.pm
          (Desc.K14.Law.ShPlan.mk (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
              (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
              Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
            (Desc.K14.Law.rad2At 2 (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
            (Desc.K14.Law.rad5At 2 (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
            Johnson.G.dryProofFull.2.1 2)
          (Desc.K14.Law.ShOpen.mk (P₀ := ProofFile.InstPub)
            (P₁ := ProofFile.InstPub × VerifiableInference.Desc.First.S)
            (Cells :=
              ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                  (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                  (P5J.At.EAt Zs)).conf.I))
            (Tok := P5J.At.Tok)
            (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
            (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
            ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                  Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)))
              ▸ P5J.At.smp Zp)
            (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.fullLinks (P5J.mgAtAll hAtMgA)
            (VerifiableInference.Desc.K13.whereOf Zp)
            ((Desc.K14.Law.Sh.openAt₀
                (Cells :=
                  ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                      (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                      (P5J.At.EAt Zs)).conf.I))
                (Tok := P5J.At.Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                (fun _ _ => 0)
                (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                (Desc.K14.Law.heldFull
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                  (Desc.K14.Law.full_index
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                    (Desc.K14.Law.full_of_shape map14_hx
                      (Desc.K14.Law.written_in_scope hAtMgA.scope
                        hAtMgA.laid.pub
                        (VerifiableInference.PlanWritten.sized_of_made
                          hMadePinnedP1)
                        (VerifiableInference.PlanWritten.first_of_made
                          hMadePinnedP1)
                        (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                          hAtMgA.laid.value hAtMgA.laid.planOk
                          hAtMgA.laid.data hAtMgA.laid.asks)
                        map14_hx).shape))
                  OnBytes.Flat.numsFull
                  (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs))
                ⟨(P5J.At.N Zp cF), P5J.fullLinks, (P5J.mgAtAll hAtMgA),
                  ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                      (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                      (fieldF oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                        (ProofFile.startS Zp) cF Zp.p.chains
                        (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                        (VerifiableInference.Desc.K12.Seat.tests Np)))
                    ▸ P5J.At.smp Zp),
                  (P5J.At.ms Zp Zs.lay)⟩).R)
            (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
            (Desc.K14.Law.heldFull
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
              (Desc.K14.p14Of Zp.p.chains
                (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
              (Desc.K14.Law.full_index
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                (Desc.K14.Law.full_of_shape map14_hx
                  (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                    (VerifiableInference.PlanWritten.sized_of_made hMadePinnedP1)
                    (VerifiableInference.PlanWritten.first_of_made hMadePinnedP1)
                    (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                      hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                    map14_hx).shape))
              OnBytes.Flat.numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
              (P5J.At.EAt Zs))))
        PLm true
        (stepAt
          (Desc.K14.Law.Sh.nums
            (Desc.K14.Law.ShPlan.mk
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np))
              (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
              (Desc.K14.Law.rad2At 2
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (Desc.K14.Law.rad5At 2
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              Johnson.G.dryProofFull.2.1 2)
            (Desc.K14.Law.ShOpen.mk (P₀ := ProofFile.InstPub)
              (P₁ := ProofFile.InstPub × VerifiableInference.Desc.First.S)
              (Cells :=
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs)).conf.I))
              (Tok := P5J.At.Tok)
              (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
              ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                  (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                  (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                    Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)))
                ▸ P5J.At.smp Zp)
              (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.fullLinks (P5J.mgAtAll hAtMgA)
              (VerifiableInference.Desc.K13.whereOf Zp)
              ((Desc.K14.Law.Sh.openAt₀
                  (Cells :=
                    ((VerifiableInference.OnPublicFiles.kcReq
                        OnBytes.Flat.numsFull
                        (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                        (P5J.At.EAt Zs)).conf.I))
                  (Tok := P5J.At.Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                  (fun _ _ => 0)
                  (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                  (Desc.K14.Law.heldFull
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                    (Desc.K14.Law.full_index
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                      (Desc.K14.Law.full_of_shape map14_hx
                        (Desc.K14.Law.written_in_scope hAtMgA.scope
                          hAtMgA.laid.pub
                          (VerifiableInference.PlanWritten.sized_of_made
                            hMadePinnedP1)
                          (VerifiableInference.PlanWritten.first_of_made
                            hMadePinnedP1)
                          (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                            hAtMgA.laid.value hAtMgA.laid.planOk
                            hAtMgA.laid.data hAtMgA.laid.asks)
                          map14_hx).shape))
                    OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs))
                  ⟨(P5J.At.N Zp cF), P5J.fullLinks, (P5J.mgAtAll hAtMgA),
                    ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                        (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                        (fieldF oL ProofFile.pureRoad.links Zp
                          ((H2K.JointK.sharedN Zp Np).lot)
                          ((H2K.JointK.sharedN Zp Np).start)
                          ((H2K.JointK.sharedN Zp Np).ended)
                          ((H2K.JointK.sharedN Zp Np).okInst)
                          ((H2K.JointK.sharedN Zp Np).fileOk)
                          ((H2K.JointK.sharedN Zp Np).standIns)
                          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                          (ProofFile.startS Zp) cF Zp.p.chains
                          (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                          (VerifiableInference.Desc.K12.Seat.tests Np)))
                      ▸ P5J.At.smp Zp),
                    (P5J.At.ms Zp Zs.lay)⟩).R)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                      (VerifiableInference.PlanWritten.sized_of_made
                        hMadePinnedP1)
                      (VerifiableInference.PlanWritten.first_of_made
                        hMadePinnedP1)
                      (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                        hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                      map14_hx).shape))
                OnBytes.Flat.numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                (P5J.At.EAt Zs))))
          (Desc.K14.Law.Sh.mg
            (Desc.K14.Law.ShPlan.mk
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np))
              (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
              (Desc.K14.Law.rad2At 2
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (Desc.K14.Law.rad5At 2
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              Johnson.G.dryProofFull.2.1 2)
            (Desc.K14.Law.ShOpen.mk (P₀ := ProofFile.InstPub)
              (P₁ := ProofFile.InstPub × VerifiableInference.Desc.First.S)
              (Cells :=
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs)).conf.I))
              (Tok := P5J.At.Tok)
              (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
              ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                  (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                  (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                    Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)))
                ▸ P5J.At.smp Zp)
              (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.fullLinks (P5J.mgAtAll hAtMgA)
              (VerifiableInference.Desc.K13.whereOf Zp)
              ((Desc.K14.Law.Sh.openAt₀
                  (Cells :=
                    ((VerifiableInference.OnPublicFiles.kcReq
                        OnBytes.Flat.numsFull
                        (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                        (P5J.At.EAt Zs)).conf.I))
                  (Tok := P5J.At.Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                  (fun _ _ => 0)
                  (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                  (Desc.K14.Law.heldFull
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                    (Desc.K14.Law.full_index
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                      (Desc.K14.Law.full_of_shape map14_hx
                        (Desc.K14.Law.written_in_scope hAtMgA.scope
                          hAtMgA.laid.pub
                          (VerifiableInference.PlanWritten.sized_of_made
                            hMadePinnedP1)
                          (VerifiableInference.PlanWritten.first_of_made
                            hMadePinnedP1)
                          (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                            hAtMgA.laid.value hAtMgA.laid.planOk
                            hAtMgA.laid.data hAtMgA.laid.asks)
                          map14_hx).shape))
                    OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs))
                  ⟨(P5J.At.N Zp cF), P5J.fullLinks, (P5J.mgAtAll hAtMgA),
                    ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                        (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                        (fieldF oL ProofFile.pureRoad.links Zp
                          ((H2K.JointK.sharedN Zp Np).lot)
                          ((H2K.JointK.sharedN Zp Np).start)
                          ((H2K.JointK.sharedN Zp Np).ended)
                          ((H2K.JointK.sharedN Zp Np).okInst)
                          ((H2K.JointK.sharedN Zp Np).fileOk)
                          ((H2K.JointK.sharedN Zp Np).standIns)
                          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                          (ProofFile.startS Zp) cF Zp.p.chains
                          (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                          (VerifiableInference.Desc.K12.Seat.tests Np)))
                      ▸ P5J.At.smp Zp),
                    (P5J.At.ms Zp Zs.lay)⟩).R)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                      (VerifiableInference.PlanWritten.sized_of_made
                        hMadePinnedP1)
                      (VerifiableInference.PlanWritten.first_of_made
                        hMadePinnedP1)
                      (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                        hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                      map14_hx).shape))
                OnBytes.Flat.numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                (P5J.At.EAt Zs))))
          (Desc.K14.Law.Sh.pm
            (Desc.K14.Law.ShPlan.mk
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np))
              (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
              (Desc.K14.Law.rad2At 2
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (Desc.K14.Law.rad5At 2
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              Johnson.G.dryProofFull.2.1 2)
            (Desc.K14.Law.ShOpen.mk (P₀ := ProofFile.InstPub)
              (P₁ := ProofFile.InstPub × VerifiableInference.Desc.First.S)
              (Cells :=
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs)).conf.I))
              (Tok := P5J.At.Tok)
              (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
              ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                  (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                  (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                    Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)))
                ▸ P5J.At.smp Zp)
              (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.fullLinks (P5J.mgAtAll hAtMgA)
              (VerifiableInference.Desc.K13.whereOf Zp)
              ((Desc.K14.Law.Sh.openAt₀
                  (Cells :=
                    ((VerifiableInference.OnPublicFiles.kcReq
                        OnBytes.Flat.numsFull
                        (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                        (P5J.At.EAt Zs)).conf.I))
                  (Tok := P5J.At.Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                  (fun _ _ => 0)
                  (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                  (Desc.K14.Law.heldFull
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                    (Desc.K14.Law.full_index
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                      (Desc.K14.Law.full_of_shape map14_hx
                        (Desc.K14.Law.written_in_scope hAtMgA.scope
                          hAtMgA.laid.pub
                          (VerifiableInference.PlanWritten.sized_of_made
                            hMadePinnedP1)
                          (VerifiableInference.PlanWritten.first_of_made
                            hMadePinnedP1)
                          (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                            hAtMgA.laid.value hAtMgA.laid.planOk
                            hAtMgA.laid.data hAtMgA.laid.asks)
                          map14_hx).shape))
                    OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs))
                  ⟨(P5J.At.N Zp cF), P5J.fullLinks, (P5J.mgAtAll hAtMgA),
                    ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                        (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                        (fieldF oL ProofFile.pureRoad.links Zp
                          ((H2K.JointK.sharedN Zp Np).lot)
                          ((H2K.JointK.sharedN Zp Np).start)
                          ((H2K.JointK.sharedN Zp Np).ended)
                          ((H2K.JointK.sharedN Zp Np).okInst)
                          ((H2K.JointK.sharedN Zp Np).fileOk)
                          ((H2K.JointK.sharedN Zp Np).standIns)
                          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                          (ProofFile.startS Zp) cF Zp.p.chains
                          (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                          (VerifiableInference.Desc.K12.Seat.tests Np)))
                      ▸ P5J.At.smp Zp),
                    (P5J.At.ms Zp Zs.lay)⟩).R)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                      (VerifiableInference.PlanWritten.sized_of_made
                        hMadePinnedP1)
                      (VerifiableInference.PlanWritten.first_of_made
                        hMadePinnedP1)
                      (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                        hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                      map14_hx).shape))
                OnBytes.Flat.numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                (P5J.At.EAt Zs))))
          (Desc.K14.Law.Sh.own
            (Desc.K14.Law.ShPlan.mk
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np))
              (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
              (Desc.K14.Law.rad2At 2
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (Desc.K14.Law.rad5At 2
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              Johnson.G.dryProofFull.2.1 2)
            (Desc.K14.Law.ShOpen.mk (P₀ := ProofFile.InstPub)
              (P₁ := ProofFile.InstPub × VerifiableInference.Desc.First.S)
              (Cells :=
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs)).conf.I))
              (Tok := P5J.At.Tok)
              (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
              ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                  (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                  (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                    Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)))
                ▸ P5J.At.smp Zp)
              (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.fullLinks (P5J.mgAtAll hAtMgA)
              (VerifiableInference.Desc.K13.whereOf Zp)
              ((Desc.K14.Law.Sh.openAt₀
                  (Cells :=
                    ((VerifiableInference.OnPublicFiles.kcReq
                        OnBytes.Flat.numsFull
                        (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                        (P5J.At.EAt Zs)).conf.I))
                  (Tok := P5J.At.Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                  (fun _ _ => 0)
                  (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                  (Desc.K14.Law.heldFull
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                    (Desc.K14.Law.full_index
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                      (Desc.K14.Law.full_of_shape map14_hx
                        (Desc.K14.Law.written_in_scope hAtMgA.scope
                          hAtMgA.laid.pub
                          (VerifiableInference.PlanWritten.sized_of_made
                            hMadePinnedP1)
                          (VerifiableInference.PlanWritten.first_of_made
                            hMadePinnedP1)
                          (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                            hAtMgA.laid.value hAtMgA.laid.planOk
                            hAtMgA.laid.data hAtMgA.laid.asks)
                          map14_hx).shape))
                    OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs))
                  ⟨(P5J.At.N Zp cF), P5J.fullLinks, (P5J.mgAtAll hAtMgA),
                    ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                        (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                        (fieldF oL ProofFile.pureRoad.links Zp
                          ((H2K.JointK.sharedN Zp Np).lot)
                          ((H2K.JointK.sharedN Zp Np).start)
                          ((H2K.JointK.sharedN Zp Np).ended)
                          ((H2K.JointK.sharedN Zp Np).okInst)
                          ((H2K.JointK.sharedN Zp Np).fileOk)
                          ((H2K.JointK.sharedN Zp Np).standIns)
                          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                          (ProofFile.startS Zp) cF Zp.p.chains
                          (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                          (VerifiableInference.Desc.K12.Seat.tests Np)))
                      ▸ P5J.At.smp Zp),
                    (P5J.At.ms Zp Zs.lay)⟩).R)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                      (VerifiableInference.PlanWritten.sized_of_made
                        hMadePinnedP1)
                      (VerifiableInference.PlanWritten.first_of_made
                        hMadePinnedP1)
                      (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                        hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                      map14_hx).shape))
                OnBytes.Flat.numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                (P5J.At.EAt Zs))))
          true
          (atDesc
            (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
              (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (piecesAt (ckP .two)
              (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np))
              (DP.at frS.P.T.a)
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.first.asBare)
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.front.map
                VerifiableInference.Desc.Block.asBare ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.links.flatMap
                VerifiableInference.Desc.Link.blocksInOrder ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.back.map
                VerifiableInference.Desc.Block.asBare ++
                [(fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.last.asBare])
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.first.asBare)
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.front.map
                VerifiableInference.Desc.Block.asBare ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                  (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.links.flatMap
                VerifiableInference.Desc.Link.blocksInOrder ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.back.map
                VerifiableInference.Desc.Block.asBare ++
                [(fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).shared.last.asBare])
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.first.asBare)
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.front.map
                VerifiableInference.Desc.Block.asBare ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                  (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.links.flatMap
                VerifiableInference.Desc.Link.blocksInOrder ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.back.map
                VerifiableInference.Desc.Block.asBare ++
                [(fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).second.last.asBare])
              (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂
          (atDesc
            (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
              (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (piecesAt (ckP .two)
              (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np))
              (DP.at frS.P.T.a)
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.first.asBare)
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.front.map
                VerifiableInference.Desc.Block.asBare ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.links.flatMap
                VerifiableInference.Desc.Link.blocksInOrder ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.back.map
                VerifiableInference.Desc.Block.asBare ++
                [(fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.last.asBare])
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.first.asBare)
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.front.map
                VerifiableInference.Desc.Block.asBare ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                  (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.links.flatMap
                VerifiableInference.Desc.Link.blocksInOrder ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.back.map
                VerifiableInference.Desc.Block.asBare ++
                [(fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).shared.last.asBare])
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.first.asBare)
              ((fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.front.map
                VerifiableInference.Desc.Block.asBare ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                  (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.links.flatMap
                VerifiableInference.Desc.Link.blocksInOrder ++
                (fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.back.map
                VerifiableInference.Desc.Block.asBare ++
                [(fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).second.last.asBare])
              (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).l₂
          (extOf
            (Desc.K14.Law.Sh.nums
              (Desc.K14.Law.ShPlan.mk
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                  Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np))
                (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                  Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
                (Desc.K14.Law.rad2At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (Desc.K14.Law.rad5At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                Johnson.G.dryProofFull.2.1 2)
              (Desc.K14.Law.ShOpen.mk (P₀ := ProofFile.InstPub)
                (P₁ := ProofFile.InstPub × VerifiableInference.Desc.First.S)
                (Cells :=
                  ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                      (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                      (P5J.At.EAt Zs)).conf.I))
                (Tok := P5J.At.Tok)
                (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0)
                (fun a => (a.1, a.2))
                ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                    (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                    (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                      cF Zp.p.chains
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                      (VerifiableInference.Desc.K12.Seat.tests Np)))
                  ▸ P5J.At.smp Zp)
                (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.fullLinks (P5J.mgAtAll hAtMgA)
                (VerifiableInference.Desc.K13.whereOf Zp)
                ((Desc.K14.Law.Sh.openAt₀
                    (Cells :=
                      ((VerifiableInference.OnPublicFiles.kcReq
                          OnBytes.Flat.numsFull
                          (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol
                            Zs.KL)
                          (P5J.At.EAt Zs)).conf.I))
                    (Tok := P5J.At.Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    cF (fun _ _ => 0)
                    (Desc.K14.Law.matN (frS.toDecR frZ 402653181)
                      OnBytes.Flat.numsFull)
                    (Desc.K14.Law.heldFull
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                      (Desc.K14.p14Of Zp.p.chains
                        (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                      (Desc.K14.Law.full_index
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np)).par.S
                        (Desc.K14.Law.full_of_shape map14_hx
                          (Desc.K14.Law.written_in_scope hAtMgA.scope
                            hAtMgA.laid.pub
                            (VerifiableInference.PlanWritten.sized_of_made
                              hMadePinnedP1)
                            (VerifiableInference.PlanWritten.first_of_made
                              hMadePinnedP1)
                            (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                              hAtMgA.laid.value hAtMgA.laid.planOk
                              hAtMgA.laid.data hAtMgA.laid.asks)
                            map14_hx).shape))
                      OnBytes.Flat.numsFull
                      (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                      (P5J.At.EAt Zs))
                    ⟨(P5J.At.N Zp cF), P5J.fullLinks, (P5J.mgAtAll hAtMgA),
                      ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                          (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                          (fieldF oL ProofFile.pureRoad.links Zp
                            ((H2K.JointK.sharedN Zp Np).lot)
                            ((H2K.JointK.sharedN Zp Np).start)
                            ((H2K.JointK.sharedN Zp Np).ended)
                            ((H2K.JointK.sharedN Zp Np).okInst)
                            ((H2K.JointK.sharedN Zp Np).fileOk)
                            ((H2K.JointK.sharedN Zp Np).standIns)
                            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                            (ProofFile.startS Zp) cF Zp.p.chains
                            (Desc.K14.p14Of Zp.p.chains
                              (Desc.K14.beforePointOf Np))
                            (VerifiableInference.Desc.K12.Seat.tests Np)))
                        ▸ P5J.At.smp Zp),
                      (P5J.At.ms Zp Zs.lay)⟩).R)
                (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                (Desc.K14.Law.heldFull
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                  (Desc.K14.Law.full_index
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                    (Desc.K14.Law.full_of_shape map14_hx
                      (Desc.K14.Law.written_in_scope hAtMgA.scope
                        hAtMgA.laid.pub
                        (VerifiableInference.PlanWritten.sized_of_made
                          hMadePinnedP1)
                        (VerifiableInference.PlanWritten.first_of_made
                          hMadePinnedP1)
                        (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                          hAtMgA.laid.value hAtMgA.laid.planOk hAtMgA.laid.data
                          hAtMgA.laid.asks)
                        map14_hx).shape))
                  OnBytes.Flat.numsFull
                  (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs))))
            (atDesc
              (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np))
              (piecesAt (ckP .two)
                (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                  Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np))
                (DP.at frS.P.T.a)
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.first.asBare)
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.front.map
                  VerifiableInference.Desc.Block.asBare ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.links.flatMap
                  VerifiableInference.Desc.Link.blocksInOrder ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.back.map
                  VerifiableInference.Desc.Block.asBare ++
                  [(fieldF oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                      (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                      (Desc.K14.p14Of Zp.p.chains
                        (Desc.K14.beforePointOf Np))
                      (VerifiableInference.Desc.K12.Seat.tests Np)).first.last.asBare])
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).shared.first.asBare)
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).shared.front.map
                  VerifiableInference.Desc.Block.asBare ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).shared.links.flatMap
                  VerifiableInference.Desc.Link.blocksInOrder ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).shared.back.map
                  VerifiableInference.Desc.Block.asBare ++
                  [(fieldF oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                      (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                      (Desc.K14.p14Of Zp.p.chains
                        (Desc.K14.beforePointOf Np))
                      (VerifiableInference.Desc.K12.Seat.tests
                        Np)).shared.last.asBare])
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).second.first.asBare)
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).second.front.map
                  VerifiableInference.Desc.Block.asBare ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).second.links.flatMap
                  VerifiableInference.Desc.Link.blocksInOrder ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).second.back.map
                  VerifiableInference.Desc.Block.asBare ++
                  [(fieldF oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                      (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                      (Desc.K14.p14Of Zp.p.chains
                        (Desc.K14.beforePointOf Np))
                      (VerifiableInference.Desc.K12.Seat.tests
                        Np)).second.last.asBare])
                (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂
            (atDesc
              (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np))
              (piecesAt (ckP .two)
                (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                  Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np))
                (DP.at frS.P.T.a)
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.first.asBare)
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.front.map
                  VerifiableInference.Desc.Block.asBare ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.links.flatMap
                  VerifiableInference.Desc.Link.blocksInOrder ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).first.back.map
                  VerifiableInference.Desc.Block.asBare ++
                  [(fieldF oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                      (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                      (Desc.K14.p14Of Zp.p.chains
                        (Desc.K14.beforePointOf Np))
                      (VerifiableInference.Desc.K12.Seat.tests Np)).first.last.asBare])
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).shared.first.asBare)
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).shared.front.map
                  VerifiableInference.Desc.Block.asBare ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).shared.links.flatMap
                  VerifiableInference.Desc.Link.blocksInOrder ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).shared.back.map
                  VerifiableInference.Desc.Block.asBare ++
                  [(fieldF oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                      (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                      (Desc.K14.p14Of Zp.p.chains
                        (Desc.K14.beforePointOf Np))
                      (VerifiableInference.Desc.K12.Seat.tests
                        Np)).shared.last.asBare])
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).second.first.asBare)
                ((fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).second.front.map
                  VerifiableInference.Desc.Block.asBare ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).second.links.flatMap
                  VerifiableInference.Desc.Link.blocksInOrder ++
                  (fieldF oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).second.back.map
                  VerifiableInference.Desc.Block.asBare ++
                  [(fieldF oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                      (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                      (Desc.K14.p14Of Zp.p.chains
                        (Desc.K14.beforePointOf Np))
                      (VerifiableInference.Desc.K12.Seat.tests
                        Np)).second.last.asBare])
                (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).l₂
            (Desc.K14.Law.Sh.ex
              (Desc.K14.Law.ShPlan.mk
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                  Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np))
                (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                  Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
                (Desc.K14.Law.rad2At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (Desc.K14.Law.rad5At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                Johnson.G.dryProofFull.2.1 2)
              (Desc.K14.Law.ShOpen.mk (P₀ := ProofFile.InstPub)
                (P₁ := ProofFile.InstPub × VerifiableInference.Desc.First.S)
                (Cells :=
                  ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                      (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                      (P5J.At.EAt Zs)).conf.I))
                (Tok := P5J.At.Tok)
                (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0)
                (fun a => (a.1, a.2))
                ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                    (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                    (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                      cF Zp.p.chains
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                      (VerifiableInference.Desc.K12.Seat.tests Np)))
                  ▸ P5J.At.smp Zp)
                (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.fullLinks (P5J.mgAtAll hAtMgA)
                (VerifiableInference.Desc.K13.whereOf Zp)
                ((Desc.K14.Law.Sh.openAt₀
                    (Cells :=
                      ((VerifiableInference.OnPublicFiles.kcReq
                          OnBytes.Flat.numsFull
                          (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol
                            Zs.KL)
                          (P5J.At.EAt Zs)).conf.I))
                    (Tok := P5J.At.Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                    cF (fun _ _ => 0)
                    (Desc.K14.Law.matN (frS.toDecR frZ 402653181)
                      OnBytes.Flat.numsFull)
                    (Desc.K14.Law.heldFull
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                      (Desc.K14.p14Of Zp.p.chains
                        (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                      (Desc.K14.Law.full_index
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np)).par.S
                        (Desc.K14.Law.full_of_shape map14_hx
                          (Desc.K14.Law.written_in_scope hAtMgA.scope
                            hAtMgA.laid.pub
                            (VerifiableInference.PlanWritten.sized_of_made
                              hMadePinnedP1)
                            (VerifiableInference.PlanWritten.first_of_made
                              hMadePinnedP1)
                            (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                              hAtMgA.laid.value hAtMgA.laid.planOk
                              hAtMgA.laid.data hAtMgA.laid.asks)
                            map14_hx).shape))
                      OnBytes.Flat.numsFull
                      (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                      (P5J.At.EAt Zs))
                    ⟨(P5J.At.N Zp cF), P5J.fullLinks, (P5J.mgAtAll hAtMgA),
                      ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                          (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                          (fieldF oL ProofFile.pureRoad.links Zp
                            ((H2K.JointK.sharedN Zp Np).lot)
                            ((H2K.JointK.sharedN Zp Np).start)
                            ((H2K.JointK.sharedN Zp Np).ended)
                            ((H2K.JointK.sharedN Zp Np).okInst)
                            ((H2K.JointK.sharedN Zp Np).fileOk)
                            ((H2K.JointK.sharedN Zp Np).standIns)
                            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                            (ProofFile.startS Zp) cF Zp.p.chains
                            (Desc.K14.p14Of Zp.p.chains
                              (Desc.K14.beforePointOf Np))
                            (VerifiableInference.Desc.K12.Seat.tests Np)))
                        ▸ P5J.At.smp Zp),
                      (P5J.At.ms Zp Zs.lay)⟩).R)
                (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                (Desc.K14.Law.heldFull
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                  (Desc.K14.Law.full_index
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                    (Desc.K14.Law.full_of_shape map14_hx
                      (Desc.K14.Law.written_in_scope hAtMgA.scope
                        hAtMgA.laid.pub
                        (VerifiableInference.PlanWritten.sized_of_made
                          hMadePinnedP1)
                        (VerifiableInference.PlanWritten.first_of_made
                          hMadePinnedP1)
                        (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                          hAtMgA.laid.value hAtMgA.laid.planOk hAtMgA.laid.data
                          hAtMgA.laid.asks)
                        map14_hx).shape))
                  OnBytes.Flat.numsFull
                  (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs)))
              (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₂
                0))))
        (((Desc.K14.Law.Sh.openAt₀
              (Cells :=
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                    (P5J.At.EAt Zs)).conf.I))
              (Tok := P5J.At.Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
              (fun _ _ => 0)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                      (VerifiableInference.PlanWritten.sized_of_made
                        hMadePinnedP1)
                      (VerifiableInference.PlanWritten.first_of_made
                        hMadePinnedP1)
                      (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                        hAtMgA.laid.value hAtMgA.laid.planOk hAtMgA.laid.data
                        hAtMgA.laid.asks)
                      map14_hx).shape))
                OnBytes.Flat.numsFull
                (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs))
              ⟨(P5J.At.N Zp cF), P5J.fullLinks, (P5J.mgAtAll hAtMgA),
                ((Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np
                    (Desc.K14.Law.secondAt Zp Np) cF hAtMgA.laid.planOk
                    (fieldF oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                      (ProofFile.startS Zp) cF Zp.p.chains
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                      (VerifiableInference.Desc.K12.Seat.tests Np)))
                  ▸ P5J.At.smp Zp),
                (P5J.At.ms Zp Zs.lay)⟩).R))).Q₂
      (2 ^ depthReq) 0
      ((atDesc
          (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
            (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (piecesAt (ckP .two)
            (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
              (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (DP.at frS.P.T.a)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.first.asBare)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.front.map
              VerifiableInference.Desc.Block.asBare ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.links.flatMap
              VerifiableInference.Desc.Link.blocksInOrder ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.back.map
              VerifiableInference.Desc.Block.asBare ++
              [(fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.last.asBare])
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.first.asBare)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.front.map
              VerifiableInference.Desc.Block.asBare ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.links.flatMap
              VerifiableInference.Desc.Link.blocksInOrder ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.back.map
              VerifiableInference.Desc.Block.asBare ++
              [(fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.last.asBare])
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.first.asBare)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.front.map
              VerifiableInference.Desc.Block.asBare ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.links.flatMap
              VerifiableInference.Desc.Link.blocksInOrder ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.back.map
              VerifiableInference.Desc.Block.asBare ++
              [(fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.last.asBare])
            (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).p₂
        ::
        (atDesc
          (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
            (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np))
          (piecesAt (ckP .two)
            (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
              (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (DP.at frS.P.T.a)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.first.asBare)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.front.map
              VerifiableInference.Desc.Block.asBare ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.links.flatMap
              VerifiableInference.Desc.Link.blocksInOrder ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).first.back.map
              VerifiableInference.Desc.Block.asBare ++
              [(fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).first.last.asBare])
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.first.asBare)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.front.map
              VerifiableInference.Desc.Block.asBare ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.links.flatMap
              VerifiableInference.Desc.Link.blocksInOrder ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).shared.back.map
              VerifiableInference.Desc.Block.asBare ++
              [(fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).shared.last.asBare])
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.first.asBare)
            ((fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.front.map
              VerifiableInference.Desc.Block.asBare ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.links.flatMap
              VerifiableInference.Desc.Link.blocksInOrder ++
              (fieldF oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Zp.p.chains
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (VerifiableInference.Desc.K12.Seat.tests Np)).second.back.map
              VerifiableInference.Desc.Block.asBare ++
              [(fieldF oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                  (ProofFile.startS Zp) cF Zp.p.chains
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.last.asBare])
            (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).l₂) := by
  exact k14_shared_joint_count
    (ms₁ := P5J.At.ms Zp Zs.lay) (N₁ := P5J.At.N Zp cF) (rdNA := rdNA) (rdNB := rdNB) (Zp := Zp)
    (cF := cF) (oL := oL) (Zs := Zs) (rP := rP) (hZs := hAtMgA.scope) (Np := Np)
    (smp₁ :=
        (Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np (Desc.K14.Law.secondAt Zp Np) cF
          hAtMgA.laid.planOk
          (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
            (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np)))
        ▸ P5J.At.smp Zp)
    (hI :=
        (map16_hI_hV oL Zs (DP.at frS.P.T.a) rP Zp Np cF hAtMgA.scope
          (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value hAtMgA.laid.planOk
            hAtMgA.laid.data hAtMgA.laid.asks)
          hAtMgA.laid.pub hAtMgA.laid.value hMadePinnedP1).1)
    (hV :=
        (map16_hI_hV oL Zs (DP.at frS.P.T.a) rP Zp Np cF hAtMgA.scope
          (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value hAtMgA.laid.planOk
            hAtMgA.laid.data hAtMgA.laid.asks)
          hAtMgA.laid.pub hAtMgA.laid.value hMadePinnedP1).2)
    (pp := VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (E := P5J.At.EAt Zs)
    (Mg₁ := P5J.mgAtAll hAtMgA) (h3 := VerifiableInference.OnPublicFiles.Last.h3_atAll hAtMgA) (dW := dW)
    (wEnd := wEnd) (hpub := hAtMgA.laid.pub) (hNp := hAtMgA.laid.places)
    (hpinS := VerifiableInference.PlanWritten.sized_of_made hMadePinnedP1)
    (hpinF := VerifiableInference.PlanWritten.first_of_made hMadePinnedP1)
    (hdesc := hAtMgA.laid.value) (Ld := VerifiableInference.Desc.K13.Law.LFull) (hR := hR)
    (hFar := Desc.K14.Law.Sh.testsFar_in_scope hAtMgA.scope hAtMgA.laid.pub hMadePinnedP1
        (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value hAtMgA.laid.planOk
          hAtMgA.laid.data hAtMgA.laid.asks)
        Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF hAtMgA.laid.value map14_hx
        (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
          (VerifiableInference.PlanWritten.sized_of_made hMadePinnedP1)
          (VerifiableInference.PlanWritten.first_of_made hMadePinnedP1)
          (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value hAtMgA.laid.planOk
            hAtMgA.laid.data hAtMgA.laid.asks)
          map14_hx))
    (DP := DP)
    (hlaid := hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value hAtMgA.laid.planOk
        hAtMgA.laid.data hAtMgA.laid.asks)
    (e₁ := e₁) (e₂ := e₂) (e₃ := e₃)
    (hO := map16_hO (DP.at frS.P.T.a) Zp cF oL Zs rP Np
        ((map16_hI_hV oL Zs (DP.at frS.P.T.a) rP Zp Np cF hAtMgA.scope
            (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value hAtMgA.laid.planOk
              hAtMgA.laid.data hAtMgA.laid.asks)
            hAtMgA.laid.pub hAtMgA.laid.value hMadePinnedP1).1)
        ((map16_hI_hV oL Zs (DP.at frS.P.T.a) rP Zp Np cF hAtMgA.scope
            (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value hAtMgA.laid.planOk
              hAtMgA.laid.data hAtMgA.laid.asks)
            hAtMgA.laid.pub hAtMgA.laid.value hMadePinnedP1).2)
        (VerifiableInference.PlanWritten.sized_of_made hMadePinnedP1)
        (VerifiableInference.PlanWritten.first_of_made hMadePinnedP1) xLook hAtMgA
        (Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np (Desc.K14.Law.secondAt Zp Np) cF
          hAtMgA.laid.planOk
          (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
            (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np)))
        hMadePinnedP1
        (map16_five (DP.at frS.P.T.a) Zp cF oL Zs rP Np
          (VerifiableInference.PlanWritten.sized_of_made hMadePinnedP1)
          (VerifiableInference.PlanWritten.first_of_made hMadePinnedP1) xLook hAtMgA
          (Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np (Desc.K14.Law.secondAt Zp Np) cF
            hAtMgA.laid.planOk
            (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
              (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (VerifiableInference.Desc.K12.Seat.tests Np)))
          hMadePinnedP1))
    (hJ := Desc.K14.Law.Sh.joint_atAll hAtMgA
        (Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np (Desc.K14.Law.secondAt Zp Np) cF
          hAtMgA.laid.planOk
          (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
            (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np)))
        (Desc.K14.Law.Sh.hlin_of_read hAtMgA.laid.pub Np (Desc.K14.Law.secondAt Zp Np) cF
          hAtMgA.laid.planOk
          (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
            (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np)))
        (Desc.K14.Law.Sh.hW_atAll hAtMgA
          (Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np (Desc.K14.Law.secondAt Zp Np) cF
            hAtMgA.laid.planOk
            (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
              (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (VerifiableInference.Desc.K12.Seat.tests Np)))))
    (hRd := hRd_all (DP.at frS.P.T.a) Zp cF oL Zs rP Np
        ((map16_hI_hV oL Zs (DP.at frS.P.T.a) rP Zp Np cF hAtMgA.scope
            (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value hAtMgA.laid.planOk
              hAtMgA.laid.data hAtMgA.laid.asks)
            hAtMgA.laid.pub hAtMgA.laid.value hMadePinnedP1).1)
        ((map16_hI_hV oL Zs (DP.at frS.P.T.a) rP Zp Np cF hAtMgA.scope
            (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value hAtMgA.laid.planOk
              hAtMgA.laid.data hAtMgA.laid.asks)
            hAtMgA.laid.pub hAtMgA.laid.value hMadePinnedP1).2)
        (VerifiableInference.PlanWritten.sized_of_made hMadePinnedP1)
        (VerifiableInference.PlanWritten.first_of_made hMadePinnedP1) xLook hAtMgA
        (Desc.K14.Law.Sh.hcs_of_read hAtMgA.laid.pub Np (Desc.K14.Law.secondAt Zp Np) cF
          hAtMgA.laid.planOk
          (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
            (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np))))
    (depthReq := depthReq) (hn := hn)

end Desc.K14.Law

#print axioms Desc.K14.Law.k14_shared_joint_count_closed
