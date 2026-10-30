-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerSharedJointCount.lean: K14_law's TOP AS THE FIELD shared_joint_count
(RowsTiedR, Johnson/P5J/SevenOfTiedR.lean), AT THAT STRUCTURE's
OWN LETTERS: k14_field_e_at_tables (Johnson/Desc/K14/Law/LedgerFieldEAtTables.lean) WITH the data
:= DP.at frS.P.T.a OUTRIGHT (hlaid · hdesc then speak at it) · slots := 2 ^ depthReq (hn : 2 ^
depthReq ≤ 64) · links := P5J.fullLinks; N₁ (the structure's Nn) and Mg₁ (the structure's MQ) stay letters. SO, WITH Mg₁ := THE STRUCTURE's MQ AND N₁ := ITS Nn, «shared_joint_count := k14_shared_joint_count …
    MgS ML PLm» IS ONE TERM (held by a harness at RowsTiedR, not in this library;
    at other letters it is not). IT IMPORTS Johnson/P5J/TopTablesR.lean.

Compiled with the whole library.
THE STATEMENT IS MADE BY PROGRAM: k14_field_e_at_tables's own binders, in its own words, with the
letters of the maps laid in and the paid premises struck. THE PROOF: the lines in front, then ONE
CALL of k14_field_e_at_tables by named arguments.
LETTERS LAID (3): Dw · slots · links.
PREMISES STRUCK (0): .
LETTERS THAT FALL, BOUND BY THE LINES IN FRONT OF THE CALL (0): none.
LETTERS AND PREMISES THAT COME IN (2): DP · depthReq.
What is not claimed. EVERY BINDER THAT STANDS IS A PREMISE OR A LETTER. That the premises can
be met together: NO MEMBER IS SHOWN. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.LedgerFieldEAtTables
import Johnson.P5J.MeansQ

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


/-- **The field RowsTiedR.shared_joint_count, at its own letters.** -/
theorem k14_shared_joint_count
    {Tok : Type}
    (ms₁ : List Mem)
    (N₁ : Numbers)
    (rdNA : ℕ → ℕ)
    (rdNB : ℕ → ℕ)
    (Zp : ProofFile.Pub)
    (cF : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl)
    (oL : ProofFile.SecondHashFunctionArgument)
    (Zs : VerifierAndGoals.PublicFiles)
    (rP : LPFD.Full.RunPF)
    (hZs : VerifierAndGoals.InScope Zs = true)
    (Np : H2U.Places4)
    (smp₁ : ProofFile.InstPub × First.S → (s : Sending) → (i : Fin s.l.length) → Option
        ((sigOf (qS Zp Np).codes s.l).om i).Smp)
    (hI : N₁.index.1 <
        ((Desc.K14.Law.Sh.t₁
            (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))))
    (hV : N₁.w.1 <
        ((Desc.K14.Law.Sh.t₁
            (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))))
    (pp : Inst.Model.ScalesAndPolicy)
    (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) numsFull pp))
    (Mg₁ : Meaning ProofFile.InstPub
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
    (h3 : wSitsItem ∈
        (pubSets
          Mg₁.more
          P5J.fullLinks
          (VerifiableInference.Desc.First.flatPlaces
            true
            P5J.fullLinks
            true))[(VerifiableInference.Desc.First.flatPlaces true P5J.fullLinks true).length]?.getD
        [])
    (dW : (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
    (wEnd : (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
    (hpub : ProofFile.pureRoad.pub oL Zs.pol Zs.lay Zs.KL = .ok Zp)
    (hNp : H2U.placesOfMade Zp.made = .ok Np)
    (hpinS : VerifiableInference.PlanWritten.sizedPinnedAt Zp.p.X.P Zp.p.chains.made = true)
    (hpinF : VerifiableInference.PlanWritten.firstPinnedAt Zp.p.X.P Zp.first = true)
    (hdesc : ProofFile.onlineDescription oL Zs.pol Zs.lay Zs.KL = .ok
        (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
          ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
          ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
          ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
          (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
          (VerifiableInference.Desc.K12.Seat.tests Np)))
    (Ld : VerifiableInference.Desc.K12.Door.Laid)
    (hR : Desc.K14.Law.Sh.ReachOwed oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF Ld)
    (hFar : Desc.K14.Law.Sh.TestsFar oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF Ld)
    (DP : WholeD)
    (hlaid : LPFD.Full.proofDataAndDecisionOfPublicFiles oL Zs.pol Zs.lay Zs.KL = .ok ((DP.at frS.P.T.a), rP))
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
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT) →
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
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
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT) →
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
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
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT) →
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
    (hO : Desc.K14.Law.Sh.TestsO
        (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
          ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)
        (oS ProofFile.InstPub Tok VerifiableInference.Desc.First.S (DP.at frS.P.T.a)
          (fun a => (a.1, a.2)) ms₁ N₁ P5J.fullLinks Zp k14_real.choose map14_hx
          ((Desc.K14.Law.Sh.openAt₀
              (Cells :=
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
              (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF (fun _ _ => 0)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                      map14_hx).shape))
                OnBytes.Flat.numsFull pp E)
              ⟨N₁, P5J.fullLinks, Mg₁, smp₁, ms₁⟩).R)
          oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub hpinS hpinF)
        ((Desc.K14.Law.Sh.t₁
            (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))))
    (hJ : Desc.K14.Law.Sh.Joint
        (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
          ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)
        (oS ProofFile.InstPub Tok VerifiableInference.Desc.First.S (DP.at frS.P.T.a)
          (fun a => (a.1, a.2)) ms₁ N₁ P5J.fullLinks Zp k14_real.choose map14_hx
          ((Desc.K14.Law.Sh.openAt₀
              (Cells :=
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
              (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF (fun _ _ => 0)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                      map14_hx).shape))
                OnBytes.Flat.numsFull pp E)
              ⟨N₁, P5J.fullLinks, Mg₁, smp₁, ms₁⟩).R)
          oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub hpinS hpinF))
    (hRd : Desc.K14.Law.Sh.Reads
        (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
          ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)
        (oS ProofFile.InstPub Tok VerifiableInference.Desc.First.S (DP.at frS.P.T.a)
          (fun a => (a.1, a.2)) ms₁ N₁ P5J.fullLinks Zp k14_real.choose map14_hx
          ((Desc.K14.Law.Sh.openAt₀
              (Cells :=
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
              (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF (fun _ _ => 0)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                      map14_hx).shape))
                OnBytes.Flat.numsFull pp E)
              ⟨N₁, P5J.fullLinks, Mg₁, smp₁, ms₁⟩).R)
          oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub hpinS hpinF)
        ((Desc.K14.Law.Sh.t₁
            (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))))
    (depthReq : ℕ)
    (hn : (2 ^ depthReq) ≤ 64) :
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
        ((fun a => (a.1, a.2))) N₁ Mg₁ P5J.fullLinks
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
              ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
            (Tok := Tok) (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
            (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
            smp₁ ms₁ N₁ P5J.fullLinks Mg₁ (VerifiableInference.Desc.K13.whereOf Zp)
            ((Desc.K14.Law.Sh.openAt₀
                (Cells :=
                  ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                      pp E).conf.I))
                (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                (fun _ _ => 0)
                (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                (Desc.K14.Law.heldFull
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                  (Desc.K14.Law.full_index
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                    (Desc.K14.Law.full_of_shape map14_hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF
                        hlaid map14_hx).shape))
                  OnBytes.Flat.numsFull pp E)
                ⟨N₁, P5J.fullLinks, Mg₁, smp₁, ms₁⟩).R)
            (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
            (Desc.K14.Law.heldFull
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
              (Desc.K14.p14Of Zp.p.chains
                (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
              (Desc.K14.Law.full_index
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                (Desc.K14.Law.full_of_shape map14_hx
                  (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                    map14_hx).shape))
              OnBytes.Flat.numsFull pp E)))
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
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
              (Tok := Tok) (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
              smp₁ ms₁ N₁ P5J.fullLinks Mg₁ (VerifiableInference.Desc.K13.whereOf Zp)
              ((Desc.K14.Law.Sh.openAt₀
                  (Cells :=
                    ((VerifiableInference.OnPublicFiles.kcReq
                        OnBytes.Flat.numsFull pp E).conf.I))
                  (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                  (fun _ _ => 0)
                  (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                  (Desc.K14.Law.heldFull
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                    (Desc.K14.Law.full_index
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                      (Desc.K14.Law.full_of_shape map14_hx
                        (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF
                          hlaid map14_hx).shape))
                    OnBytes.Flat.numsFull pp E)
                  ⟨N₁, P5J.fullLinks, Mg₁, smp₁, ms₁⟩).R)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                      map14_hx).shape))
                OnBytes.Flat.numsFull pp E)))
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
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
              (Tok := Tok) (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
              smp₁ ms₁ N₁ P5J.fullLinks Mg₁ (VerifiableInference.Desc.K13.whereOf Zp)
              ((Desc.K14.Law.Sh.openAt₀
                  (Cells :=
                    ((VerifiableInference.OnPublicFiles.kcReq
                        OnBytes.Flat.numsFull pp E).conf.I))
                  (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                  (fun _ _ => 0)
                  (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                  (Desc.K14.Law.heldFull
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                    (Desc.K14.Law.full_index
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                      (Desc.K14.Law.full_of_shape map14_hx
                        (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF
                          hlaid map14_hx).shape))
                    OnBytes.Flat.numsFull pp E)
                  ⟨N₁, P5J.fullLinks, Mg₁, smp₁, ms₁⟩).R)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                      map14_hx).shape))
                OnBytes.Flat.numsFull pp E)))
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
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
              (Tok := Tok) (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
              smp₁ ms₁ N₁ P5J.fullLinks Mg₁ (VerifiableInference.Desc.K13.whereOf Zp)
              ((Desc.K14.Law.Sh.openAt₀
                  (Cells :=
                    ((VerifiableInference.OnPublicFiles.kcReq
                        OnBytes.Flat.numsFull pp E).conf.I))
                  (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                  (fun _ _ => 0)
                  (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                  (Desc.K14.Law.heldFull
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                    (Desc.K14.Law.full_index
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                      (Desc.K14.Law.full_of_shape map14_hx
                        (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF
                          hlaid map14_hx).shape))
                    OnBytes.Flat.numsFull pp E)
                  ⟨N₁, P5J.fullLinks, Mg₁, smp₁, ms₁⟩).R)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                      map14_hx).shape))
                OnBytes.Flat.numsFull pp E)))
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
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
              (Tok := Tok) (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
              smp₁ ms₁ N₁ P5J.fullLinks Mg₁ (VerifiableInference.Desc.K13.whereOf Zp)
              ((Desc.K14.Law.Sh.openAt₀
                  (Cells :=
                    ((VerifiableInference.OnPublicFiles.kcReq
                        OnBytes.Flat.numsFull pp E).conf.I))
                  (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                  (fun _ _ => 0)
                  (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                  (Desc.K14.Law.heldFull
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                    (Desc.K14.Law.full_index
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                      (Desc.K14.Law.full_of_shape map14_hx
                        (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF
                          hlaid map14_hx).shape))
                    OnBytes.Flat.numsFull pp E)
                  ⟨N₁, P5J.fullLinks, Mg₁, smp₁, ms₁⟩).R)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                      map14_hx).shape))
                OnBytes.Flat.numsFull pp E)))
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
                  ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp
                      E).conf.I))
                (Tok := Tok)
                (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0)
                (fun a => (a.1, a.2)) smp₁ ms₁ N₁ P5J.fullLinks Mg₁
                (VerifiableInference.Desc.K13.whereOf Zp)
                ((Desc.K14.Law.Sh.openAt₀
                    (Cells :=
                      ((VerifiableInference.OnPublicFiles.kcReq
                          OnBytes.Flat.numsFull pp E).conf.I))
                    (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                    (fun _ _ => 0)
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
                          (Desc.K14.Law.written_in_scope hZs hpub hpinS
                            hpinF hlaid map14_hx).shape))
                      OnBytes.Flat.numsFull pp E)
                    ⟨N₁, P5J.fullLinks, Mg₁, smp₁, ms₁⟩).R)
                (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                (Desc.K14.Law.heldFull
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                  (Desc.K14.Law.full_index
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                    (Desc.K14.Law.full_of_shape map14_hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                        map14_hx).shape))
                  OnBytes.Flat.numsFull pp E)))
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
                  ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp
                      E).conf.I))
                (Tok := Tok)
                (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0)
                (fun a => (a.1, a.2)) smp₁ ms₁ N₁ P5J.fullLinks Mg₁
                (VerifiableInference.Desc.K13.whereOf Zp)
                ((Desc.K14.Law.Sh.openAt₀
                    (Cells :=
                      ((VerifiableInference.OnPublicFiles.kcReq
                          OnBytes.Flat.numsFull pp E).conf.I))
                    (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                    (fun _ _ => 0)
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
                          (Desc.K14.Law.written_in_scope hZs hpub hpinS
                            hpinF hlaid map14_hx).shape))
                      OnBytes.Flat.numsFull pp E)
                    ⟨N₁, P5J.fullLinks, Mg₁, smp₁, ms₁⟩).R)
                (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                (Desc.K14.Law.heldFull
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                  (Desc.K14.Law.full_index
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                    (Desc.K14.Law.full_of_shape map14_hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                        map14_hx).shape))
                  OnBytes.Flat.numsFull pp E))
              (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₂
                0))))
        (((Desc.K14.Law.Sh.openAt₀
              (Cells :=
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
              (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
              (fun _ _ => 0)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                      map14_hx).shape))
                OnBytes.Flat.numsFull pp E)
              ⟨N₁, P5J.fullLinks, Mg₁, smp₁, ms₁⟩).R))).on₂
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
        ((fun a => (a.1, a.2))) N₁ Mg₁ P5J.fullLinks
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
              ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
            (Tok := Tok) (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
            (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2)) smp₁
            ms₁ N₁ P5J.fullLinks Mg₁ (VerifiableInference.Desc.K13.whereOf Zp)
            ((Desc.K14.Law.Sh.openAt₀
                (Cells :=
                  ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull
                      pp E).conf.I))
                (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                (fun _ _ => 0)
                (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                (Desc.K14.Law.heldFull
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                  (Desc.K14.Law.full_index
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                    (Desc.K14.Law.full_of_shape map14_hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF
                        hlaid map14_hx).shape))
                  OnBytes.Flat.numsFull pp E)
                ⟨N₁, P5J.fullLinks, Mg₁, smp₁, ms₁⟩).R)
            (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
            (Desc.K14.Law.heldFull
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
              (Desc.K14.p14Of Zp.p.chains
                (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
              (Desc.K14.Law.full_index
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                (Desc.K14.Law.full_of_shape map14_hx
                  (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                    map14_hx).shape))
              OnBytes.Flat.numsFull pp E)))
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
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
              (Tok := Tok) (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
              smp₁ ms₁ N₁ P5J.fullLinks Mg₁ (VerifiableInference.Desc.K13.whereOf Zp)
              ((Desc.K14.Law.Sh.openAt₀
                  (Cells :=
                    ((VerifiableInference.OnPublicFiles.kcReq
                        OnBytes.Flat.numsFull pp E).conf.I))
                  (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                  (fun _ _ => 0)
                  (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                  (Desc.K14.Law.heldFull
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                    (Desc.K14.Law.full_index
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                      (Desc.K14.Law.full_of_shape map14_hx
                        (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF
                          hlaid map14_hx).shape))
                    OnBytes.Flat.numsFull pp E)
                  ⟨N₁, P5J.fullLinks, Mg₁, smp₁, ms₁⟩).R)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                      map14_hx).shape))
                OnBytes.Flat.numsFull pp E)))
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
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
              (Tok := Tok) (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
              smp₁ ms₁ N₁ P5J.fullLinks Mg₁ (VerifiableInference.Desc.K13.whereOf Zp)
              ((Desc.K14.Law.Sh.openAt₀
                  (Cells :=
                    ((VerifiableInference.OnPublicFiles.kcReq
                        OnBytes.Flat.numsFull pp E).conf.I))
                  (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                  (fun _ _ => 0)
                  (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                  (Desc.K14.Law.heldFull
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                    (Desc.K14.Law.full_index
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                      (Desc.K14.Law.full_of_shape map14_hx
                        (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF
                          hlaid map14_hx).shape))
                    OnBytes.Flat.numsFull pp E)
                  ⟨N₁, P5J.fullLinks, Mg₁, smp₁, ms₁⟩).R)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                      map14_hx).shape))
                OnBytes.Flat.numsFull pp E)))
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
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
              (Tok := Tok) (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
              smp₁ ms₁ N₁ P5J.fullLinks Mg₁ (VerifiableInference.Desc.K13.whereOf Zp)
              ((Desc.K14.Law.Sh.openAt₀
                  (Cells :=
                    ((VerifiableInference.OnPublicFiles.kcReq
                        OnBytes.Flat.numsFull pp E).conf.I))
                  (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                  (fun _ _ => 0)
                  (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                  (Desc.K14.Law.heldFull
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                    (Desc.K14.Law.full_index
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                      (Desc.K14.Law.full_of_shape map14_hx
                        (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF
                          hlaid map14_hx).shape))
                    OnBytes.Flat.numsFull pp E)
                  ⟨N₁, P5J.fullLinks, Mg₁, smp₁, ms₁⟩).R)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                      map14_hx).shape))
                OnBytes.Flat.numsFull pp E)))
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
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
              (Tok := Tok) (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
              (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
              smp₁ ms₁ N₁ P5J.fullLinks Mg₁ (VerifiableInference.Desc.K13.whereOf Zp)
              ((Desc.K14.Law.Sh.openAt₀
                  (Cells :=
                    ((VerifiableInference.OnPublicFiles.kcReq
                        OnBytes.Flat.numsFull pp E).conf.I))
                  (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                  (fun _ _ => 0)
                  (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                  (Desc.K14.Law.heldFull
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                    (Desc.K14.Law.full_index
                      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                      (Desc.K14.Law.full_of_shape map14_hx
                        (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF
                          hlaid map14_hx).shape))
                    OnBytes.Flat.numsFull pp E)
                  ⟨N₁, P5J.fullLinks, Mg₁, smp₁, ms₁⟩).R)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                      map14_hx).shape))
                OnBytes.Flat.numsFull pp E)))
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
                  ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
                (Tok := Tok)
                (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0)
                (fun a => (a.1, a.2)) smp₁ ms₁ N₁ P5J.fullLinks Mg₁
                (VerifiableInference.Desc.K13.whereOf Zp)
                ((Desc.K14.Law.Sh.openAt₀
                    (Cells :=
                      ((VerifiableInference.OnPublicFiles.kcReq
                          OnBytes.Flat.numsFull pp E).conf.I))
                    (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                    (fun _ _ => 0)
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
                          (Desc.K14.Law.written_in_scope hZs hpub hpinS
                            hpinF hlaid map14_hx).shape))
                      OnBytes.Flat.numsFull pp E)
                    ⟨N₁, P5J.fullLinks, Mg₁, smp₁, ms₁⟩).R)
                (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                (Desc.K14.Law.heldFull
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                  (Desc.K14.Law.full_index
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                    (Desc.K14.Law.full_of_shape map14_hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                        map14_hx).shape))
                  OnBytes.Flat.numsFull pp E)))
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
                  ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
                (Tok := Tok)
                (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0)
                (fun a => (a.1, a.2)) smp₁ ms₁ N₁ P5J.fullLinks Mg₁
                (VerifiableInference.Desc.K13.whereOf Zp)
                ((Desc.K14.Law.Sh.openAt₀
                    (Cells :=
                      ((VerifiableInference.OnPublicFiles.kcReq
                          OnBytes.Flat.numsFull pp E).conf.I))
                    (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                    (fun _ _ => 0)
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
                          (Desc.K14.Law.written_in_scope hZs hpub hpinS
                            hpinF hlaid map14_hx).shape))
                      OnBytes.Flat.numsFull pp E)
                    ⟨N₁, P5J.fullLinks, Mg₁, smp₁, ms₁⟩).R)
                (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                (Desc.K14.Law.heldFull
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                  (Desc.K14.p14Of Zp.p.chains
                    (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                  (Desc.K14.Law.full_index
                    (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                    (Desc.K14.Law.full_of_shape map14_hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                        map14_hx).shape))
                  OnBytes.Flat.numsFull pp E))
              (frameAt (DP.at frS.P.T.a) (allOf (DP.at frS.P.T.a)) (DP.at frS.P.T.a).key₂
                0))))
        (((Desc.K14.Law.Sh.openAt₀
              (Cells :=
                ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
              (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF (fun _ _ => 0)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                      map14_hx).shape))
                OnBytes.Flat.numsFull pp E)
              ⟨N₁, P5J.fullLinks, Mg₁, smp₁, ms₁⟩).R))).Q₂
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
  exact k14_field_e_at_tables
    (Dw := DP.at frS.P.T.a) (ms₁ := ms₁) (N₁ := N₁) (links := P5J.fullLinks) (slots := 2 ^ depthReq)
    (hn := hn) (rdNA := rdNA) (rdNB := rdNB) (Zp := Zp) (cF := cF) (oL := oL) (Zs := Zs) (rP := rP)
    (hZs := hZs) (hlaid := hlaid) (Np := Np) (smp₁ := smp₁) (hI := hI) (hV := hV) (pp := pp)
    (E := E) (Mg₁ := Mg₁) (h3 := h3) (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) (dW := dW) (wEnd := wEnd)
    (hpub := hpub) (hNp := hNp) (hpinS := hpinS) (hpinF := hpinF) (hO := hO) (hJ := hJ) (hRd := hRd)
    (hdesc := hdesc) (Ld := Ld) (hR := hR) (hFar := hFar)

end Desc.K14.Law

#print axioms Desc.K14.Law.k14_shared_joint_count
