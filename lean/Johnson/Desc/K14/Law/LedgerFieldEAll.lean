-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerFieldEAll.lean: k14_field_e (Johnson/Desc/K14/Law/LedgerFieldE.lean) AT
THE CLOSED CONSTANT: THE FIRST TABLE's FIVE LETTERS AND Tok · pp · E LAID (N₁ := P5J.At.N Zp cF
· links := P5J.At.links · Mg₁ := P5J.mgAtAll hAtMgA · smp₁ := eCodes ▸ P5J.At.smp Zp · ms₁ :=
P5J.At.ms Zp Zs.lay · Tok := P5J.At.Tok · pp := ppAtFiles Zs.pol Zs.KL · E := P5J.At.EAt Zs): O IS
THEN Sh.openAll hAtMgA eCodes; FIVE PREMISES OF THE SCOPE FALL TO FIELDS OF THE HEAD hAtMgA
(hZs · hpub · hNp · hdesc · hlaid). IT IMPORTS Johnson/P5J/MgAtAll.lean.
Compiled with the whole library.
THE STATEMENT IS MADE BY PROGRAM: k14_field_e's own binders, in its own words, with the letters of
the maps laid in and the paid premises struck. THE PROOF: the lines in front, then ONE CALL of
k14_field_e by named arguments.
LETTERS LAID (8): Tok · pp · E · N₁ · links · ms₁ · smp₁ · Mg₁.
PREMISES STRUCK (5): hZs · hpub · hNp · hdesc · hlaid.
LETTERS THAT FALL, BOUND BY THE LINES IN FRONT OF THE CALL (0): none.
LETTERS AND PREMISES THAT COME IN (3): xLook · hAtMgA · eCodes.
What is not claimed. EVERY BINDER THAT STANDS IS A PREMISE OR A LETTER STILL. That the premises can
be met together: NO MEMBER IS SHOWN. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.LedgerFieldE
import Johnson.P5J.LettersAt
import Johnson.P5J.DecFree
import Johnson.P5J.MgAtAll
import Johnson.Desc.K14.Law.SharedConstCodesAt

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


/-- **The field shared_joint_count's own text, at the closed constant (P5J.mgAtAll).** -/
theorem k14_field_e_all
    (Dw : WholeD)
    (slots : ℕ)
    (hn : slots ≤ 64)
    (rdNA : ℕ → ℕ)
    (rdNB : ℕ → ℕ)
    (Zp : ProofFile.Pub)
    (cF : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl)
    (oL : ProofFile.SecondHashFunctionArgument)
    (Zs : VerifierAndGoals.PublicFiles)
    (rP : LPFD.Full.RunPF)
    (Np : H2U.Places4)
    (hI : (P5J.At.N Zp cF).index.1 <
        ((Desc.K14.Law.Sh.t₁
            (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))))
    (hV : (P5J.At.N Zp cF).w.1 <
        ((Desc.K14.Law.Sh.t₁
            (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))))
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
        × (frameAt Dw (allOf Dw) Dw.key₁ 0).E.Str → Iop.Tr (uLT (ckP .two) ds) →
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
        × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr (uLT (ckP .two) ds) →
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
        (frameAt Dw (allOf Dw) Dw.key₃
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
    (hpinS : VerifiableInference.PlanWritten.sizedPinnedAt Zp.p.X.P Zp.p.chains.made = true)
    (hpinF : VerifiableInference.PlanWritten.firstPinnedAt Zp.p.X.P Zp.first = true)
    (Ld : VerifiableInference.Desc.K12.Door.Laid)
    (hR : Desc.K14.Law.Sh.ReachOwed oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF Ld)
    (hFar : Desc.K14.Law.Sh.TestsFar oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF Ld)
    (xLook : VerifiableInference.Desc.First.Look.Place)
    (hAtMgA : P5J.AtMgA oL Zs Dw rP Zp Np cF xLook)
    (h3 : wSitsItem ∈
        (pubSets
          (P5J.mgAtAll
            hAtMgA).more
          P5J.At.links
          (VerifiableInference.Desc.First.flatPlaces
            true
            P5J.At.links
            true))[(VerifiableInference.Desc.First.flatPlaces true P5J.At.links true).length]?.getD
        [])
    (eCodes : P5J.At.cs Zp = (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).codes)
    (hO : Desc.K14.Law.Sh.TestsO
        (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
          ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)
        (oS ProofFile.InstPub P5J.At.Tok VerifiableInference.Desc.First.S Dw (fun a => (a.1, a.2))
          (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.At.links Zp k14_real.choose map14_hx
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
                    (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                      hpinS hpinF
                      (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                        hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                      map14_hx).shape))
                OnBytes.Flat.numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                (P5J.At.EAt Zs))
              ⟨(P5J.At.N Zp cF), P5J.At.links, (P5J.mgAtAll hAtMgA),
                (eCodes ▸ P5J.At.smp Zp), (P5J.At.ms Zp Zs.lay)⟩).R)
          oL Zs rP hAtMgA.scope
          (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value hAtMgA.laid.planOk
            hAtMgA.laid.data hAtMgA.laid.asks)
          Np (eCodes ▸ P5J.At.smp Zp) (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
          (P5J.At.EAt Zs) (P5J.mgAtAll hAtMgA) hAtMgA.laid.pub hpinS hpinF)
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
        (oS ProofFile.InstPub P5J.At.Tok VerifiableInference.Desc.First.S Dw (fun a => (a.1, a.2))
          (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.At.links Zp k14_real.choose map14_hx
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
                    (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                      hpinS hpinF
                      (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                        hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                      map14_hx).shape))
                OnBytes.Flat.numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                (P5J.At.EAt Zs))
              ⟨(P5J.At.N Zp cF), P5J.At.links, (P5J.mgAtAll hAtMgA),
                (eCodes ▸ P5J.At.smp Zp), (P5J.At.ms Zp Zs.lay)⟩).R)
          oL Zs rP hAtMgA.scope
          (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value hAtMgA.laid.planOk
            hAtMgA.laid.data hAtMgA.laid.asks)
          Np (eCodes ▸ P5J.At.smp Zp) (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
          (P5J.At.EAt Zs) (P5J.mgAtAll hAtMgA) hAtMgA.laid.pub hpinS hpinF))
    (hRd : Desc.K14.Law.Sh.Reads
        (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
          ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)
        (oS ProofFile.InstPub P5J.At.Tok VerifiableInference.Desc.First.S Dw (fun a => (a.1, a.2))
          (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.At.links Zp k14_real.choose map14_hx
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
                    (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                      hpinS hpinF
                      (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                        hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                      map14_hx).shape))
                OnBytes.Flat.numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                (P5J.At.EAt Zs))
              ⟨(P5J.At.N Zp cF), P5J.At.links, (P5J.mgAtAll hAtMgA),
                (eCodes ▸ P5J.At.smp Zp), (P5J.At.ms Zp Zs.lay)⟩).R)
          oL Zs rP hAtMgA.scope
          (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value hAtMgA.laid.planOk
            hAtMgA.laid.data hAtMgA.laid.asks)
          Np (eCodes ▸ P5J.At.smp Zp) (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
          (P5J.At.EAt Zs) (P5J.mgAtAll hAtMgA) hAtMgA.laid.pub hpinS hpinF)
        ((Desc.K14.Law.Sh.t₁
            (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)))) :
    EachLawsBN
      (keyAt Prod.snd Dw.t₁
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
            Dw
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
            Dw
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
      (onQ₂
        ((tiedNumbers (P5J.At.N Zp cF)
            (Desc.K14.Law.Fence.numbersSh
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
              (0, 0) (0, 0))))
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
            (Tok := P5J.At.Tok) (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
            (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
            (eCodes ▸ P5J.At.smp Zp) (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.At.links
            (P5J.mgAtAll hAtMgA) (VerifiableInference.Desc.K13.whereOf Zp)
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
                      (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                        hpinS hpinF
                        (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                          hAtMgA.laid.value hAtMgA.laid.planOk hAtMgA.laid.data
                          hAtMgA.laid.asks)
                        map14_hx).shape))
                  OnBytes.Flat.numsFull
                  (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs))
                ⟨(P5J.At.N Zp cF), P5J.At.links, (P5J.mgAtAll hAtMgA),
                  (eCodes ▸ P5J.At.smp Zp), (P5J.At.ms Zp Zs.lay)⟩).R)
            (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
            (Desc.K14.Law.heldFull
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
              (Desc.K14.p14Of Zp.p.chains
                (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
              (Desc.K14.Law.full_index
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                (Desc.K14.Law.full_of_shape map14_hx
                  (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub hpinS
                    hpinF
                    (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                      hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                    map14_hx).shape))
              OnBytes.Flat.numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
              (P5J.At.EAt Zs))))
        ((ocWith
            (ocEnd (fun a => (a.1, a.2)) (P5J.At.N Zp cF) (P5J.mgAtAll hAtMgA) P5J.At.links
              (VerifiableInference.Desc.First.flatPlaces true P5J.At.links true))
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
                      (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                        hpinS hpinF
                        (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                          hAtMgA.laid.value hAtMgA.laid.planOk hAtMgA.laid.data
                          hAtMgA.laid.asks)
                        map14_hx).shape))
                  OnBytes.Flat.numsFull
                  (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs))
                ⟨(P5J.At.N Zp cF), P5J.At.links, (P5J.mgAtAll hAtMgA),
                  (eCodes ▸ P5J.At.smp Zp), (P5J.At.ms Zp Zs.lay)⟩).R)))
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
              ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
              (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (VerifiableInference.Desc.K12.Seat.tests Np))
            Dw
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
            Dw
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
      (stepAt
        (Desc.K14.Law.Sh.nums
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
            (Tok := P5J.At.Tok) (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
            (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
            (eCodes ▸ P5J.At.smp Zp) (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.At.links
            (P5J.mgAtAll hAtMgA) (VerifiableInference.Desc.K13.whereOf Zp)
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
                      (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                        hpinS hpinF
                        (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                          hAtMgA.laid.value hAtMgA.laid.planOk hAtMgA.laid.data
                          hAtMgA.laid.asks)
                        map14_hx).shape))
                  OnBytes.Flat.numsFull
                  (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs))
                ⟨(P5J.At.N Zp cF), P5J.At.links, (P5J.mgAtAll hAtMgA),
                  (eCodes ▸ P5J.At.smp Zp), (P5J.At.ms Zp Zs.lay)⟩).R)
            (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
            (Desc.K14.Law.heldFull
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
              (Desc.K14.p14Of Zp.p.chains
                (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
              (Desc.K14.Law.full_index
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                (Desc.K14.Law.full_of_shape map14_hx
                  (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub hpinS
                    hpinF
                    (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                      hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                    map14_hx).shape))
              OnBytes.Flat.numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
              (P5J.At.EAt Zs))))
        (Desc.K14.Law.Sh.mg
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
            (Tok := P5J.At.Tok) (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
            (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
            (eCodes ▸ P5J.At.smp Zp) (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.At.links
            (P5J.mgAtAll hAtMgA) (VerifiableInference.Desc.K13.whereOf Zp)
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
                      (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                        hpinS hpinF
                        (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                          hAtMgA.laid.value hAtMgA.laid.planOk hAtMgA.laid.data
                          hAtMgA.laid.asks)
                        map14_hx).shape))
                  OnBytes.Flat.numsFull
                  (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs))
                ⟨(P5J.At.N Zp cF), P5J.At.links, (P5J.mgAtAll hAtMgA),
                  (eCodes ▸ P5J.At.smp Zp), (P5J.At.ms Zp Zs.lay)⟩).R)
            (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
            (Desc.K14.Law.heldFull
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
              (Desc.K14.p14Of Zp.p.chains
                (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
              (Desc.K14.Law.full_index
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                (Desc.K14.Law.full_of_shape map14_hx
                  (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub hpinS
                    hpinF
                    (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                      hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                    map14_hx).shape))
              OnBytes.Flat.numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
              (P5J.At.EAt Zs))))
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
            (Tok := P5J.At.Tok) (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
            (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
            (eCodes ▸ P5J.At.smp Zp) (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.At.links
            (P5J.mgAtAll hAtMgA) (VerifiableInference.Desc.K13.whereOf Zp)
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
                      (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                        hpinS hpinF
                        (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                          hAtMgA.laid.value hAtMgA.laid.planOk hAtMgA.laid.data
                          hAtMgA.laid.asks)
                        map14_hx).shape))
                  OnBytes.Flat.numsFull
                  (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs))
                ⟨(P5J.At.N Zp cF), P5J.At.links, (P5J.mgAtAll hAtMgA),
                  (eCodes ▸ P5J.At.smp Zp), (P5J.At.ms Zp Zs.lay)⟩).R)
            (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
            (Desc.K14.Law.heldFull
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
              (Desc.K14.p14Of Zp.p.chains
                (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
              (Desc.K14.Law.full_index
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                (Desc.K14.Law.full_of_shape map14_hx
                  (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub hpinS
                    hpinF
                    (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                      hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                    map14_hx).shape))
              OnBytes.Flat.numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
              (P5J.At.EAt Zs))))
        (Desc.K14.Law.Sh.own
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
            (Tok := P5J.At.Tok) (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
            (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2))
            (eCodes ▸ P5J.At.smp Zp) (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.At.links
            (P5J.mgAtAll hAtMgA) (VerifiableInference.Desc.K13.whereOf Zp)
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
                      (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                        hpinS hpinF
                        (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                          hAtMgA.laid.value hAtMgA.laid.planOk hAtMgA.laid.data
                          hAtMgA.laid.asks)
                        map14_hx).shape))
                  OnBytes.Flat.numsFull
                  (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs))
                ⟨(P5J.At.N Zp cF), P5J.At.links, (P5J.mgAtAll hAtMgA),
                  (eCodes ▸ P5J.At.smp Zp), (P5J.At.ms Zp Zs.lay)⟩).R)
            (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
            (Desc.K14.Law.heldFull
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
              (Desc.K14.p14Of Zp.p.chains
                (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
              (Desc.K14.Law.full_index
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                (Desc.K14.Law.full_of_shape map14_hx
                  (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub hpinS
                    hpinF
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
              ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
              (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (VerifiableInference.Desc.K12.Seat.tests Np))
            Dw
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
            Dw
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
            (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).l₂
        (extOf
          (Desc.K14.Law.Sh.nums
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
              (eCodes ▸ P5J.At.smp Zp) (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.At.links
              (P5J.mgAtAll hAtMgA) (VerifiableInference.Desc.K13.whereOf Zp)
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
                          hAtMgA.laid.pub hpinS hpinF
                          (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                            hAtMgA.laid.value hAtMgA.laid.planOk
                            hAtMgA.laid.data hAtMgA.laid.asks)
                          map14_hx).shape))
                    OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs))
                  ⟨(P5J.At.N Zp cF), P5J.At.links, (P5J.mgAtAll hAtMgA),
                    (eCodes ▸ P5J.At.smp Zp), (P5J.At.ms Zp Zs.lay)⟩).R)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                      hpinS hpinF
                      (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                        hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                      map14_hx).shape))
                OnBytes.Flat.numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                (P5J.At.EAt Zs))))
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
              Dw
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
              Dw
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
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                    (ProofFile.startS Zp) cF Zp.p.chains
                    (Desc.K14.p14Of Zp.p.chains
                      (Desc.K14.beforePointOf Np))
                    (VerifiableInference.Desc.K12.Seat.tests Np)).second.last.asBare])
              (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).l₂
          (Desc.K14.Law.Sh.ex
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
              (eCodes ▸ P5J.At.smp Zp) (P5J.At.ms Zp Zs.lay) (P5J.At.N Zp cF) P5J.At.links
              (P5J.mgAtAll hAtMgA) (VerifiableInference.Desc.K13.whereOf Zp)
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
                          hAtMgA.laid.pub hpinS hpinF
                          (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of
                            hAtMgA.laid.value hAtMgA.laid.planOk
                            hAtMgA.laid.data hAtMgA.laid.asks)
                          map14_hx).shape))
                    OnBytes.Flat.numsFull
                    (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (P5J.At.EAt Zs))
                  ⟨(P5J.At.N Zp cF), P5J.At.links, (P5J.mgAtAll hAtMgA),
                    (eCodes ▸ P5J.At.smp Zp), (P5J.At.ms Zp Zs.lay)⟩).R)
              (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
              (Desc.K14.Law.heldFull
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
                (Desc.K14.p14Of Zp.p.chains
                  (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hAtMgA.scope hAtMgA.laid.pub
                      hpinS hpinF
                      (hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value
                        hAtMgA.laid.planOk hAtMgA.laid.data hAtMgA.laid.asks)
                      map14_hx).shape))
                OnBytes.Flat.numsFull (VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL)
                (P5J.At.EAt Zs)))
            (frameAt Dw (allOf Dw) Dw.key₂ 0))))
      slots 0
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
            Dw
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
            Dw
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
  exact k14_field_e
    (Dw := Dw) (ms₁ := P5J.At.ms Zp Zs.lay) (N₁ := P5J.At.N Zp cF) (links := P5J.At.links)
    (slots := slots) (hn := hn) (rdNA := rdNA) (rdNB := rdNB) (Zp := Zp) (cF := cF) (oL := oL)
    (Zs := Zs) (rP := rP) (hZs := hAtMgA.scope)
    (hlaid := hAtMgA.laid.run ▸ LPFD.Full.laidPOf_of hAtMgA.laid.value hAtMgA.laid.planOk
        hAtMgA.laid.data hAtMgA.laid.asks)
    (Np := Np) (smp₁ := eCodes ▸ P5J.At.smp Zp) (hI := hI) (hV := hV)
    (pp := VerifiableInference.OnPublicFiles.ppAtFiles Zs.pol Zs.KL) (E := P5J.At.EAt Zs)
    (Mg₁ := P5J.mgAtAll hAtMgA) (h3 := h3) (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) (dW := dW)
    (wEnd := wEnd) (hpub := hAtMgA.laid.pub) (hNp := hAtMgA.laid.places) (hpinS := hpinS)
    (hpinF := hpinF) (hO := hO) (hJ := hJ) (hRd := hRd) (hdesc := hAtMgA.laid.value) (Ld := Ld)
    (hR := hR) (hFar := hFar)

end Desc.K14.Law

#print axioms Desc.K14.Law.k14_field_e_all
