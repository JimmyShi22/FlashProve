-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerFieldScope.lean: THE LEDGER's END IN THE FIELD's OWN TEXT, AT THE SEAT
THAT THE VERIFIER MAKES, WITH SIX MORE PREMISES PAID OUT OF THE SCOPE's OWN
(Johnson/Desc/K14/Law/LedgerScopeTerms.lean): tA · tB (firstTie_in_scope_U | _O) · fSp9 · fSp10
(fSp_written_U | _O) · hTold (toldFit_written) · hx (x := k14_real.choose). THE
NUMBER OF SLOTS STAYS A LETTER UNDER hn : slots ≤ 64, so that whoever joins can lay it.
ledger_field_seat (Johnson/Desc/K14/Law/LedgerFieldSeat.lean) is called once.
THE STATEMENT IS MADE BY PROGRAM: ledger_field_seat's own binders, in its own words, with the
letters of the maps laid in and the paid premises struck. THE PROOF: the lines in front, then ONE
CALL of ledger_field_seat by named arguments.
LETTERS LAID (1): x.
PREMISES STRUCK (6): hx · hTold · tA · tB · fSp9 · fSp10.
LETTERS THAT FALL, BOUND BY THE LINES IN FRONT OF THE CALL (0): none.
LETTERS AND PREMISES THAT COME IN (0): none.
What is not claimed. EVERY BINDER THAT STANDS IS A PREMISE OR A LETTER STILL. That the premises can
be met together: NO MEMBER IS SHOWN. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.LedgerFieldSeat
import Johnson.Desc.K14.Law.LedgerScopeTerms

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


/-- **The ledger's top at the seat, with what the scope gives laid in.** -/
theorem ledger_field_scope
    {Tok : Type}
    (Dw : WholeD)
    (ms₁ : List Mem)
    (N₁ : Numbers)
    (links : List ModelPart)
    (slots : ℕ)
    (hn : slots ≤ 64)
    (rdNA : ℕ → ℕ)
    (rdNB : ℕ → ℕ)
    (Zp : ProofFile.Pub)
    (cF : VerifiableInference.Desc.Chain VerifiableInference.Desc.First.S ProofFile.Cl)
    (oL : ProofFile.SecondHashFunctionArgument)
    (Zs : VerifierAndGoals.PublicFiles)
    (rP : LPFD.Full.RunPF)
    (hZs : VerifierAndGoals.InScope Zs = true)
    (hlaid : LPFD.Full.proofDataAndDecisionOfPublicFiles oL Zs.pol Zs.lay Zs.KL = .ok (Dw, rP))
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
          links
          (VerifiableInference.Desc.First.flatPlaces
            true links
            true))[(VerifiableInference.Desc.First.flatPlaces true links true).length]?.getD
        [])
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
        × (frameAt Dw (allOf Dw) Dw.key₂ 0).E.Str → Iop.Tr (uLT (ckP .two) ds) →
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
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT) →
        (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
    (dW : (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
    (wEnd : (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok MsgT))
    (hpub : ProofFile.pureRoad.pub oL Zs.pol Zs.lay Zs.KL = .ok Zp)
    (hNp : H2U.placesOfMade Zp.made = .ok Np)
    (hpinS : VerifiableInference.PlanWritten.sizedPinnedAt Zp.p.X.P Zp.p.chains.made = true)
    (hpinF : VerifiableInference.PlanWritten.firstPinnedAt Zp.p.X.P Zp.first = true)
    (hO : Desc.K14.Law.Sh.TestsO
        (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
          ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)
        (oS ProofFile.InstPub Tok VerifiableInference.Desc.First.S Dw (fun a => (a.1, a.2)) ms₁ N₁
          links Zp k14_real.choose map14_hx
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
              ⟨N₁, links, Mg₁, smp₁, ms₁⟩).R)
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
        (oS ProofFile.InstPub Tok VerifiableInference.Desc.First.S Dw (fun a => (a.1, a.2)) ms₁ N₁
          links Zp k14_real.choose map14_hx
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
              ⟨N₁, links, Mg₁, smp₁, ms₁⟩).R)
          oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub hpinS hpinF))
    (hRd : Desc.K14.Law.Sh.Reads
        (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
          ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)
        (oS ProofFile.InstPub Tok VerifiableInference.Desc.First.S Dw (fun a => (a.1, a.2)) ms₁ N₁
          links Zp k14_real.choose map14_hx
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
              ⟨N₁, links, Mg₁, smp₁, ms₁⟩).R)
          oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub hpinS hpinF)
        ((Desc.K14.Law.Sh.t₁
            (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))))
    (hdesc : ProofFile.onlineDescription oL Zs.pol Zs.lay Zs.KL = .ok
        (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
          ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
          ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
          ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
          (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
          (VerifiableInference.Desc.K12.Seat.tests Np)))
    (Ld : VerifiableInference.Desc.K12.Door.Laid)
    (hR : Desc.K14.Law.Sh.ReachOwed oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF Ld)
    (hFar : Desc.K14.Law.Sh.TestsFar oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF Ld) :
    EachLawsBN
      (keyAt Prod.snd Dw.t₁
        (tS Tok VerifiableInference.Desc.First.S Dw oL ProofFile.pureRoad.links Zp
          ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
          pp E e₁ e₂ e₃ dW wEnd).p₂
        (tS Tok VerifiableInference.Desc.First.S Dw oL ProofFile.pureRoad.links Zp
          ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
          pp E e₁ e₂ e₃ dW wEnd).l₂)
      (onQ₂
        (tiedNumbers N₁
          (Desc.K14.Law.Fence.numbersSh
            (Desc.K14.Law.Sh.t₁
              (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
            (Desc.K14.Law.Sh.layU
              (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
            (Desc.K14.Law.Sh.layO
              (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
            (0, 0) (0, 0)))
        ((pmK (P14.codes (qS Zp Np))
            (gS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)
            (smpSt (P14.codes (qS Zp Np))
              (oNoSh
                (Desc.K14.Law.Sh.sentU
                  (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                    cF Np)).size)
              stSh)
            (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
              ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
              (Desc.K14.Law.Sh.t₁
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.Sh.layU
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.Sh.layO
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)))
            (decK (qS Zp Np).par 0 2852142980
              (Desc.K14.Law.Sh.rank
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.heldFull (qS Zp Np).par 0 (qS Zp Np).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index (qS Zp Np).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                      map14_hx).shape))
                OnBytes.Flat.numsFull pp E))
            (shiftBook
              (NumbersS.lo
                (tiedNumbers N₁
                  (Desc.K14.Law.Fence.numbersSh
                    (Desc.K14.Law.Sh.t₁
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF Np))
                    (Desc.K14.Law.Sh.layU
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF Np))
                    (Desc.K14.Law.Sh.layO
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF Np))
                    (0, 0) (0, 0)))))
            (pmPoint (qS Zp Np).codes
              (gS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)
              (smpSt (qS Zp Np).codes
                (oNoSh
                  (Desc.K14.Law.Sh.sentU
                    (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                      (ProofFile.startS Zp) cF Np)).size)
                stSh)
              (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
                ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
                (Desc.K14.Law.Sh.t₁
                  (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
                (Desc.K14.Law.Sh.layU
                  (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
                (Desc.K14.Law.Sh.layO
                  (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)))
              (qS Zp Np).par 0 2852142980
              (Desc.K14.Law.Sh.rank
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.heldFull (qS Zp Np).par 0 (qS Zp Np).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index (qS Zp Np).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                      map14_hx).shape))
                OnBytes.Flat.numsFull pp E)
              (fun s : St => s.st)
              (fun s : St => shiftBook
                (tiedNumbers N₁
                  (Desc.K14.Law.Fence.numbersSh
                    (Desc.K14.Law.Sh.t₁
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                        (ProofFile.startS Zp) cF Np))
                    (Desc.K14.Law.Sh.layU
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                        (ProofFile.startS Zp) cF Np))
                    (Desc.K14.Law.Sh.layO
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                        (ProofFile.startS Zp) cF Np))
                    (0, 0) (0, 0))).lo
                s.book)
              (pmZ (qS Zp Np).par Desc.K14.Law.Sh.idleP))
            (FoldeqShape.columns (LinShape.fold (P14.S (qS Zp Np)))) 0
            (Array.size
              (Desc.K14.Law.Sh.sentU
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)))
            (qS Zp Np)
            (XK (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.Sh.layU
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.Sh.layO
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (shapeAt
                (parU (qS Zp Np)
                  (Desc.K14.Law.Sh.sentU
                    (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                      Np)))
                ⟨0,
                  (places (qS Zp Np)
                    (Desc.K14.Law.Sh.sentU
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                        (ProofFile.startS Zp) cF Np))).1
                  (Desc.K14.Law.Sh.tests_hUw
                    (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                      Np)
                    (Desc.K14.Law.Sh.tests_at map14_hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid map14_hx)
                      hNp
                      (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF (Zp.p.chains) (qS Zp Np)
                        (VerifiableInference.Desc.K12.Seat.tests Np))
                      (Desc.K14.Law.Sh.chainOk_descAt oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF _ _ _ ((Desc.K14.Law.Sh.laid_at hlaid hdesc).1))))⟩,
                shapeAt (parO (qS Zp Np))
                ⟨0,
                  (places (qS Zp Np)
                    (Desc.K14.Law.Sh.sentU
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                        (ProofFile.startS Zp) cF Np))).2.1⟩,
                shapeAt (parO (qS Zp Np))
                ⟨1,
                  (places (qS Zp Np)
                    (Desc.K14.Law.Sh.sentU
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                        (ProofFile.startS Zp) cF Np))).2.2
                  (Desc.K14.Law.Sh.tests_hS
                    (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                      Np)
                    (Desc.K14.Law.Sh.tests_at map14_hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid map14_hx)
                      hNp
                      (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF (Zp.p.chains) (qS Zp Np)
                        (VerifiableInference.Desc.K12.Seat.tests Np))
                      (Desc.K14.Law.Sh.chainOk_descAt oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF _ _ _ ((Desc.K14.Law.Sh.laid_at hlaid hdesc).1))))⟩,
                (smpK (qS Zp Np).codes
                  (shapeAt
                    (parU (qS Zp Np)
                      (Desc.K14.Law.Sh.sentU
                        (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                          ((H2K.JointK.sharedN Zp Np).lot)
                          ((H2K.JointK.sharedN Zp Np).start)
                          ((H2K.JointK.sharedN Zp Np).ended)
                          ((H2K.JointK.sharedN Zp Np).okInst)
                          ((H2K.JointK.sharedN Zp Np).fileOk)
                          ((H2K.JointK.sharedN Zp Np).standIns)
                          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                          (ProofFile.startS Zp) cF Np)))
                    ⟨0,
                      (places (qS Zp Np)
                        (Desc.K14.Law.Sh.sentU
                          (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links
                            Zp ((H2K.JointK.sharedN Zp Np).lot)
                            ((H2K.JointK.sharedN Zp Np).start)
                            ((H2K.JointK.sharedN Zp Np).ended)
                            ((H2K.JointK.sharedN Zp Np).okInst)
                            ((H2K.JointK.sharedN Zp Np).fileOk)
                            ((H2K.JointK.sharedN Zp Np).standIns)
                            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                            (ProofFile.startS Zp) cF Np))).1
                      (Desc.K14.Law.Sh.tests_hUw
                        (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                          ((H2K.JointK.sharedN Zp Np).lot)
                          ((H2K.JointK.sharedN Zp Np).start)
                          ((H2K.JointK.sharedN Zp Np).ended)
                          ((H2K.JointK.sharedN Zp Np).okInst)
                          ((H2K.JointK.sharedN Zp Np).fileOk)
                          ((H2K.JointK.sharedN Zp Np).standIns)
                          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                          (ProofFile.startS Zp) cF Np)
                        (Desc.K14.Law.Sh.tests_at map14_hx
                          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                            map14_hx)
                          hNp
                          (fieldF oL ProofFile.pureRoad.links Zp
                            ((H2K.JointK.sharedN Zp Np).lot)
                            ((H2K.JointK.sharedN Zp Np).start)
                            ((H2K.JointK.sharedN Zp Np).ended)
                            ((H2K.JointK.sharedN Zp Np).okInst)
                            ((H2K.JointK.sharedN Zp Np).fileOk)
                            ((H2K.JointK.sharedN Zp Np).standIns)
                            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                            (ProofFile.startS Zp) cF (Zp.p.chains) (qS Zp Np)
                            (VerifiableInference.Desc.K12.Seat.tests Np))
                          (Desc.K14.Law.Sh.chainOk_descAt oL ProofFile.pureRoad.links Zp
                            ((H2K.JointK.sharedN Zp Np).lot)
                            ((H2K.JointK.sharedN Zp Np).start)
                            ((H2K.JointK.sharedN Zp Np).ended)
                            ((H2K.JointK.sharedN Zp Np).okInst)
                            ((H2K.JointK.sharedN Zp Np).fileOk)
                            ((H2K.JointK.sharedN Zp Np).standIns)
                            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                            (ProofFile.startS Zp) cF _ _ _
                            ((Desc.K14.Law.Sh.laid_at hlaid hdesc).1))))⟩)
                  (shapeAt (parO (qS Zp Np))
                    ⟨0,
                      (places (qS Zp Np)
                        (Desc.K14.Law.Sh.sentU
                          (aS VerifiableInference.Desc.First.S oL
                            ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                            ((H2K.JointK.sharedN Zp Np).start)
                            ((H2K.JointK.sharedN Zp Np).ended)
                            ((H2K.JointK.sharedN Zp Np).okInst)
                            ((H2K.JointK.sharedN Zp Np).fileOk)
                            ((H2K.JointK.sharedN Zp Np).standIns)
                            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                            (ProofFile.startS Zp) cF Np))).2.1⟩)
                  (shapeAt (parO (qS Zp Np))
                    ⟨1,
                      (places (qS Zp Np)
                        (Desc.K14.Law.Sh.sentU
                          (aS VerifiableInference.Desc.First.S oL
                            ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                            ((H2K.JointK.sharedN Zp Np).start)
                            ((H2K.JointK.sharedN Zp Np).ended)
                            ((H2K.JointK.sharedN Zp Np).okInst)
                            ((H2K.JointK.sharedN Zp Np).fileOk)
                            ((H2K.JointK.sharedN Zp Np).standIns)
                            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                            (ProofFile.startS Zp) cF Np))).2.2
                      (Desc.K14.Law.Sh.tests_hS
                        (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                          ((H2K.JointK.sharedN Zp Np).lot)
                          ((H2K.JointK.sharedN Zp Np).start)
                          ((H2K.JointK.sharedN Zp Np).ended)
                          ((H2K.JointK.sharedN Zp Np).okInst)
                          ((H2K.JointK.sharedN Zp Np).fileOk)
                          ((H2K.JointK.sharedN Zp Np).standIns)
                          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                          (ProofFile.startS Zp) cF Np)
                        (Desc.K14.Law.Sh.tests_at map14_hx
                          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                            map14_hx)
                          hNp
                          (fieldF oL ProofFile.pureRoad.links Zp
                            ((H2K.JointK.sharedN Zp Np).lot)
                            ((H2K.JointK.sharedN Zp Np).start)
                            ((H2K.JointK.sharedN Zp Np).ended)
                            ((H2K.JointK.sharedN Zp Np).okInst)
                            ((H2K.JointK.sharedN Zp Np).fileOk)
                            ((H2K.JointK.sharedN Zp Np).standIns)
                            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                            (ProofFile.startS Zp) cF (Zp.p.chains) (qS Zp Np)
                            (VerifiableInference.Desc.K12.Seat.tests Np))
                          (Desc.K14.Law.Sh.chainOk_descAt oL ProofFile.pureRoad.links Zp
                            ((H2K.JointK.sharedN Zp Np).lot)
                            ((H2K.JointK.sharedN Zp Np).start)
                            ((H2K.JointK.sharedN Zp Np).ended)
                            ((H2K.JointK.sharedN Zp Np).okInst)
                            ((H2K.JointK.sharedN Zp Np).fileOk)
                            ((H2K.JointK.sharedN Zp Np).standIns)
                            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                            (ProofFile.startS Zp) cF _ _ _
                            ((Desc.K14.Law.Sh.laid_at hlaid hdesc).1))))⟩)
                  (Desc.K14.Law.Sh.sentU
                    (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                      (ProofFile.startS Zp) cF Np)).size))
              (Array.size
                (Desc.K14.Law.Sh.sentU
                  (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))))))
        (ocWith
          (ocEnd (fun a => (a.1, a.2)) N₁ Mg₁ links
            (VerifiableInference.Desc.First.flatPlaces true links true))
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
              ⟨N₁, links, Mg₁, smp₁, ms₁⟩).R))
        true
        (tS Tok VerifiableInference.Desc.First.S Dw oL ProofFile.pureRoad.links Zp
          ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
          pp E e₁ e₂ e₃ dW wEnd).p₂
        (tS Tok VerifiableInference.Desc.First.S Dw oL ProofFile.pureRoad.links Zp
          ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
          pp E e₁ e₂ e₃ dW wEnd).l₂)
      (stepAt
        (tiedNumbers N₁
          (Desc.K14.Law.Fence.numbersSh
            (Desc.K14.Law.Sh.t₁
              (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
            (Desc.K14.Law.Sh.layU
              (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
            (Desc.K14.Law.Sh.layO
              (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
            (0, 0) (0, 0)))
        ((mgK (P14.codes (qS Zp Np))
            (gS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)
            (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
            (smpSt (P14.codes (qS Zp Np))
              (oNoSh
                (Desc.K14.Law.Sh.sentU
                  (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                    cF Np)).size)
              stSh)
            (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
              ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
              (Desc.K14.Law.Sh.t₁
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.Sh.layU
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.Sh.layO
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)))
            (decK (qS Zp Np).par 0 2852142980
              (Desc.K14.Law.Sh.rank
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.heldFull (qS Zp Np).par 0 (qS Zp Np).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index (qS Zp Np).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                      map14_hx).shape))
                OnBytes.Flat.numsFull pp E))
            (tiedMeaning (fun a => (a.1, a.2)) Mg₁
              (mgJoint (qS Zp Np).codes
                (gS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)
                (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun a => (a.1, a.2)) smp₁ ms₁
                (Desc.K14.Law.Sh.xW
                  (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)
                  (oS ProofFile.InstPub Tok VerifiableInference.Desc.First.S Dw
                    (fun a => (a.1, a.2)) ms₁ N₁ links Zp k14_real.choose map14_hx
                    ((Desc.K14.Law.Sh.openAt₀
                        (Cells :=
                          ((VerifiableInference.OnPublicFiles.kcReq
                              OnBytes.Flat.numsFull pp E).conf.I))
                        (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF
                        (fun _ _ => 0)
                        (Desc.K14.Law.matN (frS.toDecR frZ 402653181)
                          OnBytes.Flat.numsFull)
                        (Desc.K14.Law.heldFull
                          (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par
                          0
                          (Desc.K14.p14Of Zp.p.chains
                            (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
                          (Desc.K14.Law.full_index
                            (Desc.K14.p14Of Zp.p.chains
                              (Desc.K14.beforePointOf Np)).par.S
                            (Desc.K14.Law.full_of_shape map14_hx
                              (Desc.K14.Law.written_in_scope hZs hpub hpinS
                                hpinF hlaid map14_hx).shape))
                          OnBytes.Flat.numsFull pp E)
                        ⟨N₁, links, Mg₁, smp₁, ms₁⟩).R)
                    oL Zs rP hZs hlaid Np smp₁ pp E Mg₁ hpub hpinS hpinF))
                (smpSt (qS Zp Np).codes
                  (oNoSh
                    (Desc.K14.Law.Sh.sentU
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                        (ProofFile.startS Zp) cF Np)).size)
                  stSh)
                (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
                  ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0)
                  ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
                  (Desc.K14.Law.Sh.t₁
                    (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                      Np))
                  (Desc.K14.Law.Sh.layU
                    (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                      Np))
                  (Desc.K14.Law.Sh.layO
                    (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                      Np)))
                (linLayW (qS Zp Np).codes (VerifiableInference.Desc.K13.whereOf Zp).lin)
                (fun q => VerifiableInference.Desc.Sound.stFirst ((fun a => (a.1, a.2)) q))
                (fun q =>
                  (VerifiableInference.Desc.Sound.tabFirst
                    (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)))
                  ((fun a => (a.1, a.2)) q))
                (rgOf (qS Zp Np).codes (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
                  (memK (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
                    ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0)
                    ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
                    (Desc.K14.Law.Sh.t₁
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF Np))
                    (Desc.K14.Law.Sh.layU
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF Np))
                    (Desc.K14.Law.Sh.layO
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF Np))
                    (Desc.K14.Law.Sh.sentU
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                        (ProofFile.startS Zp) cF Np)).size)
                  (rdK (qS Zp Np).codes))
                (omWK (qS Zp Np).codes (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
                  (memK (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
                    ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0)
                    ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
                    (Desc.K14.Law.Sh.t₁
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF Np))
                    (Desc.K14.Law.Sh.layU
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF Np))
                    (Desc.K14.Law.Sh.layO
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF Np))
                    (Desc.K14.Law.Sh.sentU
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                        (ProofFile.startS Zp) cF Np)).size)
                  (rdK (qS Zp Np).codes)
                  (Desc.K14.Law.Sh.sentU
                    (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                      (ProofFile.startS Zp) cF Np)).size
                  (qS Zp Np))
                (qS Zp Np).par 2852142980
                (gLaid (VerifiableInference.Desc.K13.whereOf Zp) (fun a => (a.1, a.2))) 0
                2852142980
                (Desc.K14.Law.Sh.rank
                  (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
                (Desc.K14.Law.heldFull (qS Zp Np).par 0
                  (qS Zp Np).par.S.fold.index.saltBytes
                  (Desc.K14.Law.full_index (qS Zp Np).par.S
                    (Desc.K14.Law.full_of_shape map14_hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                        map14_hx).shape))
                  OnBytes.Flat.numsFull pp E)
                (VerifiableInference.Desc.K13.whereOf Zp)
                (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
                (mgZ (qS Zp Np).codes (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
                  (memK (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
                    ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0)
                    ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
                    (Desc.K14.Law.Sh.t₁
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF Np))
                    (Desc.K14.Law.Sh.layU
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF Np))
                    (Desc.K14.Law.Sh.layO
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF Np))
                    (Desc.K14.Law.Sh.sentU
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                        (ProofFile.startS Zp) cF Np)).size)
                  (rdK (qS Zp Np).codes)
                  (numSh
                    (Desc.K14.Law.Sh.sentU
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                        (ProofFile.startS Zp) cF Np)).size)
                  Desc.K14.Law.Sh.idleM)))
            (memK (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
              ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
              (Desc.K14.Law.Sh.t₁
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.Sh.layU
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.Sh.layO
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.Sh.sentU
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                  Np)).size)
            (rdK (qS Zp Np).codes) 2852142980
            (FoldeqShape.columns (LinShape.fold (P14.S (qS Zp Np))))
            (Array.size
              (Desc.K14.Law.Sh.sentU
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)))
            (qS Zp Np)))
        ((pmK (P14.codes (qS Zp Np))
            (gS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)
            (smpSt (P14.codes (qS Zp Np))
              (oNoSh
                (Desc.K14.Law.Sh.sentU
                  (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
                    ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                    cF Np)).size)
              stSh)
            (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
              ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
              (Desc.K14.Law.Sh.t₁
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.Sh.layU
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.Sh.layO
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)))
            (decK (qS Zp Np).par 0 2852142980
              (Desc.K14.Law.Sh.rank
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.heldFull (qS Zp Np).par 0 (qS Zp Np).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index (qS Zp Np).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                      map14_hx).shape))
                OnBytes.Flat.numsFull pp E))
            (shiftBook
              (NumbersS.lo
                (tiedNumbers N₁
                  (Desc.K14.Law.Fence.numbersSh
                    (Desc.K14.Law.Sh.t₁
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF Np))
                    (Desc.K14.Law.Sh.layU
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF Np))
                    (Desc.K14.Law.Sh.layO
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF Np))
                    (0, 0) (0, 0)))))
            (pmPoint (qS Zp Np).codes
              (gS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)
              (smpSt (qS Zp Np).codes
                (oNoSh
                  (Desc.K14.Law.Sh.sentU
                    (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                      (ProofFile.startS Zp) cF Np)).size)
                stSh)
              (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
                ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
                (Desc.K14.Law.Sh.t₁
                  (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
                (Desc.K14.Law.Sh.layU
                  (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
                (Desc.K14.Law.Sh.layO
                  (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)))
              (qS Zp Np).par 0 2852142980
              (Desc.K14.Law.Sh.rank
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.heldFull (qS Zp Np).par 0 (qS Zp Np).par.S.fold.index.saltBytes
                (Desc.K14.Law.full_index (qS Zp Np).par.S
                  (Desc.K14.Law.full_of_shape map14_hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                      map14_hx).shape))
                OnBytes.Flat.numsFull pp E)
              (fun s : St => s.st)
              (fun s : St => shiftBook
                (tiedNumbers N₁
                  (Desc.K14.Law.Fence.numbersSh
                    (Desc.K14.Law.Sh.t₁
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                        (ProofFile.startS Zp) cF Np))
                    (Desc.K14.Law.Sh.layU
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                        (ProofFile.startS Zp) cF Np))
                    (Desc.K14.Law.Sh.layO
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                        (ProofFile.startS Zp) cF Np))
                    (0, 0) (0, 0))).lo
                s.book)
              (pmZ (qS Zp Np).par Desc.K14.Law.Sh.idleP))
            (FoldeqShape.columns (LinShape.fold (P14.S (qS Zp Np)))) 0
            (Array.size
              (Desc.K14.Law.Sh.sentU
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)))
            (qS Zp Np)
            (XK (qS Zp Np)
              (Desc.K14.Law.Sh.sentU
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.Sh.layU
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.Sh.layO
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (shapeAt
                (parU (qS Zp Np)
                  (Desc.K14.Law.Sh.sentU
                    (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                      Np)))
                ⟨0,
                  (places (qS Zp Np)
                    (Desc.K14.Law.Sh.sentU
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                        (ProofFile.startS Zp) cF Np))).1
                  (Desc.K14.Law.Sh.tests_hUw
                    (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                      Np)
                    (Desc.K14.Law.Sh.tests_at map14_hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid map14_hx)
                      hNp
                      (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF (Zp.p.chains) (qS Zp Np)
                        (VerifiableInference.Desc.K12.Seat.tests Np))
                      (Desc.K14.Law.Sh.chainOk_descAt oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF _ _ _ ((Desc.K14.Law.Sh.laid_at hlaid hdesc).1))))⟩,
                shapeAt (parO (qS Zp Np))
                ⟨0,
                  (places (qS Zp Np)
                    (Desc.K14.Law.Sh.sentU
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                        (ProofFile.startS Zp) cF Np))).2.1⟩,
                shapeAt (parO (qS Zp Np))
                ⟨1,
                  (places (qS Zp Np)
                    (Desc.K14.Law.Sh.sentU
                      (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                        (ProofFile.startS Zp) cF Np))).2.2
                  (Desc.K14.Law.Sh.tests_hS
                    (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                      Np)
                    (Desc.K14.Law.Sh.tests_at map14_hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid map14_hx)
                      hNp
                      (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF (Zp.p.chains) (qS Zp Np)
                        (VerifiableInference.Desc.K12.Seat.tests Np))
                      (Desc.K14.Law.Sh.chainOk_descAt oL ProofFile.pureRoad.links Zp
                        ((H2K.JointK.sharedN Zp Np).lot)
                        ((H2K.JointK.sharedN Zp Np).start)
                        ((H2K.JointK.sharedN Zp Np).ended)
                        ((H2K.JointK.sharedN Zp Np).okInst)
                        ((H2K.JointK.sharedN Zp Np).fileOk)
                        ((H2K.JointK.sharedN Zp Np).standIns)
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                        cF _ _ _ ((Desc.K14.Law.Sh.laid_at hlaid hdesc).1))))⟩,
                (smpK (qS Zp Np).codes
                  (shapeAt
                    (parU (qS Zp Np)
                      (Desc.K14.Law.Sh.sentU
                        (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                          ((H2K.JointK.sharedN Zp Np).lot)
                          ((H2K.JointK.sharedN Zp Np).start)
                          ((H2K.JointK.sharedN Zp Np).ended)
                          ((H2K.JointK.sharedN Zp Np).okInst)
                          ((H2K.JointK.sharedN Zp Np).fileOk)
                          ((H2K.JointK.sharedN Zp Np).standIns)
                          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                          (ProofFile.startS Zp) cF Np)))
                    ⟨0,
                      (places (qS Zp Np)
                        (Desc.K14.Law.Sh.sentU
                          (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links
                            Zp ((H2K.JointK.sharedN Zp Np).lot)
                            ((H2K.JointK.sharedN Zp Np).start)
                            ((H2K.JointK.sharedN Zp Np).ended)
                            ((H2K.JointK.sharedN Zp Np).okInst)
                            ((H2K.JointK.sharedN Zp Np).fileOk)
                            ((H2K.JointK.sharedN Zp Np).standIns)
                            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                            (ProofFile.startS Zp) cF Np))).1
                      (Desc.K14.Law.Sh.tests_hUw
                        (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                          ((H2K.JointK.sharedN Zp Np).lot)
                          ((H2K.JointK.sharedN Zp Np).start)
                          ((H2K.JointK.sharedN Zp Np).ended)
                          ((H2K.JointK.sharedN Zp Np).okInst)
                          ((H2K.JointK.sharedN Zp Np).fileOk)
                          ((H2K.JointK.sharedN Zp Np).standIns)
                          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                          (ProofFile.startS Zp) cF Np)
                        (Desc.K14.Law.Sh.tests_at map14_hx
                          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                            map14_hx)
                          hNp
                          (fieldF oL ProofFile.pureRoad.links Zp
                            ((H2K.JointK.sharedN Zp Np).lot)
                            ((H2K.JointK.sharedN Zp Np).start)
                            ((H2K.JointK.sharedN Zp Np).ended)
                            ((H2K.JointK.sharedN Zp Np).okInst)
                            ((H2K.JointK.sharedN Zp Np).fileOk)
                            ((H2K.JointK.sharedN Zp Np).standIns)
                            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                            (ProofFile.startS Zp) cF (Zp.p.chains) (qS Zp Np)
                            (VerifiableInference.Desc.K12.Seat.tests Np))
                          (Desc.K14.Law.Sh.chainOk_descAt oL ProofFile.pureRoad.links Zp
                            ((H2K.JointK.sharedN Zp Np).lot)
                            ((H2K.JointK.sharedN Zp Np).start)
                            ((H2K.JointK.sharedN Zp Np).ended)
                            ((H2K.JointK.sharedN Zp Np).okInst)
                            ((H2K.JointK.sharedN Zp Np).fileOk)
                            ((H2K.JointK.sharedN Zp Np).standIns)
                            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                            (ProofFile.startS Zp) cF _ _ _
                            ((Desc.K14.Law.Sh.laid_at hlaid hdesc).1))))⟩)
                  (shapeAt (parO (qS Zp Np))
                    ⟨0,
                      (places (qS Zp Np)
                        (Desc.K14.Law.Sh.sentU
                          (aS VerifiableInference.Desc.First.S oL
                            ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                            ((H2K.JointK.sharedN Zp Np).start)
                            ((H2K.JointK.sharedN Zp Np).ended)
                            ((H2K.JointK.sharedN Zp Np).okInst)
                            ((H2K.JointK.sharedN Zp Np).fileOk)
                            ((H2K.JointK.sharedN Zp Np).standIns)
                            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                            (ProofFile.startS Zp) cF Np))).2.1⟩)
                  (shapeAt (parO (qS Zp Np))
                    ⟨1,
                      (places (qS Zp Np)
                        (Desc.K14.Law.Sh.sentU
                          (aS VerifiableInference.Desc.First.S oL
                            ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                            ((H2K.JointK.sharedN Zp Np).start)
                            ((H2K.JointK.sharedN Zp Np).ended)
                            ((H2K.JointK.sharedN Zp Np).okInst)
                            ((H2K.JointK.sharedN Zp Np).fileOk)
                            ((H2K.JointK.sharedN Zp Np).standIns)
                            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                            (ProofFile.startS Zp) cF Np))).2.2
                      (Desc.K14.Law.Sh.tests_hS
                        (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                          ((H2K.JointK.sharedN Zp Np).lot)
                          ((H2K.JointK.sharedN Zp Np).start)
                          ((H2K.JointK.sharedN Zp Np).ended)
                          ((H2K.JointK.sharedN Zp Np).okInst)
                          ((H2K.JointK.sharedN Zp Np).fileOk)
                          ((H2K.JointK.sharedN Zp Np).standIns)
                          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                          (ProofFile.startS Zp) cF Np)
                        (Desc.K14.Law.Sh.tests_at map14_hx
                          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                            map14_hx)
                          hNp
                          (fieldF oL ProofFile.pureRoad.links Zp
                            ((H2K.JointK.sharedN Zp Np).lot)
                            ((H2K.JointK.sharedN Zp Np).start)
                            ((H2K.JointK.sharedN Zp Np).ended)
                            ((H2K.JointK.sharedN Zp Np).okInst)
                            ((H2K.JointK.sharedN Zp Np).fileOk)
                            ((H2K.JointK.sharedN Zp Np).standIns)
                            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                            (ProofFile.startS Zp) cF (Zp.p.chains) (qS Zp Np)
                            (VerifiableInference.Desc.K12.Seat.tests Np))
                          (Desc.K14.Law.Sh.chainOk_descAt oL ProofFile.pureRoad.links Zp
                            ((H2K.JointK.sharedN Zp Np).lot)
                            ((H2K.JointK.sharedN Zp Np).start)
                            ((H2K.JointK.sharedN Zp Np).ended)
                            ((H2K.JointK.sharedN Zp Np).okInst)
                            ((H2K.JointK.sharedN Zp Np).fileOk)
                            ((H2K.JointK.sharedN Zp Np).standIns)
                            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                            (ProofFile.startS Zp) cF _ _ _
                            ((Desc.K14.Law.Sh.laid_at hlaid hdesc).1))))⟩)
                  (Desc.K14.Law.Sh.sentU
                    (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                      (ProofFile.startS Zp) cF Np)).size))
              (Array.size
                (Desc.K14.Law.Sh.sentU
                  (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))))))
        (ocWith
          (ocEnd (fun a => (a.1, a.2)) N₁ Mg₁ links
            (VerifiableInference.Desc.First.flatPlaces true links true))
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
              ⟨N₁, links, Mg₁, smp₁, ms₁⟩).R))
        true
        (tS Tok VerifiableInference.Desc.First.S Dw oL ProofFile.pureRoad.links Zp
          ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
          pp E e₁ e₂ e₃ dW wEnd).p₂
        (tS Tok VerifiableInference.Desc.First.S Dw oL ProofFile.pureRoad.links Zp
          ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
          pp E e₁ e₂ e₃ dW wEnd).l₂
        (extOf
          (tiedNumbers N₁
            (Desc.K14.Law.Fence.numbersSh
              (Desc.K14.Law.Sh.t₁
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.Sh.layU
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (Desc.K14.Law.Sh.layO
                (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                  ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
              (0, 0) (0, 0)))
          (tS Tok VerifiableInference.Desc.First.S Dw oL ProofFile.pureRoad.links Zp
            ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
            ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
            ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np
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
            pp E e₁ e₂ e₃ dW wEnd).p₂
          (tS Tok VerifiableInference.Desc.First.S Dw oL ProofFile.pureRoad.links Zp
            ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
            ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
            ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np
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
            pp E e₁ e₂ e₃ dW wEnd).l₂
          ((exK (P14.codes (qS Zp Np))
              (gS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)
              (P5T.arrOf (P5T.planSeatsAll Zp Zp.D))
              (smpSt (P14.codes (qS Zp Np))
                (oNoSh
                  (Desc.K14.Law.Sh.sentU
                    (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                      (ProofFile.startS Zp) cF Np)).size)
                stSh)
              (msSh (qS Zp Np).S ((Desc.K14.Law.rad2At 2 (qS Zp Np)) 0)
                ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 0) ((Desc.K14.Law.rad5At 2 (qS Zp Np)) 1)
                (Desc.K14.Law.Sh.t₁
                  (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
                (Desc.K14.Law.Sh.layU
                  (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
                (Desc.K14.Law.Sh.layO
                  (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np)))
              (decK (qS Zp Np).par 0 2852142980
                (Desc.K14.Law.Sh.rank
                  (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                    ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
                    ((H2K.JointK.sharedN Zp Np).fileOk)
                    ((H2K.JointK.sharedN Zp Np).standIns)
                    (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))
                (Desc.K14.Law.heldFull (qS Zp Np).par 0
                  (qS Zp Np).par.S.fold.index.saltBytes
                  (Desc.K14.Law.full_index (qS Zp Np).par.S
                    (Desc.K14.Law.full_of_shape map14_hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid
                        map14_hx).shape))
                  OnBytes.Flat.numsFull pp E))
              (fun _ _ => 0)
              (tiedNumbers N₁
                (Desc.K14.Law.Fence.numbersSh
                  (Desc.K14.Law.Sh.t₁
                    (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                      Np))
                  (Desc.K14.Law.Sh.layU
                    (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                      Np))
                  (Desc.K14.Law.Sh.layO
                    (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                      ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                      Np))
                  (0, 0) (0, 0)))
              (frameAt Dw (allOf Dw) Dw.key₂ 0)))))
      slots 0
      ((tS Tok VerifiableInference.Desc.First.S Dw oL ProofFile.pureRoad.links Zp
          ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
          pp E e₁ e₂ e₃ dW wEnd).p₂
        ::
        (tS Tok VerifiableInference.Desc.First.S Dw oL ProofFile.pureRoad.links Zp
          ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
          pp E e₁ e₂ e₃ dW wEnd).l₂) := by
  exact ledger_field_seat
    (Dw := Dw) (ms₁ := ms₁) (N₁ := N₁) (links := links) (slots := slots) (hn := hn) (rdNA := rdNA)
    (rdNB := rdNB) (Zp := Zp) (cF := cF) (x := k14_real.choose) (hx := map14_hx) (oL := oL)
    (Zs := Zs) (rP := rP) (hZs := hZs) (hlaid := hlaid) (hTold := map14_hTold) (Np := Np)
    (smp₁ := smp₁)
    (fSp9 := map14_fSp9 oL Zs Dw rP Zp Np cF k14_real.choose hZs hlaid hpub hNp hdesc hpinS hpinF
        map14_hx _ _ _ _ _)
    (tA := map14_tA oL Zs Dw rP Zp Np cF hZs hlaid hpub hNp hdesc) (hI := hI) (hV := hV)
    (fSp10 := map14_fSp10 oL Zs Dw rP Zp Np cF k14_real.choose hZs hlaid hpub hNp hdesc hpinS
        hpinF map14_hx _ _ _ _ _)
    (tB := map14_tB oL Zs Dw rP Zp Np cF hZs hlaid hpub hNp hdesc) (pp := pp) (E := E) (Mg₁ := Mg₁)
    (h3 := h3) (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) (dW := dW) (wEnd := wEnd) (hpub := hpub)
    (hNp := hNp) (hpinS := hpinS) (hpinF := hpinF) (hO := hO) (hJ := hJ) (hRd := hRd)
    (hdesc := hdesc) (Ld := Ld) (hR := hR) (hFar := hFar)

end Desc.K14.Law

#print axioms Desc.K14.Law.ledger_field_scope
