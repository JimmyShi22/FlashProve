-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerFieldSeat.lean: THE LEDGER's END IN THE FIELD's OWN TEXT, AT THE SEAT
THAT THE VERIFIER MAKES: ledger_field_laid (Johnson/Desc/K14/Law/LedgerFieldLaid.lean) WITH fieldF's
OWN LETTERS LAID (the IOP as written in Lean is then descN oL pureRoad.links guardedProximityTestParts Zp Np cF)
AND THE FOUR PREMISES THAT STOOD UNDER «∀ ‹the made letters›, hlf → …» PAID (NF · TF: nine_at_row |
ten_at_row · hSh2 · hSh5: Sh.shown_two | shown_five). THE CONDITION BESIDE THE FIRST TABLE's PROMISE
IS TAKEN FROM THE CONSTANT ((Sh.openAt₀ …).R), NEVER SPELLED.
THE STATEMENT IS MADE BY PROGRAM: ledger_field_laid's own binders, in its own words, with the
letters of the maps laid in and the paid premises struck. THE PROOF: the lines in front, then ONE
CALL of ledger_field_laid by named arguments.
LETTERS LAID (23): oH · mkL · lt · st₂ · en₂ · ok₂ · fo₂ · si₂ · Bs · σ₁ · P₀ · getS · startS · get
· Rend · fileN · nO · c₁ · k₁ · c₂ · k₂ · c₃ · k₃.
PREMISES STRUCK (12): hGp · hDw · hsl · hNO · h₁f · h₂f · h₃f · hF · NF · TF · hSh2 · hSh5.
LETTERS THAT FALL, BOUND BY THE LINES IN FRONT OF THE CALL (6): t₂A · dBA · dtA · t₂B · dBB · dtB.
LETTERS AND PREMISES THAT COME IN (4): hdesc · Ld · hR · hFar.
What is not claimed. EVERY BINDER THAT STANDS IS A PREMISE OR A LETTER STILL. That the premises can
be met together: NO MEMBER IS SHOWN. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.LedgerFieldLaid
import Johnson.Loose.H2K12.LaterSeatsN
import Johnson.Top.H0.Walk.ReachThree
import Johnson.Desc.K14.Law.SharedConstScope
import Johnson.Desc.BlockLaws
import Johnson.Desc.K14.Law.SharedConstReachOwed
import Johnson.Desc.K14.Law.SharedConstFar
import Johnson.Desc.K14.Law.SharedConstFoldAt
import Johnson.Desc.K14.Law.LedgerNineTenAtRow
import Johnson.Desc.K14.Law.SharedConstShown
import Johnson.Second.Seam.SeatOfTold
import Johnson.Desc.K14.Law.LedgerToldFitOwed
import Johnson.Desc.K14.Law.LedgerSeatChain
import Johnson.Desc.Sound.SeamDesc

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


/-- **The ledger's top at the seat that the verifier makes.** -/
theorem ledger_field_seat
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
    (x : LinSized)
    (hx : VerifiableInference.Desc.K1.realSized = some (x, Johnson.G.codesFull2))
    (oL : ProofFile.SecondHashFunctionArgument)
    (Zs : VerifierAndGoals.PublicFiles)
    (rP : LPFD.Full.RunPF)
    (hZs : VerifierAndGoals.InScope Zs = true)
    (hlaid : LPFD.Full.proofDataAndDecisionOfPublicFiles oL Zs.pol Zs.lay Zs.KL = .ok (Dw, rP))
    (hTold : ToldFitOwed)
    (Np : H2U.Places4)
    (smp₁ : ProofFile.InstPub × First.S → (s : Sending) → (i : Fin s.l.length) → Option
        ((sigOf (qS Zp Np).codes s.l).om i).Smp)
    (fSp9 : ∀ a₀ rest, (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U).nums.stages = a₀ :: rest → 0 <
        (qS Zp Np).S.sharedSplit.maskRows ∧ (qS Zp Np).codes.base.size ≤
        (qS Zp Np).S.sharedSplit.code ∧
        ((Desc.K14.Law.Sh.layO
            (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
              cF Np)).shapes.getD
          ((Desc.K14.Law.Sh.layO
              (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Np)).tree.getD
            1 0)
          default).logN
        ≤ a₀.Z.a)
    (tA : FirstTie H2K.Member.setAt H2K.Member.szUFull (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U)
        H2K.Member.rUFull)
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
    (fSp10 : ∀ a₀ rest, (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ (Np.O.getD Np.U)).nums.stages = a₀ :: rest
        → 0 < (qS Zp Np).S.sharedSplit.maskRows ∧ (qS Zp Np).codes.base.size ≤
        (qS Zp Np).S.sharedSplit.code ∧
        ((Desc.K14.Law.Sh.layO
            (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
              cF Np)).shapes.getD
          ((Desc.K14.Law.Sh.layO
              (aS VerifiableInference.Desc.First.S oL ProofFile.pureRoad.links Zp
                ((H2K.JointK.sharedN Zp Np).lot)
                ((H2K.JointK.sharedN Zp Np).start)
                ((H2K.JointK.sharedN Zp Np).ended)
                ((H2K.JointK.sharedN Zp Np).okInst)
                ((H2K.JointK.sharedN Zp Np).fileOk)
                ((H2K.JointK.sharedN Zp Np).standIns)
                (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
                (ProofFile.startS Zp) cF Np)).tree.getD
            1 0)
          default).logN
        ≤ a₀.Z.a)
    (tB : FirstTie H2K.Member.setAt H2K.Member.szOFull
        (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ (Np.O.getD Np.U)) H2K.Member.rOFull)
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
          links Zp x hx
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
                  (Desc.K14.Law.full_of_shape hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
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
          links Zp x hx
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
                  (Desc.K14.Law.full_of_shape hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
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
          links Zp x hx
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
                  (Desc.K14.Law.full_of_shape hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
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
                  (Desc.K14.Law.full_of_shape hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
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
                  (Desc.K14.Law.full_of_shape hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
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
                    (Desc.K14.Law.Sh.tests_at hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
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
                    (Desc.K14.Law.Sh.tests_at hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
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
                        (Desc.K14.Law.Sh.tests_at hx
                          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx)
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
                        (Desc.K14.Law.Sh.tests_at hx
                          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx)
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
                  (Desc.K14.Law.full_of_shape hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
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
                  (Desc.K14.Law.full_of_shape hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
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
                    (fun a => (a.1, a.2)) ms₁ N₁ links Zp x hx
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
                            (Desc.K14.Law.full_of_shape hx
                              (Desc.K14.Law.written_in_scope hZs hpub hpinS
                                hpinF hlaid hx).shape))
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
                    (Desc.K14.Law.full_of_shape hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
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
                  (Desc.K14.Law.full_of_shape hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
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
                  (Desc.K14.Law.full_of_shape hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
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
                    (Desc.K14.Law.Sh.tests_at hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
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
                    (Desc.K14.Law.Sh.tests_at hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
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
                        (Desc.K14.Law.Sh.tests_at hx
                          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx)
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
                        (Desc.K14.Law.Sh.tests_at hx
                          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx)
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
                  (Desc.K14.Law.full_of_shape hx
                    (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
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
                    (Desc.K14.Law.full_of_shape hx
                      (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
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
  obtain ⟨t₂A, dBA, dtA, hNine⟩ := nine_at_row ((VerifiableInference.OnPublicFiles.kcReq
      OnBytes.Flat.numsFull pp E).conf.I) Tok oL Zs Dw rP Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np)
      cF ⟨hZs, hlaid, hdesc, hpub, hNp⟩ ((fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp
            Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
      ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN
      Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
      Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).first.first.asBare) ((fieldF oL
      ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
      ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp
      Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s
                       => s) (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).first.front.map
      VerifiableInference.Desc.Block.asBare ++ (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN
            Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
      ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN
      Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
      Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).first.links.flatMap
      VerifiableInference.Desc.Link.blocksInOrder ++ (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp
                     Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
               ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN
               Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
               Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
               (VerifiableInference.Desc.K12.Seat.tests Np)).first.back.map
      VerifiableInference.Desc.Block.asBare ++ [(fieldF oL ProofFile.pureRoad.links Zp
      ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp
      Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
      ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
      (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).first.last.asBare]) ((fieldF oL
      ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
      ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp
      Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s
                       => s) (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).shared.first.asBare) ((fieldF oL
      ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
      ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp
      Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s
                       => s) (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).shared.front.map
      VerifiableInference.Desc.Block.asBare ++ (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN
            Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
      ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN
      Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
      Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).shared.links.flatMap
      VerifiableInference.Desc.Link.blocksInOrder ++ (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp
                     Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
               ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN
               Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
               Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
               (VerifiableInference.Desc.K12.Seat.tests Np)).shared.back.map
      VerifiableInference.Desc.Block.asBare ++ [(fieldF oL ProofFile.pureRoad.links Zp
      ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp
      Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
      ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
      (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).shared.last.asBare]) ((fieldF oL
      ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
      ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp
      Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s
                       => s) (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).second.first.asBare) ((fieldF oL
      ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
      ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp
      Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s
                       => s) (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).second.front.map
      VerifiableInference.Desc.Block.asBare ++ (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN
            Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
      ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN
      Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
      Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).second.links.flatMap
      VerifiableInference.Desc.Link.blocksInOrder ++ (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp
                     Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
               ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN
               Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
               Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
               (VerifiableInference.Desc.K12.Seat.tests Np)).second.back.map
      VerifiableInference.Desc.Block.asBare ++ [(fieldF oL ProofFile.pureRoad.links Zp
      ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp
      Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
      ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
      (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).second.last.asBare]) e₁ e₂ e₃ dW wEnd
      (VerifiableInference.Desc.Chain.flat_eq _) (VerifiableInference.Desc.Chain.flat_eq _)
      (VerifiableInference.Desc.Chain.flat_eq _)
  obtain ⟨nO', hNO', t₂B, dBB, dtB, hTenR⟩ := ten_at_row ((VerifiableInference.OnPublicFiles.kcReq
      OnBytes.Flat.numsFull pp E).conf.I) Tok oL Zs Dw rP Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np)
      cF ⟨hZs, hlaid, hdesc, hpub, hNp⟩ ((fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp
            Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
      ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN
      Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
      Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).first.first.asBare) ((fieldF oL
      ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
      ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp
      Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s
                       => s) (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).first.front.map
      VerifiableInference.Desc.Block.asBare ++ (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN
            Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
      ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN
      Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
      Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).first.links.flatMap
      VerifiableInference.Desc.Link.blocksInOrder ++ (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp
                     Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
               ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN
               Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
               Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
               (VerifiableInference.Desc.K12.Seat.tests Np)).first.back.map
      VerifiableInference.Desc.Block.asBare ++ [(fieldF oL ProofFile.pureRoad.links Zp
      ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp
      Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
      ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
      (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).first.last.asBare]) ((fieldF oL
      ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
      ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp
      Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s
                       => s) (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).shared.first.asBare) ((fieldF oL
      ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
      ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp
      Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s
                       => s) (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).shared.front.map
      VerifiableInference.Desc.Block.asBare ++ (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN
            Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
      ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN
      Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
      Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).shared.links.flatMap
      VerifiableInference.Desc.Link.blocksInOrder ++ (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp
                     Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
               ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN
               Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
               Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
               (VerifiableInference.Desc.K12.Seat.tests Np)).shared.back.map
      VerifiableInference.Desc.Block.asBare ++ [(fieldF oL ProofFile.pureRoad.links Zp
      ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp
      Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
      ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
      (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).shared.last.asBare]) ((fieldF oL
      ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
      ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp
      Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s
                       => s) (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).second.first.asBare) ((fieldF oL
      ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
      ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp
      Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s
                       => s) (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).second.front.map
      VerifiableInference.Desc.Block.asBare ++ (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN
            Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
      ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN
      Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
      Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).second.links.flatMap
      VerifiableInference.Desc.Link.blocksInOrder ++ (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp
                     Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
               ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN
               Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
               Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
               (VerifiableInference.Desc.K12.Seat.tests Np)).second.back.map
      VerifiableInference.Desc.Block.asBare ++ [(fieldF oL ProofFile.pureRoad.links Zp
      ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp
      Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
      ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
      (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)).second.last.asBare]) e₁ e₂ e₃ dW wEnd
      (VerifiableInference.Desc.Chain.flat_eq _) (VerifiableInference.Desc.Chain.flat_eq _)
      (VerifiableInference.Desc.Chain.flat_eq _)
  obtain rfl := Option.some.inj (hNO'.symm.trans (Desc.K14.Law.Sh.omega_at hZs hlaid hdesc))
  have hBt : (Second.Seam.toldFitB (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).codes
      (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).S (Desc.K14.Law.Sh.layU
      (Desc.K14.Law.ShPlan.mk (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)) (fieldF oL
      ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
      ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp
      Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s
                       => s) (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)) (VerifiableInference.Desc.Third.p₁₄Z
      Zp.p.chains.made.sized.proof.set Zp.p.chains.made.sized.proof.codes
      Zp.p.chains.made.sized.proof.batch) (Desc.K14.Law.rad2At 2 (Desc.K14.p14Of Zp.p.chains
      (Desc.K14.beforePointOf Np))) (Desc.K14.Law.rad5At 2 (Desc.K14.p14Of Zp.p.chains
      (Desc.K14.beforePointOf Np))) Johnson.G.dryProofFull.2.1 2)) (Desc.K14.Law.Sh.layO
      (Desc.K14.Law.ShPlan.mk (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)) (fieldF oL
      ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
      ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp
      Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s
                       => s) (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
      (VerifiableInference.Desc.K12.Seat.tests Np)) (VerifiableInference.Desc.Third.p₁₄Z
      Zp.p.chains.made.sized.proof.set Zp.p.chains.made.sized.proof.codes
      Zp.p.chains.made.sized.proof.batch) (Desc.K14.Law.rad2At 2 (Desc.K14.p14Of Zp.p.chains
      (Desc.K14.beforePointOf Np))) (Desc.K14.Law.rad5At 2 (Desc.K14.p14Of Zp.p.chains
      (Desc.K14.beforePointOf Np))) Johnson.G.dryProofFull.2.1 2)) = true) := by
    have h := hTold x hx
    unfold Sh.layU Sh.layO Sh.sentU
    show Second.Seam.toldFitB (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).codes
        (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).S ((layTrees (Desc.K14.p14Of
        Zp.p.chains (Desc.K14.beforePointOf Np)).codes ((withU (Desc.K14.p14Of Zp.p.chains
        (Desc.K14.beforePointOf Np)).S).getD #[])).getD default) ((layTrees (Desc.K14.p14Of
        Zp.p.chains (Desc.K14.beforePointOf Np)).codes (withOmega (Desc.K14.p14Of Zp.p.chains
        (Desc.K14.beforePointOf Np)).S)).getD default) = true
    rw [(show (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).codes = Johnson.G.codesFull2
        from (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).codes), (show
        (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).S = x.shape from
        (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape)]
    exact h
  have hsF : ((fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN
            Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
      ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN
      guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains
                             (Desc.K14.beforePointOf Np)) (VerifiableInference.Desc.K12.Seat.tests Np)).sentFit = true) :=
      by
    have hpl := ((Desc.K14.Law.Sh.laid_at hlaid hdesc).1)
    simp only [FileDescription.planOk, FileDescription.planOkCore, Bool.and_eq_true] at hpl
    exact hpl.1.2
  exact ledger_field_laid
    (Dw := Dw) (get := fun a => (a.1, a.2)) (ms₁ := ms₁) (N₁ := N₁) (links := links)
    (slots := slots) (hn := hn) (t₂A := t₂A) (rdNA := rdNA) (dBA := dBA) (dtA := dtA) (t₂B := t₂B)
    (rdNB := rdNB) (dBB := dBB) (dtB := dtB) (oH := oL) (mkL := ProofFile.pureRoad.links) (Zp := Zp)
    (lt := (H2K.JointK.sharedN Zp Np).lot) (st₂ := (H2K.JointK.sharedN Zp Np).start)
    (en₂ := (H2K.JointK.sharedN Zp Np).ended) (ok₂ := (H2K.JointK.sharedN Zp Np).okInst)
    (fo₂ := (H2K.JointK.sharedN Zp Np).fileOk) (si₂ := (H2K.JointK.sharedN Zp Np).standIns)
    (Bs := H2K.JointK.secondN guardedProximityTestParts Zp Np) (getS := fun s => s) (startS := ProofFile.startS Zp)
    (cF := cF) (fileN := "proof file") (x := x) (hx := hx)
    (Rend :=
        (Desc.K14.Law.Sh.openAt₀
          (Cells := ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
          (Tok := Tok) oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF (fun _ _ => 0)
          (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
          (Desc.K14.Law.heldFull (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par
            0
            (Desc.K14.p14Of Zp.p.chains
              (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
            (Desc.K14.Law.full_index
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
              (Desc.K14.Law.full_of_shape hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
            OnBytes.Flat.numsFull pp E)
          ⟨N₁, links, Mg₁, smp₁, ms₁⟩).R)
    (oL := oL) (Zs := Zs) (rP := rP) (hZs := hZs) (hlaid := hlaid) (hTold := hTold) (Np := Np)
    (smp₁ := smp₁) (fSp9 := fSp9)
    (c₁ :=
        (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
          ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended)
          ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk)
          ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
          Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
          (VerifiableInference.Desc.K12.Seat.tests Np)).first.first.asBare)
    (k₁ :=
        (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
          ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
          ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
          ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
          Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
          (VerifiableInference.Desc.K12.Seat.tests Np)).first.front.map
        VerifiableInference.Desc.Block.asBare ++
        (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
          ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended)
          ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk)
          ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
          Zp.p.chains
          (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
          (VerifiableInference.Desc.K12.Seat.tests Np)).first.links.flatMap
        VerifiableInference.Desc.Link.blocksInOrder ++
        (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
          ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
          ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
          ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
          Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
          (VerifiableInference.Desc.K12.Seat.tests Np)).first.back.map
        VerifiableInference.Desc.Block.asBare ++
        [(fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start)
            ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst)
            ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns)
            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
            cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np)).first.last.asBare])
    (c₂ :=
        (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
          ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended)
          ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk)
          ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
          Zp.p.chains
          (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
          (VerifiableInference.Desc.K12.Seat.tests Np)).shared.first.asBare)
    (k₂ :=
        (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
          ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
          ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk)
          ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
          Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
          (VerifiableInference.Desc.K12.Seat.tests Np)).shared.front.map
        VerifiableInference.Desc.Block.asBare ++
        (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
          ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended)
          ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk)
          ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
          cF Zp.p.chains
          (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
          (VerifiableInference.Desc.K12.Seat.tests Np)).shared.links.flatMap
        VerifiableInference.Desc.Link.blocksInOrder ++
        (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
          ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
          ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
          ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
          Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
          (VerifiableInference.Desc.K12.Seat.tests Np)).shared.back.map
        VerifiableInference.Desc.Block.asBare ++
        [(fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start)
            ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst)
            ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns)
            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
            cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np)).shared.last.asBare])
    (c₃ :=
        (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
          ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended)
          ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk)
          ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
          Zp.p.chains
          (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
          (VerifiableInference.Desc.K12.Seat.tests Np)).second.first.asBare)
    (k₃ :=
        (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
          ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
          ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk)
          ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
          Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
          (VerifiableInference.Desc.K12.Seat.tests Np)).second.front.map
        VerifiableInference.Desc.Block.asBare ++
        (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
          ((H2K.JointK.sharedN Zp Np).start)
          ((H2K.JointK.sharedN Zp Np).ended)
          ((H2K.JointK.sharedN Zp Np).okInst)
          ((H2K.JointK.sharedN Zp Np).fileOk)
          ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
          cF Zp.p.chains
          (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
          (VerifiableInference.Desc.K12.Seat.tests Np)).second.links.flatMap
        VerifiableInference.Desc.Link.blocksInOrder ++
        (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
          ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
          ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
          ((H2K.JointK.sharedN Zp Np).standIns)
          (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
          Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
          (VerifiableInference.Desc.K12.Seat.tests Np)).second.back.map
        VerifiableInference.Desc.Block.asBare ++
        [(fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start)
            ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst)
            ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns)
            (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
            cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np)).second.last.asBare])
    (h₁f := VerifiableInference.Desc.Chain.flat_eq _)
    (h₂f := VerifiableInference.Desc.Chain.flat_eq _)
    (h₃f := VerifiableInference.Desc.Chain.flat_eq _)
    (hDw := (Desc.K14.Law.Sh.laid_at hlaid hdesc).2.1)
    (hsl := Desc.K14.Law.Sh.seal_of_planOk _ (Desc.K14.Law.Sh.laid_at hlaid hdesc).1) (tA := tA)
    (hI := hI) (hV := hV) (hGp := (Desc.K14.Law.Sh.laid_at hlaid hdesc).1) (nO := Np.O.getD Np.U)
    (fSp10 := fSp10) (tB := tB) (pp := pp) (E := E) (Mg₁ := Mg₁) (h3 := h3) (e₁ := e₁) (e₂ := e₂)
    (e₃ := e₃) (dW := dW) (wEnd := wEnd)
    (NF := fun base d ext err base2 d21 d22 ex2 er2 x3 base4 d4 ex4 er4 base5 d51 d52 ex5 er5 x6
        base7 d7 ex7 er7 x8 x9 x10 x11 hlf => hNine x9
        (by
          show
              ((atDesc
                  (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
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
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                      cF Zp.p.chains
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
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                        (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np))
                        (VerifiableInference.Desc.K12.Seat.tests
                          Np)).first.first.asBare)
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np))
                        (VerifiableInference.Desc.K12.Seat.tests
                          Np)).first.links.flatMap
                      VerifiableInference.Desc.Link.blocksInOrder ++
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
                          (fun s => s) (ProofFile.startS Zp) cF
                          Zp.p.chains
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np))
                        (VerifiableInference.Desc.K12.Seat.tests
                          Np)).shared.first.asBare)
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
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
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                        (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np))
                        (VerifiableInference.Desc.K12.Seat.tests
                          Np)).second.first.asBare)
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
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
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                        (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
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
                ::
                (atDesc
                  (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                    ((H2K.JointK.sharedN Zp Np).start)
                    ((H2K.JointK.sharedN Zp Np).ended)
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
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                      cF Zp.p.chains
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
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                        (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np))
                        (VerifiableInference.Desc.K12.Seat.tests
                          Np)).first.first.asBare)
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np))
                        (VerifiableInference.Desc.K12.Seat.tests
                          Np)).first.links.flatMap
                      VerifiableInference.Desc.Link.blocksInOrder ++
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
                          (fun s => s) (ProofFile.startS Zp) cF
                          Zp.p.chains
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np))
                        (VerifiableInference.Desc.K12.Seat.tests
                          Np)).shared.first.asBare)
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
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
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                        (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np))
                        (VerifiableInference.Desc.K12.Seat.tests
                          Np)).second.first.asBare)
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
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
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                        (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
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
                    (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).l₂)[9]?
              = some x9
          rw [hlf]
          rfl))
    (TF := fun base d ext err base2 d21 d22 ex2 er2 x3 base4 d4 ex4 er4 base5 d51 d52 ex5 er5 x6
        base7 d7 ex7 er7 x8 x9 x10 x11 hlf => hTenR x10
        (by
          show
              ((atDesc
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
                  (piecesAt (ckP .two)
                    (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                      cF Zp.p.chains
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
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np))
                        (VerifiableInference.Desc.K12.Seat.tests
                          Np)).first.first.asBare)
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np))
                        (VerifiableInference.Desc.K12.Seat.tests
                          Np)).first.links.flatMap
                      VerifiableInference.Desc.Link.blocksInOrder ++
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
                          (fun s => s) (ProofFile.startS Zp) cF
                          Zp.p.chains
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np))
                        (VerifiableInference.Desc.K12.Seat.tests
                          Np)).shared.first.asBare)
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
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
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                        (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np))
                        (VerifiableInference.Desc.K12.Seat.tests
                          Np)).second.first.asBare)
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
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
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                        (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
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
                ::
                (atDesc
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
                  (piecesAt (ckP .two)
                    (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                      ((H2K.JointK.sharedN Zp Np).start)
                      ((H2K.JointK.sharedN Zp Np).ended)
                      ((H2K.JointK.sharedN Zp Np).okInst)
                      ((H2K.JointK.sharedN Zp Np).fileOk)
                      ((H2K.JointK.sharedN Zp Np).standIns)
                      (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
                      cF Zp.p.chains
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
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np))
                        (VerifiableInference.Desc.K12.Seat.tests
                          Np)).first.first.asBare)
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np))
                        (VerifiableInference.Desc.K12.Seat.tests
                          Np)).first.links.flatMap
                      VerifiableInference.Desc.Link.blocksInOrder ++
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
                          (fun s => s) (ProofFile.startS Zp) cF
                          Zp.p.chains
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np))
                        (VerifiableInference.Desc.K12.Seat.tests
                          Np)).shared.first.asBare)
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
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
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                        (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
                        (Desc.K14.p14Of Zp.p.chains
                          (Desc.K14.beforePointOf Np))
                        (VerifiableInference.Desc.K12.Seat.tests
                          Np)).second.first.asBare)
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
                        (fun s => s) (ProofFile.startS Zp) cF
                        Zp.p.chains
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
                        (H2K.JointK.secondN guardedProximityTestParts Zp Np)
                        (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
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
                    (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).l₂)[10]?
              = some x10
          rw [hlf]
          rfl))
    (hSh2 := fun base d ext err base2 d21 d22 ex2 er2 x3 base4 d4 ex4 er4 base5 d51 d52 ex5 er5 x6
        base7 d7 ex7 er7 x8 x9 x10 x11 hlf => Desc.K14.Law.Sh.shown_two
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
        ("proof file") Dw Zp.p.chains (VerifiableInference.Desc.K12.Seat.tests Np)
        VerifiableInference.Desc.K12.Seat.last
        (Desc.K14.Law.Sh.tests_hUw
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
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
              (fun s => s) (ProofFile.startS Zp) cF (Zp.p.chains)
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF _ _ _
              ((Desc.K14.Law.Sh.laid_at hlaid hdesc).1))))
        (told_of_retype
          (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
            (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np))
          Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
          (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last rfl)
        hBt ((Desc.K14.Law.Sh.laid_at hlaid hdesc).2.1) hsF
        (Fence.counts_of_planOk
          (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
            (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np))
          ("proof file") Dw ((Desc.K14.Law.Sh.laid_at hlaid hdesc).1)
          ((Desc.K14.Law.Sh.laid_at hlaid hdesc).2.1)).1
        (Fence.counts_of_planOk
          (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
            (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np))
          ("proof file") Dw ((Desc.K14.Law.Sh.laid_at hlaid hdesc).1)
          ((Desc.K14.Law.Sh.laid_at hlaid hdesc).2.1)).2
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
              (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
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
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.last.asBare])
            (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd))
        _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl⟩
        (pc2
          ((Desc.K14.Law.Sh.bk
              (Desc.K14.Law.ShPlan.mk
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                  Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np))
                (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                  Zp.p.chains.made.sized.proof.codes
                  Zp.p.chains.made.sized.proof.batch)
                (Desc.K14.Law.rad2At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (Desc.K14.Law.rad5At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                Johnson.G.dryProofFull.2.1 2)
              1).retype
            (Cl' := ProofFile.Cl))
          base2 d21 d22 ex2 er2)
        (by rw [hlf]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self)))
        d21 d22 rfl _ _ _)
    (hSh5 := fun base d ext err base2 d21 d22 ex2 er2 x3 base4 d4 ex4 er4 base5 d51 d52 ex5 er5 x6
        base7 d7 ex7 er7 x8 x9 x10 x11 hlf => Desc.K14.Law.Sh.shown_five
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
        ("proof file") Dw Zp.p.chains (VerifiableInference.Desc.K12.Seat.tests Np)
        VerifiableInference.Desc.K12.Seat.last
        (Desc.K14.Law.Sh.tests_hUw
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
          (Desc.K14.Law.Sh.tests_at hx
            (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx) hNp
            (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
              (fun s => s) (ProofFile.startS Zp) cF (Zp.p.chains)
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (VerifiableInference.Desc.K12.Seat.tests Np))
            (Desc.K14.Law.Sh.chainOk_descAt oL ProofFile.pureRoad.links Zp
              ((H2K.JointK.sharedN Zp Np).lot) ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended) ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk) ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF _ _ _
              ((Desc.K14.Law.Sh.laid_at hlaid hdesc).1))))
        (told_of_retype
          (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
            (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np))
          Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
          (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last rfl)
        hBt ((Desc.K14.Law.Sh.laid_at hlaid hdesc).2.1) hsF
        (Fence.counts_of_planOk
          (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
            (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np))
          ("proof file") Dw ((Desc.K14.Law.Sh.laid_at hlaid hdesc).1)
          ((Desc.K14.Law.Sh.laid_at hlaid hdesc).2.1)).1
        (Fence.counts_of_planOk
          (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
            (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np))
          ("proof file") Dw ((Desc.K14.Law.Sh.laid_at hlaid hdesc).1)
          ((Desc.K14.Law.Sh.laid_at hlaid hdesc).2.1)).2
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
              (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
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
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
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
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np)).second.last.asBare])
            (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd))
        _ _ _ _ _ _ _ _ _ _ ⟨rfl, rfl, rfl⟩
        (pc2
          ((Desc.K14.Law.Sh.bk
              (Desc.K14.Law.ShPlan.mk
                (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
                  ((H2K.JointK.sharedN Zp Np).start)
                  ((H2K.JointK.sharedN Zp Np).ended)
                  ((H2K.JointK.sharedN Zp Np).okInst)
                  ((H2K.JointK.sharedN Zp Np).fileOk)
                  ((H2K.JointK.sharedN Zp Np).standIns)
                  (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF
                  Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
                  (VerifiableInference.Desc.K12.Seat.tests Np))
                (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
                  Zp.p.chains.made.sized.proof.codes
                  Zp.p.chains.made.sized.proof.batch)
                (Desc.K14.Law.rad2At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                (Desc.K14.Law.rad5At 2
                  (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
                Johnson.G.dryProofFull.2.1 2)
              4).retype
            (Cl' := ProofFile.Cl))
          base5 d51 d52 ex5 er5)
        (by
          rw [hlf]
          exact List.mem_cons_of_mem _
              (List.mem_cons_of_mem _
                (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self))))))
        d51 d52 rfl _ _ _)
    (hpub := hpub) (hNp := hNp) (hNO := Desc.K14.Law.Sh.omega_at hZs hlaid hdesc) (hpinS := hpinS)
    (hpinF := hpinF) (hO := hO)
    (hF := Desc.K14.Law.Sh.foldFacts_of_owed₀ oL Zp Np (H2K.JointK.secondN guardedProximityTestParts Zp Np) cF Ld
        (fun _ _ => 0) (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
        (Desc.K14.Law.heldFull (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
          (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
          (Desc.K14.Law.full_index
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
            (Desc.K14.Law.full_of_shape hx
              (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid hx).shape))
          OnBytes.Flat.numsFull pp E)
        ⟨N₁, links, Mg₁, smp₁, ms₁⟩ hR hFar)
    (hJ := hJ) (hRd := hRd)

end Desc.K14.Law

#print axioms Desc.K14.Law.ledger_field_seat
