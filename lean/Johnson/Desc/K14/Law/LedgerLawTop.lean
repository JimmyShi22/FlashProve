-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerLawTop.lean: K14_law's TOP IN THE LAW's OWN NAME: Sh.Law A O f l slots
(Johnson/Desc/K14/Law/SharedConstLedger.lean: each of the shared chain's twelve sub-protocols has
its error bound for a batch, at the shared table's constant: Sh.nums · Sh.mg · Sh.pm · Sh.own ·
Sh.ex), AT THE PIECES THAT THE MAKER CUTS OUT OF THE IOP AS WRITTEN IN LEAN (f :: l := the cut's
shared row), AT THE SEAT THAT THE VERIFIER MAKES.
  k14_law_top   **one call**: Sh.law_of_top (Johnson/Desc/K14/Law/SharedConstTop.lean) applied to
    ledger_field_scope (Johnson/Desc/K14/Law/LedgerFieldScope.lean); hXD (behind each piece's accept
    the door's test XD holds at the next border) := Sh.xd_at_field …
    (Johnson/Desc/K14/Law/SharedConstTopAt.lean).
THE STATEMENT IS MADE BY PROGRAM: ITS BINDERS ARE ledger_field_scope's, TO THE LETTER, AND NO OTHER.
On what it rests. The proof calls Cb.Bridge.foldErr_ix (Johnson/Bridge/FoldErrIx.lean), which rests
on Cb/Bridge/CodeListRSProved.lean, and so on the files under ThirdParty/: files adapted from
ArkLib and Mathlib (lean/LIMITS.md,
L15).
Work is counted in the cap (Johnson/Desc/K14/Law/LedgerAtCap.lean). At "LOC" the share 2⁻¹ ^ 128
holds only with the written round's bits of work (28 at the release's list); "LIN point" and
"LIN zeta" bear none; the two rounds of seeds bear the sendings' own.
What is not claimed. EVERY BINDER THAT STANDS IS A PREMISE OR A LETTER STILL. That they can be met
together: NO MEMBER IS SHOWN. No soundness of a verifier.

-/
import Johnson.Desc.K14.Law.LedgerFieldScope
import Johnson.Desc.K14.Law.SharedConstTop
import Johnson.Desc.K14.Law.SharedConstTopAt

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

/-- **K14_law's top in the law's own name.** -/
theorem k14_law_top
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
    Desc.K14.Law.Sh.Law
      (Desc.K14.Law.ShPlan.mk (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
        (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
          ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
          ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
          ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
          (ProofFile.startS Zp) cF Zp.p.chains
          (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
          (VerifiableInference.Desc.K12.Seat.tests Np))
        (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
          Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
        (Desc.K14.Law.rad2At 2 (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
        (Desc.K14.Law.rad5At 2 (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
        Johnson.G.dryProofFull.2.1 2)
      (Desc.K14.Law.ShOpen.mk (P₀ := ProofFile.InstPub)
        (P₁ := ProofFile.InstPub × VerifiableInference.Desc.First.S)
        (Cells := ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
        (Tok := Tok) (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
        (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2)) smp₁ ms₁ N₁
        links Mg₁ (VerifiableInference.Desc.K13.whereOf Zp)
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
        (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
        (Desc.K14.Law.heldFull (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
          (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
          (Desc.K14.Law.full_index
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
            (Desc.K14.Law.full_of_shape map14_hx
              (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid map14_hx).shape))
          OnBytes.Flat.numsFull pp E))
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
          (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)).l₂
      slots := by
  exact Desc.K14.Law.Sh.law_of_top
    (Desc.K14.Law.ShPlan.mk (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
        (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
          ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
          ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
          ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
          (ProofFile.startS Zp) cF Zp.p.chains
          (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
          (VerifiableInference.Desc.K12.Seat.tests Np))
        (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
          Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
        (Desc.K14.Law.rad2At 2 (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
        (Desc.K14.Law.rad5At 2 (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
        Johnson.G.dryProofFull.2.1 2)
    (Desc.K14.Law.ShOpen.mk (P₀ := ProofFile.InstPub)
        (P₁ := ProofFile.InstPub × VerifiableInference.Desc.First.S)
        (Cells := ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
        (Tok := Tok) (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
        (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2)) smp₁ ms₁ N₁
        links Mg₁ (VerifiableInference.Desc.K13.whereOf Zp)
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
        (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
        (Desc.K14.Law.heldFull (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
          (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
          (Desc.K14.Law.full_index
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
            (Desc.K14.Law.full_of_shape map14_hx
              (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid map14_hx).shape))
          OnBytes.Flat.numsFull pp E))
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
        (Desc.K14.Law.Sh.tests_at map14_hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid map14_hx) hNp
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
    (Desc.K14.Law.Sh.tests_hS
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
        (Desc.K14.Law.Sh.tests_at map14_hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid map14_hx) hNp
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
    _
    _
    _
    Dw.t₁
    (((Desc.K14.Law.Fence.counts_of_planOk
            (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
              (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
              (VerifiableInference.Desc.K12.Seat.tests Np))
            ("proof file") Dw ((Desc.K14.Law.Sh.laid_at hlaid hdesc).1)
            ((Desc.K14.Law.Sh.laid_at hlaid hdesc).2.1)).1)).symm
    (Desc.K14.Law.Sh.xd_at_field oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
        ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
        ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
        ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s)
        (ProofFile.startS Zp) cF Zp.p.chains (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
        (VerifiableInference.Desc.K12.Seat.tests Np) (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Np.U)
        (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ (Np.O.getD Np.U))
        (Desc.K14.Law.Sh.tests_two Np (Np.O.getD Np.U)
          (Desc.K14.Law.Sh.omega_at hZs hlaid hdesc))
        (VerifiableInference.Desc.Third.p₁₄Z Zp.p.chains.made.sized.proof.set
          Zp.p.chains.made.sized.proof.codes Zp.p.chains.made.sized.proof.batch)
        (Desc.K14.Law.rad2At 2 (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
        (Desc.K14.Law.rad5At 2 (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
        Johnson.G.dryProofFull.2.1 2
        (Desc.K14.Law.Sh.tests_at map14_hx
          (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid map14_hx) hNp
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
            ((Desc.K14.Law.Sh.laid_at hlaid hdesc).1)))
        (Desc.K14.Law.Sh.front_at hZs hlaid hpub hpinS hpinF map14_hx hNp
          (Desc.K14.Law.Sh.omega_at hZs hlaid hdesc)).2.1.1
        (Desc.K14.Law.Sh.front_at hZs hlaid hpub hpinS hpinF map14_hx hNp
          (Desc.K14.Law.Sh.omega_at hZs hlaid hdesc)).2.1.2.1
        (Desc.K14.Law.Sh.front_at hZs hlaid hpub hpinS hpinF map14_hx hNp
          (Desc.K14.Law.Sh.omega_at hZs hlaid hdesc)).2.1.2.2
        (Desc.K14.Law.Sh.front_at hZs hlaid hpub hpinS hpinF map14_hx hNp
          (Desc.K14.Law.Sh.omega_at hZs hlaid hdesc)).2.2.1
        (Desc.K14.Law.Sh.front_at hZs hlaid hpub hpinS hpinF map14_hx hNp
          (Desc.K14.Law.Sh.omega_at hZs hlaid hdesc)).2.2.2.1
        (Desc.K14.Law.Sh.front_at hZs hlaid hpub hpinS hpinF map14_hx hNp
          (Desc.K14.Law.Sh.omega_at hZs hlaid hdesc)).2.2.2.2
        (Desc.K14.Law.ShOpen.mk (P₀ := ProofFile.InstPub)
          (P₁ := ProofFile.InstPub × VerifiableInference.Desc.First.S)
          (Cells := ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I))
          (Tok := Tok) (Q := (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)))
          (P5T.arrOf (P5T.planSeatsAll Zp Zp.D)) (fun _ _ => 0) (fun a => (a.1, a.2)) smp₁ ms₁
          N₁ links Mg₁ (VerifiableInference.Desc.K13.whereOf Zp)
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
          (Desc.K14.Law.matN (frS.toDecR frZ 402653181) OnBytes.Flat.numsFull)
          (Desc.K14.Law.heldFull (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par 0
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S.fold.index.saltBytes
            (Desc.K14.Law.full_index
              (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S
              (Desc.K14.Law.full_of_shape map14_hx
                (Desc.K14.Law.written_in_scope hZs hpub hpinS hpinF hlaid map14_hx).shape))
            OnBytes.Flat.numsFull pp E))
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
          ((fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
              cF Zp.p.chains
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
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
              cF Zp.p.chains
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
          ((fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
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
            (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
              cF Zp.p.chains
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
          ((fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
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
            (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
              ((H2K.JointK.sharedN Zp Np).start)
              ((H2K.JointK.sharedN Zp Np).ended)
              ((H2K.JointK.sharedN Zp Np).okInst)
              ((H2K.JointK.sharedN Zp Np).fileOk)
              ((H2K.JointK.sharedN Zp Np).standIns)
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp)
              cF Zp.p.chains
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
          (restCap e₁) (restCap e₂) (restCap e₃) dW wEnd)
        (paidAtDesc ProofFile.Inst
          (Wit ((VerifiableInference.OnPublicFiles.kcReq OnBytes.Flat.numsFull pp E).conf.I) Tok
            MsgT)
          (fieldF oL ProofFile.pureRoad.links Zp ((H2K.JointK.sharedN Zp Np).lot)
            ((H2K.JointK.sharedN Zp Np).start) ((H2K.JointK.sharedN Zp Np).ended)
            ((H2K.JointK.sharedN Zp Np).okInst) ((H2K.JointK.sharedN Zp Np).fileOk)
            ((H2K.JointK.sharedN Zp Np).standIns) (H2K.JointK.secondN guardedProximityTestParts Zp Np)
            (fun s => s) (ProofFile.startS Zp) cF Zp.p.chains
            (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np))
            (VerifiableInference.Desc.K12.Seat.tests Np))
          ("proof file") Dw ((Desc.K14.Law.Sh.laid_at hlaid hdesc).2.1)
          (Desc.K14.Law.Sh.seal_of_planOk _ (Desc.K14.Law.Sh.laid_at hlaid hdesc).1)
          (ckP .two)
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
          (VerifiableInference.Desc.Chain.flat_eq _)
          (VerifiableInference.Desc.Chain.flat_eq _)
          (VerifiableInference.Desc.Chain.flat_eq _) (restCap e₁) (restCap e₂) (restCap e₃) dW
          wEnd).1)
    (ledger_field_scope
      (Dw := Dw) (ms₁ := ms₁) (N₁ := N₁) (links := links) (slots := slots) (hn := hn) (rdNA := rdNA)
      (rdNB := rdNB) (Zp := Zp) (cF := cF) (oL := oL) (Zs := Zs) (rP := rP) (hZs := hZs)
      (hlaid := hlaid) (Np := Np) (smp₁ := smp₁) (hI := hI) (hV := hV) (pp := pp) (E := E)
      (Mg₁ := Mg₁) (h3 := h3) (e₁ := e₁) (e₂ := e₂) (e₃ := e₃) (dW := dW) (wEnd := wEnd)
      (hpub := hpub) (hNp := hNp) (hpinS := hpinS) (hpinF := hpinF) (hO := hO) (hJ := hJ)
      (hRd := hRd) (hdesc := hdesc) (Ld := Ld) (hR := hR) (hFar := hFar))

end Desc.K14.Law

#print axioms Desc.K14.Law.k14_law_top
