-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/LedgerReadsAll.lean: the premise hRd of k14_field_e_all
(Johnson/Desc/K14/Law/LedgerFieldEAll.lean), TO THE LETTER, PAID: at another file's closed constant
(Mg₁ := P5J.mgAtAll h, MgAtAll.lean) the letters that the first chain's last promise reads read
the oracles below lo alone (Sh.Reads: LettersReadBelow at the last border's open set). A joining of
what lies: no new mathematics. A law file; no running text imports it. Whence. lettersReadBelow_eq
(Johnson/Desc/Sound/ReadsBelowEq.lean) asks three equations on the meaning and one test. The three
(decodes, shown, noColl) hold at mgAll by unfolding (mgAll_decodes, mgAll_shown, mgAll_noColl,
Johnson/Desc/Sound/MgAll.lean), and the constant IS mgAll at its structure of letters. The test
(what is open at the last border is sampled below lo) is a theorem at every lawful list of segments
from the two comparisons hI and hV (sampledBelow_of_open, endOpenOnly), which k14_field_e_all has as
premises anyway.
  linksOk_at: the constant's list of segments is lawful: Lean's kernel
  reads_at_all: at every head h, every lo, N₁ and lawful links: LettersReadBelow lo N₁ (P5J.mgAtAll
      h) ‹the last border's open set›, from hI and hV
  hRd_all: the premise, to the letter: its binders and its statement are cut by program out of
      LedgerFieldEAll.lean

What is not claimed. NO EXAMPLE: no head hAtMgA is shown; hI and hV stay premises. The sentence is
true by the make of the constant: "proved (general)". Nothing on soundness.

-/
import Johnson.Desc.K14.Law.LedgerFieldEAll
import Johnson.Desc.Sound.ReadsBelowEq
import Johnson.Desc.K13.Law.EndTestsAll

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
open VerifiableInference.Desc.First (linksOk flatPlaces)
open VerifiableInference.Desc.K13.Law (sampledBelow_of_open endOpenOnly)

set_option maxRecDepth 1000000 in
/-- The constant's list of segments is lawful. -/
theorem linksOk_at : linksOk P5J.At.links = true := by decide +kernel

/-- **At the closed constant the first table's letters read below lo.** -/
theorem reads_at_all {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place} (h : P5J.AtMgA o Z D r Zp Np cF x) (lo : ℕ)
    (N₁ : Numbers) (links : List ModelPart) (hlk : linksOk links = true) (hI : N₁.index.1 < lo)
    (hV : N₁.w.1 < lo) :
    LettersReadBelow lo N₁ (P5J.mgAtAll h)
      ((openSets links (flatPlaces true links true) (start links))[(flatPlaces true links
        true).length]?.getD []) :=
  lettersReadBelow_eq h.𝔇.cs h.𝔇.G h.𝔇.smp h.𝔇.ms h.𝔇.decT (P5J.mgAtAll h)
    (mgAll_decodes h.𝔇 mgBase) (mgAll_shown h.𝔇 mgBase) (mgAll_noColl h.𝔇 mgBase) lo N₁ _
    (sampledBelow_of_open lo N₁ _ (endOpenOnly links hlk) hI hV)

/-- **The premise hRd of k14_field_e_all, to the letter.** -/
theorem hRd_all
    (Dw : WholeD)
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
    (hpinS : VerifiableInference.PlanWritten.sizedPinnedAt Zp.p.X.P Zp.p.chains.made = true)
    (hpinF : VerifiableInference.PlanWritten.firstPinnedAt Zp.p.X.P Zp.first = true)
    (xLook : VerifiableInference.Desc.First.Look.Place)
    (hAtMgA : P5J.AtMgA oL Zs Dw rP Zp Np cF xLook)
    (eCodes : P5J.At.cs Zp = (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).codes) :
    Desc.K14.Law.Sh.Reads
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
              (H2K.JointK.secondN guardedProximityTestParts Zp Np) (fun s => s) (ProofFile.startS Zp) cF Np))) :=
  reads_at_all hAtMgA _ _ _ linksOk_at hI hV

end Desc.K14.Law

#print axioms Desc.K14.Law.linksOk_at
#print axioms Desc.K14.Law.reads_at_all
#print axioms Desc.K14.Law.hRd_all
