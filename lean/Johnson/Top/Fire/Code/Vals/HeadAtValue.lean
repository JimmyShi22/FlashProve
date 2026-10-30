-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Vals/HeadAtValue.lean: the head of the chain at the full size: from the very
terms that a run sheet calls (`fastFAt`, `stepsFAt`: Vals/FastFull.lean) to the fast form `fastF` (VerifyVFastD.lean) at the same letters and at the family `famFQ`. Two statements, each a definition of its own, and their proofs.

Why. What is proved of the fast form is proved of `fastF`. What runs is `fastFT` | `fastStepsT` (the
two great arms at the kit made for a run) at a family that the caller binds once. These two
equations say that the value that a run computes is `fastF`'s.
Main names. `HeadWholeF`: `fastFAt … = fastF …`. `HeadStepsF`: `(stepsFAt …).yes = fastF …`.
`headWholeF`, `headStepsF`: their proofs: by `fastFT_eq` | `fastStepsT_eq` (Johnson/PV/KitWholeF.lean),
`fastSteps_is` (FastStepsProbe.lean), and unfolding (`famBound_eq`'s content).
No premise: at all makers' data G, every digest c, all data DK, DP, all three decisions, the entry's rounds' data and openings, all the writing
side's letters, every O and all that a parser can hand over.
Limits. They cover the value's text, its whole and its steps: not another text, not a
ride of one arm. The sheet's own calls lie two layers above, in files that are not part of this
library. Equations between terms: nothing on time. That `fastF` at this family is the verifier's
evaluation has a premise (`ReadsAs`) that is not paid here. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.Vals.FastFull
import Johnson.Top.Fire.Code.FastStepsProbe

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD.Full
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (SOf)
open PV.EntryFive
open OnBytes.Maker.Page (Pd3)

section At
variable (G : FilesParameters XF RecFull) (c : ByteArray) (DK DP : WholeD)
  (runK : RecFull → _root_.Fmt.View → _root_.Fmt.View → _root_.Fmt.View → Bool)
  (runP : XF × RecFull → _root_.Fmt.View → _root_.Fmt.View → _root_.Fmt.View → Bool)
  (ds : List TypedOracleCompiler.Run.PQ.RD) (xs : List _root_.Run.PQ.XO)
  (dec : RecFull × RecFull → _root_.Fmt.View → Bool)

set_option quotPrecheck false in
local notation "Kb" => KF DK DP

set_option quotPrecheck false in
local notation "CKe" => ckP _root_.Fmt.Fld.two
set_option quotPrecheck false in
local notation "LKs" => linkProtocolOfRoundData CKe ds frS.P.T.a xs dec
set_option quotPrecheck false in
local notation "ALs" => _root_.Run.Twin.allLo (SOf CKe ds)
set_option quotPrecheck false in
local notation "LVe" => LvOf DK DP runK runP G.rec₀ G.z₀.2
  (sBG G).logLeaves G.early LKs
set_option quotPrecheck false in
local notation "ATe" => aTOf DK DP runK runP G.rec₀ G.z₀.2
  (sBG G).logLeaves G.early LKs
set_option quotPrecheck false in
local notation "CVe" => carrierV LVe (List Bool) ATe ALs
set_option quotPrecheck false in
local notation "PLe" => PV.MFull.plF DK DP runK runP G.rec₀ G.z₀.2
  (sBG G).logLeaves G.early LKs ALs
set_option quotPrecheck false in
local notation "Me" => PV.MFull.mF DK DP runK runP G.rec₀ G.z₀.2
  (sBG G).logLeaves G.early LKs ALs (saltG G)
set_option quotPrecheck false in
local notation "Pe" => PV.MFull.prepF DK DP runK runP G.rec₀ G.z₀.2
  (sBG G).logLeaves G.early LKs ALs (saltG G)
set_option quotPrecheck false in
local notation "Fq" => PV.MFull.famFQ DK DP runK runP G.rec₀ G.z₀.2
  (sBG G).logLeaves G.early LKs ALs
set_option quotPrecheck false in
local notation "Bq" => W4M.shoutAt (PV.MFull.bkF DK DP runK runP G.rec₀ G.z₀.2
  (sBG G).logLeaves G.early LKs ALs Kb PV.SerReq.sXF (serLAt ds))

/-- **The head, the whole**: what a run calls is the fast form at the family `famFQ`. -/
def HeadWholeF : Prop :=
  ∀ (h₀ : HId)
    (sp : XF → ByteArray × ByteArray) (okS : XF → Bool) (sR : ℕ)
    (linkF : FbIn 256 CVe .link × Fin (Kb + 1 + 1) → Option (List Bool)) (dK dP : Pd3)
    (O : ByteArray → ByteArray)
    (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn),
    fastFAt G c DK DP runK runP ds xs dec h₀ sp okS sR linkF dK dP O commitment prompt output aux cm rcd copy fT e fB =
      fastF DK DP runK runP G.rec₀ G.z₀.2 (sTG G) (sBG G)
        G.early ds xs dec Kb (saltG G) PV.MFull.tF (PV.MFull.cfgF c) PV.MFull.shapeF PLe PLe
        PV.Front.numCopy (recSeedK recT recLg recS (Kb + 1) (hKF DK DP)) PV.Front.r0Full (pAt (saltG G))
        (Fq Kb Bq O (Pe Kb h₀ G.k G.c sp okS PV.Front.r0Full c sR linkF dK dP))
        (fun k => PV.EncId.encF (_root_.Run.bytesToDig c) k.cm k.rcd) (Flat.buildReq)
        (hashOf O) commitment prompt output aux cm rcd copy fT e fB

/-- **The head, the steps**: the «and» of the twelve steps that a run prints is the same. -/
def HeadStepsF : Prop :=
  ∀ (h₀ : HId)
    (sp : XF → ByteArray × ByteArray) (okS : XF → Bool) (sR : ℕ)
    (linkF : FbIn 256 CVe .link × Fin (Kb + 1 + 1) → Option (List Bool)) (dK dP : Pd3)
    (O : ByteArray → ByteArray)
    (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn),
    (stepsFAt G c DK DP runK runP ds xs dec h₀ sp okS sR linkF dK dP O commitment prompt output aux cm rcd copy fT e fB).yes =
      fastF DK DP runK runP G.rec₀ G.z₀.2 (sTG G) (sBG G)
        G.early ds xs dec Kb (saltG G) PV.MFull.tF (PV.MFull.cfgF c) PV.MFull.shapeF PLe PLe
        PV.Front.numCopy (recSeedK recT recLg recS (Kb + 1) (hKF DK DP)) PV.Front.r0Full (pAt (saltG G))
        (Fq Kb Bq O (Pe Kb h₀ G.k G.c sp okS PV.Front.r0Full c sR linkF dK dP))
        (fun k => PV.EncId.encF (_root_.Run.bytesToDig c) k.cm k.rcd) (Flat.buildReq)
        (hashOf O) commitment prompt output aux cm rcd copy fT e fB

theorem headWholeF : HeadWholeF G c DK DP runK runP ds xs dec := by
  intro h₀ sp okS sR linkF dK dP O commitment prompt output aux cm rcd copy fT e fB
  unfold fastFAt
  exact fastFT_eq ..

theorem headStepsF : HeadStepsF G c DK DP runK runP ds xs dec := by
  intro h₀ sp okS sR linkF dK dP O commitment prompt output aux cm rcd copy fT e fB
  unfold stepsFAt
  dsimp only
  rw [fastStepsT_eq]
  exact (fastSteps_is ..).symm

end At

end LPFD.Full

#print axioms LPFD.Full.HeadWholeF
#print axioms LPFD.Full.HeadStepsF
#print axioms LPFD.Full.headWholeF
#print axioms LPFD.Full.headStepsF
