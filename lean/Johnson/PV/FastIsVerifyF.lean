-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/PV/FastIsVerifyF.lean: THE ROW fast_is_verify, THE FULL SIZE: **WHAT A RUN CALLS IS THE
  EVALUATION OF verifyV AT THE INPUT THAT IT LAYS, AT THE HASH FUNCTION MADE OF THE SAME O: ONE
  NAMED THEOREM; NO PREMISE.**
GATHERED, NOTHING NEW: the value (FastFull.lean: fastFAt · stepsFAt · dvEAt · famBound_eq) · the
  kit's twins' equations (KitWholeF.lean: fastFT_eq · fastStepsT_eq: by ckPT_eq) · fastSteps_is
  (FastStepsProbe.lean) · fastF_reads_is_verifyV (FastFamProbe.lean), WHOSE ONE PREMISE ReadsAs IS
  PAID HERE by famFQ_reads (Johnson/PV/MFullQ.lean).
  reads_atRun: ReadsAs ‹the m that dvEAt lays› O ‹the family that fastFAt | stepsFAt bind once›
  **fast_is_verify : fastFAt G c DK DP runK runP ds xs dec h₀ sp okS sR linkF dK dP O ‹the user's›
    ‹the prover's› = (verifyV (dvEAt G c DK DP runK runP ds xs dec h₀ sp okS sR linkF dK dP)
    commitment prompt output (proofE …)).evaluate (hashOf O)**
  **steps_is_verify : (stepsFAt …).yes = the same**
OVER FastFull.lean, WHERE THE
  ENTRY's ds · xs · dec ARE LETTERS TOO.
GENERAL IN EVERY LETTER (G · c · DK · DP · runK · runP · ds · xs · dec · h₀ · sp · okS · sR · linkF
  · dK · dP · O).
NOT SAID: that dvEAt … is r.toInputV of an InnerCompilerInput of which a soundness theorem speaks (the m that
  is laid is a writing side; (Tm) (Johnson/Top/Fire/Code/TmStatement.lean) carries it to the
  one-to-one coding's off the spare oracle) · that proofE's typed proof is what a parser of the
  goals returns · nothing on soundness.

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

/-- The family that a run binds once answers what the m that is laid reads out of the hash function
  made of O. -/
theorem reads_atRun (h₀ : HId)
    (sp : XF → ByteArray × ByteArray) (okS : XF → Bool) (sR : ℕ)
    (linkF : FbIn 256 CVe .link × Fin (Kb + 1 + 1) → Option (List Bool)) (dK dP : Pd3)
    (O : ByteArray → ByteArray) :
    ReadsAs (Me Kb h₀ G.k G.c sp okS PV.Front.r0Full c sR linkF dK dP Bq) O
      (W4M.famPrepQ (Pe Kb h₀ G.k G.c sp okS PV.Front.r0Full c sR linkF dK dP) Bq O
        (W4M.hintK (Kb + 1) (DK.at frS.P.T.a)) (Johnson.RunOne.Lite.needAt (DP.at frS.P.T.a))) :=
  fun o q => PV.MFull.famFQ_reads DK DP runK runP G.rec₀ G.z₀.2 (sBG G).logLeaves G.early LKs ALs
      (saltG G) Kb h₀ G.k G.c sp okS
    PV.Front.r0Full c sR linkF dK dP Bq O o q

/-- **THE ROW.** -/
theorem fast_is_verify (h₀ : HId)
    (sp : XF → ByteArray × ByteArray) (okS : XF → Bool) (sR : ℕ)
    (linkF : FbIn 256 CVe .link × Fin (Kb + 1 + 1) → Option (List Bool)) (dK dP : Pd3)
    (O : ByteArray → ByteArray)
    (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) :
    fastFAt G c DK DP runK runP ds xs dec h₀ sp okS sR linkF dK dP O commitment prompt output aux cm
        rcd copy fT e fB =
      (verifyV (dvEAt G c DK DP runK runP ds xs dec h₀ sp okS sR linkF dK dP) commitment prompt
          output
        (proofE DK DP runK runP G.rec₀ G.z₀.2 (sTG G) (sBG G) G.early ds xs dec aux cm rcd copy fT e
            fB)).evaluate (hashOf O) := by
  unfold fastFAt dvEAt
  dsimp only
  rw [fastFT_eq]
  exact fastF_reads_is_verifyV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ O _
    (reads_atRun G c DK DP runK runP ds xs dec h₀ sp okS sR linkF dK dP O) commitment prompt output
        aux cm rcd copy fT e fB

/-- **The same of the twelve steps' «and».** -/
theorem steps_is_verify (h₀ : HId)
    (sp : XF → ByteArray × ByteArray) (okS : XF → Bool) (sR : ℕ)
    (linkF : FbIn 256 CVe .link × Fin (Kb + 1 + 1) → Option (List Bool)) (dK dP : Pd3)
    (O : ByteArray → ByteArray)
    (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) :
    (stepsFAt G c DK DP runK runP ds xs dec h₀ sp okS sR linkF dK dP O commitment prompt output aux
        cm rcd copy fT e fB).yes =
      (verifyV (dvEAt G c DK DP runK runP ds xs dec h₀ sp okS sR linkF dK dP) commitment prompt
          output
        (proofE DK DP runK runP G.rec₀ G.z₀.2 (sTG G) (sBG G) G.early ds xs dec aux cm rcd copy fT e
            fB)).evaluate (hashOf O) := by
  rw [← fast_is_verify G c DK DP runK runP ds xs dec h₀ sp okS sR linkF dK dP O commitment prompt
      output aux cm rcd copy fT e fB]
  unfold stepsFAt fastFAt
  dsimp only
  rw [fastStepsT_eq, fastFT_eq]
  exact (fastSteps_is _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      _).symm

end At

end LPFD.Full

#print axioms LPFD.Full.reads_atRun
#print axioms LPFD.Full.fast_is_verify
#print axioms LPFD.Full.steps_is_verify
