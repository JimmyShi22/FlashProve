-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/TieJoin.lean (the request's item is a letter `it`: Dec/MOneD.lean's head says why): THE JOIN, AT THE FULL SIZE: ONE THEOREM AT THE RUN's LETTERS, EVERY PREMISE THAT IS LEFT NAMED.
  `run_is_verify`: WHAT A RUN CALLS (`LPFD.Full.fastFAt`, Vals/FastFull.lean, at sp := spI it (a run calls it at ONE item: the one that its sheet makes; the theorem holds at every it), okS := okOwnF, linkF := W4M.linkFF …, AT ANY THREE DECISIONS runK runP dec) IS
    `verifyAtT (tAt …) (sTG G) (hashOf O) …` (TieAtValues.lean): the evaluation, at the hash made of O, of the verifier of `innerSystem (innerCompilerInputAtFullSize (tAt …))` at the image, under the way back, of the
    proof that is laid of what a parser hands over.
  `steps_is_verifyAtT`: the like for what the sheet prints: `(stepsFAt …).yes`.
How: `headWholeF` | `headStepsF` (Vals/HeadAtValue.lean: `fastFT_eq` | `fastStepsT_eq`, `fastSteps_is`, and the content of `famBound_eq`: the family that is bound once is `famFQ`), then
`tie_at` (TieAtValues.lean: `tieT2R` at the T, the writing side and the family that are laid there).
THE PREMISES THAT ARE LEFT, ALL IN THE BINDERS: hc : c.size = 32 · hDK | hDP : kindsAndWorkBelow256 of both files' data · hK : KF DK DP + 2 < 2 ^ 49. LETTERS WITHOUT A VALUE: A · E · P · N · d₀ · it.
LIMITS: those of TieAtValues.lean's and TieStatedR.lean's heads. `PV.EncId.encF` is marked irreducible in this file alone, so that Lean unfolds T and not the key's code when it compares the two.

-/
import Johnson.Top.Fire.Code.TieAtValues
import Johnson.Top.Fire.Code.Vals.HeadAtValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace LPFD.Full
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1
open TypedOracleCompiler.Run.PQ (SOf)
open PV.EntryFive
open OnBytes.Maker.Page (Pd3 kindsAndWorkBelow256)
open PV.OkOwn (okOwnF)


attribute [local irreducible] PV.EncId.encF

/-- The entry file's chain queries' strings with code, at these letters, AT THE TYPE AT WHICH `fastFAt` TAKES THEM (the interface spelt as Vals/FastFull.lean spells it). -/
abbrev linkAt (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32) (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (pdL : Dig 256) :
    FbIn 256 (carrierV (LvOf DK DP runK runP G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (linkProtocolOfRoundData (ckP _root_.Fmt.Fld.two) dsF frS.P.T.a xsF dec)) (List Bool)
        (aTOf DK DP runK runP G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (linkProtocolOfRoundData (ckP _root_.Fmt.Fld.two) dsF frS.P.T.a xsF dec))
        (_root_.Run.Twin.allLo (SOf (ckP _root_.Fmt.Fld.two) dsF))) .link × Fin (KF DK DP + 1 + 1) → Option (List Bool) :=
  W4M.linkFF (PV.MFull.carF DK DP runK runP G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (PV.MFull.lkD dec) PV.MFull.aLD) (Equiv.refl _) (KF DK DP) c hc pdL

section
variable (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₀ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (N : NamedSideOfFullD A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) P) (d₀ : Dig 256)

set_option maxHeartbeats 2000000 in
/-- **THE CAPSTONE: what a run calls is the evaluation of the verifier of `innerSystem (innerCompilerInputAtFullSize (tAt …))`.** -/
theorem run_is_verify (O : ByteArray → ByteArray) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) :
    fastFAt G c DK DP runK runP dsF xsF dec h₀ (PV.MFull.spI it) okOwnF sR (linkAt G c hc DK DP runK runP dec pdL)
        dK dP O commitment prompt output aux cm rcd copy fT e fB =
      verifyAtT (tAt A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK N d₀) (sTG G) (hashOf O)
        commitment prompt output aux cm rcd copy fT e fB :=
  (headWholeF G c DK DP runK runP dsF xsF dec h₀ (PV.MFull.spI it) okOwnF sR (linkAt G c hc DK DP runK runP dec pdL)
      dK dP O commitment prompt output aux cm rcd copy fT e fB).trans
    (tie_at A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK N d₀ O commitment prompt output aux cm rcd copy fT e fB)

set_option maxHeartbeats 2000000 in
/-- **The like for what the sheet prints**: the «and» of the twelve steps. -/
theorem steps_is_verifyAtT (O : ByteArray → ByteArray) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) :
    (stepsFAt G c DK DP runK runP dsF xsF dec h₀ (PV.MFull.spI it) okOwnF sR (linkAt G c hc DK DP runK runP dec pdL)
        dK dP O commitment prompt output aux cm rcd copy fT e fB).yes =
      verifyAtT (tAt A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK N d₀) (sTG G) (hashOf O)
        commitment prompt output aux cm rcd copy fT e fB :=
  (headStepsF G c DK DP runK runP dsF xsF dec h₀ (PV.MFull.spI it) okOwnF sR (linkAt G c hc DK DP runK runP dec pdL)
      dK dP O commitment prompt output aux cm rcd copy fT e fB).trans
    (tie_at A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK N d₀ O commitment prompt output aux cm rcd copy fT e fB)

end

end LPFD.Full

#print axioms LPFD.Full.run_is_verify
#print axioms LPFD.Full.steps_is_verifyAtT
