-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/TieFilled.lean (the request's item is a letter `it`: Dec/MOneD.lean's head says why): two riders to the test for emptiness of the tie at the full size (TieAtValues.lean).
  `input_at`: (T1) AT THE T THAT IS LAID, WRITTEN OUT: the verifier's side of the soundness theorem's input `innerCompilerInputAtFullSize (tAt …)` IS `DvE` at the very letters of the value that a run lays
    (`LPFD.Full.dvEAt`, Vals/FastFull.lean), but for m: here the writing side of the coding that is one to one and onto (`mOneAt …`), there the writing side with code (`mFLaid`).
  `codingH`, `namedH`, `tFilled`, `t_is_there`: THE LETTERS E · P · N FILLED, at every claims A: a hollow coding (the text of the `OnBytes.K.Fire.MemberReq.hollow`), the silent provers
    (`Files.fixedMessageProvers`, OnBytes/Flat/Silent.lean), a named side with no model, an extractor that finds nothing, εId := 0, εs := 2^-128. SO THERE IS A T AT THE RUN's LETTERS: under the four conditions on data,
    at every A, every request x₀ and every digest d₀. `t_is_there_at_data`: the same at x₀ := G.z₀.1 and d₀ := pdL: so no letter is left beside the claims A and a run's data.
LIMITS. THE FILLERS ARE HOLLOW: at them nothing on soundness is to be had (keySound | entrySound | proofSound | commitment | the meaning are hypotheses on T and are not looked at here; `commitment` is FALSE at this hollow side once an
honest proof is accepted: NamedReal.lean lays a side at which it is a theorem): they show that the tie's
∀ T is not empty, and no more. Those of TieAtValues.lean's head.

-/
import Johnson.Top.Fire.Code.TieAtValues
import OnBytes.Flat.Silent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

open scoped ENNReal

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

/-- The hollow coding, for all claims. -/
def codingH {D : DecR} {X : Type} (A : D.Claims X) : Coding A where
  Rnd := Unit
  enc := fun _ _ _ => (0, [])
  Pad := Unit
  hold := fun _ _ _ => 0
  smp := fun _ _ _ => 0

/-- A hollow named side. -/
def namedH (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) (x₀ : XF) :
    NamedSideOfFullD A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) P where
  nextToken := fun _ _ => none
  ext := ⟨fun _ _ => none, fun _ _ _ _ _ => ()⟩
  εId := fun _ => 0
  x₀ := x₀
  εs := (2 : ℝ≥0∞)⁻¹ ^ 128
  hε := le_refl _

/-- **A T at the run's letters with E · P · N filled.** -/
def tFilled (A : (frS.toDecR frZ 402653181).Claims XF) (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (h₀ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (x₀ : XF) (d₀ : Dig 256) :
    InnerCompilerInputAndAnalysisFieldsAtFullSize A (codingH A) DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) (KF DK DP)
      (Files.fixedMessageProvers (FsAtR A (codingH A) G DK DP runK runP dec)) :=
  tAt A (codingH A) G c hc DK DP runK runP dec (Files.fixedMessageProvers (FsAtR A (codingH A) G DK DP runK runP dec)) h₀ it sR pdL dK dP hDK hDP hK
    (namedH A (codingH A) G DK DP runK runP dec (Files.fixedMessageProvers (FsAtR A (codingH A) G DK DP runK runP dec)) x₀) d₀

/-- **There is a T at the run's letters.** -/
theorem t_is_there (A : (frS.toDecR frZ 402653181).Claims XF) (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (h₀ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (x₀ : XF) (d₀ : Dig 256) :
    Nonempty (InnerCompilerInputAndAnalysisFieldsAtFullSize A (codingH A) DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) (KF DK DP)
      (Files.fixedMessageProvers (FsAtR A (codingH A) G DK DP runK runP dec))) :=
  ⟨tFilled A G c hc DK DP runK runP dec h₀ it sR pdL dK dP hDK hDP hK x₀ d₀⟩

/-- **The same with no letter beside the claims and a run's data**: the request is the makers' data's own (G.z₀.1), the digest is pdL. -/
theorem t_is_there_at_data (A : (frS.toDecR frZ 402653181).Claims XF) (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (h₀ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49) :
    Nonempty (InnerCompilerInputAndAnalysisFieldsAtFullSize A (codingH A) DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) (KF DK DP)
      (Files.fixedMessageProvers (FsAtR A (codingH A) G DK DP runK runP dec))) :=
  t_is_there A G c hc DK DP runK runP dec h₀ it sR pdL dK dP hDK hDP hK G.z₀.1 pdL

section
variable (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₀ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (N : NamedSideOfFullD A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) P) (d₀ : Dig 256)

set_option maxHeartbeats 1000000 in
/-- **(T1) at the T that is laid, written out.** -/
theorem input_at :
    (innerCompilerInputAtFullSize (tAt A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK N d₀)).toInputV =
      DvE DK DP runK runP G.rec₀ G.z₀.2 (sTG G) (sBG G) G.early dsF xsF dec (KF DK DP) (saltG G)
        PV.MFull.tF (PV.MFull.cfgF c) PV.MFull.shapeF
        (PV.MFull.plF DK DP runK runP G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (linkProtocolOfRoundData (ckP _root_.Fmt.Fld.two) dsF frS.P.T.a xsF dec) (_root_.Run.Twin.allLo (SOf (ckP _root_.Fmt.Fld.two) dsF)))
        (PV.MFull.plF DK DP runK runP G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (linkProtocolOfRoundData (ckP _root_.Fmt.Fld.two) dsF frS.P.T.a xsF dec) (_root_.Run.Twin.allLo (SOf (ckP _root_.Fmt.Fld.two) dsF)))
        PV.Front.numCopy (recSeedK recT recLg recS (KF DK DP + 1) (hKF DK DP)) PV.Front.r0Full (pAt (saltG G))
        (mOneAt A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK).v
        (fun k => PV.EncId.encF (_root_.Run.bytesToDig c) k.cm k.rcd) (Flat.buildReq) :=
  (tieT1 A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G) G.early (saltG G) (KF DK DP) P
    (tAt A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK N d₀) (sTG G)
    (depth_at A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK N d₀)).trans rfl

end

end LPFD.Full

#print axioms LPFD.Full.codingH
#print axioms LPFD.Full.namedH
#print axioms LPFD.Full.tFilled
#print axioms LPFD.Full.t_is_there
#print axioms LPFD.Full.t_is_there_at_data
#print axioms LPFD.Full.input_at
