-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Tie/Seam10.lean: at the full size: THE RIGHT HALF OF THE TIE (Seam.lean) AT THE GENERAL
FORM BENEATH EVERY CALL
OF A RUN SHEET.

Why. Every call of that sheet is `PV.RunPure.Full.stepsFullAllWith τ Z O c seven DK DP runK runP
dec` at values (Johnson/Goal/Tie/RunPureFull.lean: …AtWith lays DK := dkLanded Z, dec := decF;
…RunWith
lays c := cOf Z, seven := sevenOf Z, made at the format's fixed hash; …ThruWith lays both
as read through O: `PV.Head.cThru`, `sevenThru`; …With lays `verify-on-bytes`'s decisions), and the
sheet prints `s.yes` as
its verdict on the branch on which the call is made.
Main names. `seam10`: THE SEAM at the sheet's letters: `seamIn` (Seam.lean) at G := GF Z, it := the item that `spF` makes of Z's pol | KL (`PV.MFull.itF`: the sheet's call
makes the item so: SO THIS FILE's TERMS REACH THE SECOND HASH FUNCTION, as that call does),
sR := sRFull Z, pdL, dK, dP := the sheet's own readings of the list seven under the turn τ. c,
seven, DK, DP, runK, runP, dec, h₁:
letters. NO O. `Seam10Steps`, `Seam10Whole` (each statement a definition of its own): where the call
gives `some s`, c has 32
bytes and `s.yes` is the evaluation, at the hash function made of O, of `innerCompiledVerifier (seam10 …)` at
the image, under the way back,
of the proof that is laid of what a parser hands over, its three cfg overwritten with c as the sheet
does. `seam10Steps`,
`seam10Whole`: the proofs: the call's own body, then `seamSteps` | `seamWhole`.
THE PREMISES THAT ARE LEFT, all in the binders: hDK, hDP: `kindsAndWorkBelow256` of both files' data · hK: K + 2 <
2 ^ 49. That c has 32 bytes
comes out of the call. LETTERS WITHOUT A VALUE: A · E · P · N · d₀ · h₁.
Limits. Those of Seam.lean's head. It covers a ride of the steps or of the whole over the value's
text and that sheet's text: not a ride of one arm, not another text. THE TURN τ SITS INSIDE THE
INPUT: where a mode turns dK | dP | pdL the «no» is
an honest proof refused by a TURNED member. NOT EVERY «VERDICT no» OF A SHEET IS THIS TERM = false:
where a row in front says no
the sheet prints its verdict without the call. The parser and what makes the entry's input stand
outside. THE TYPED PROOF HOLDS c
(the three cfg): a parser of a description must lay it.

-/
import Johnson.Top.Fire.Code.Seam
import Johnson.Goal.Tie.RunPureFull

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

/-- **THE SEAM at the sheet's letters.** No O. -/
abbrev seam10 (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (τ : PV.RunPure.Full.Turn)
    (Z : OnBytes.K.Pub)
    (c : ByteArray) (hc : c.size = 32) (seven : List ByteArray) (DK DP : WholeD) (runK : RunKF)
        (runP : RunPF) (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E (GF Z) DK DP runK runP dec).Provers) (h₁ : HId)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true)
    (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (N : NamedSideOfFullD A E DK DP runK runP dsF xsF dec (GF Z).rec₀ (GF Z).z₀.2
        (sBG (GF Z)).logLeaves (GF Z).early (saltG (GF Z)) P)
    (d₀ : Dig 256) : InnerCompilerInput :=
  seamIn A E (GF Z) c hc DK DP runK runP dec P h₁ (PV.MFull.itF Z.pol Z.KL) (PV.RunPure.Full.sRFull Z)
      (τ.pdL (PV.RunArgsF.pdLOf seven))
    (τ.dK (PV.RunArgsF.pd3At seven 4)) (τ.dP (PV.RunArgsF.pd3At seven 1)) hDK hDP hK N d₀

/-- **The right half at the sheet's call, the steps**: the verdict that a sheet prints. -/
def Seam10Steps : Prop :=
  ∀ (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (τ : PV.RunPure.Full.Turn)
      (Z : OnBytes.K.Pub)
    (O : ByteArray → ByteArray) (c : ByteArray) (seven : List ByteArray) (DK DP : WholeD)
        (runK : RunKF)
    (runP : RunPF) (dec : RecFull × RecFull → PQ.View → Bool)
        (P : (FsAtR A E (GF Z) DK DP runK runP dec).Provers) (h₁ : HId)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true)
    (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (N : NamedSideOfFullD A E DK DP runK runP dsF xsF dec (GF Z).rec₀ (GF Z).z₀.2
        (sBG (GF Z)).logLeaves (GF Z).early (saltG (GF Z)) P)
    (d₀ : Dig 256) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) (s : FastSteps),
    PV.RunPure.Full.stepsFullAllWith τ Z O c seven DK DP runK runP dec commitment prompt output aux
        cm rcd copy fT e fB = some s →
    ∃ hc : c.size = 32,
      s.yes = (innerCompiledVerifier (seam10 A E τ Z c hc seven DK DP runK runP dec P h₁ hDK hDP hK N d₀)
          commitment prompt output
        ((seam10 A E τ Z c hc seven DK DP runK runP dec P h₁ hDK hDP hK N d₀).back
          (seamProof (GF Z) DK DP runK runP dec aux cm rcd copy
            { fT with cfg := c } { e with cfg := c } { fB with cfg := c }))).evaluate (hashOf O)

/-- **The right half at the sheet's call, the whole**: the one Bool. -/
def Seam10Whole : Prop :=
  ∀ (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (τ : PV.RunPure.Full.Turn)
      (Z : OnBytes.K.Pub)
    (O : ByteArray → ByteArray) (c : ByteArray) (seven : List ByteArray) (DK DP : WholeD)
        (runK : RunKF)
    (runP : RunPF) (dec : RecFull × RecFull → PQ.View → Bool)
        (P : (FsAtR A E (GF Z) DK DP runK runP dec).Provers) (h₁ : HId)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true)
    (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (N : NamedSideOfFullD A E DK DP runK runP dsF xsF dec (GF Z).rec₀ (GF Z).z₀.2
        (sBG (GF Z)).logLeaves (GF Z).early (saltG (GF Z)) P)
    (d₀ : Dig 256) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) (b : Bool),
    PV.RunPure.Full.wholeFullAllWith τ Z O c seven DK DP runK runP dec commitment prompt output aux
        cm rcd copy fT e fB = some b →
    ∃ hc : c.size = 32,
      b = (innerCompiledVerifier (seam10 A E τ Z c hc seven DK DP runK runP dec P h₁ hDK hDP hK N d₀) commitment
          prompt output
        ((seam10 A E τ Z c hc seven DK DP runK runP dec P h₁ hDK hDP hK N d₀).back
          (seamProof (GF Z) DK DP runK runP dec aux cm rcd copy
            { fT with cfg := c } { e with cfg := c } { fB with cfg := c }))).evaluate (hashOf O)

set_option maxHeartbeats 2000000 in
theorem seam10Steps : Seam10Steps := by
  intro A E τ Z O c seven DK DP runK runP dec P h₁ hDK hDP hK N d₀ commitment prompt output aux cm
      rcd copy fT e fB s h
  unfold PV.RunPure.Full.stepsFullAllWith at h
  split at h
  · rename_i hc
    refine ⟨hc, ?_⟩
    rw [← Option.some.inj h]
    exact seamSteps A E (GF Z) c hc DK DP runK runP dec P (_root_.Fmt.HO O) h₁ (PV.MFull.itF Z.pol Z.KL)
      (PV.RunPure.Full.sRFull Z) (τ.pdL (PV.RunArgsF.pdLOf seven))
      (τ.dK (PV.RunArgsF.pd3At seven 4)) (τ.dP (PV.RunArgsF.pd3At seven 1))
      hDK hDP hK N d₀ O commitment prompt output aux cm rcd copy _ _ _
  · cases h

set_option maxHeartbeats 2000000 in
theorem seam10Whole : Seam10Whole := by
  intro A E τ Z O c seven DK DP runK runP dec P h₁ hDK hDP hK N d₀ commitment prompt output aux cm
      rcd copy fT e fB b h
  unfold PV.RunPure.Full.wholeFullAllWith at h
  split at h
  · rename_i hc
    refine ⟨hc, ?_⟩
    rw [← Option.some.inj h]
    exact seamWhole A E (GF Z) c hc DK DP runK runP dec P (_root_.Fmt.HO O) h₁ (PV.MFull.itF Z.pol Z.KL)
      (PV.RunPure.Full.sRFull Z) (τ.pdL (PV.RunArgsF.pdLOf seven))
      (τ.dK (PV.RunArgsF.pd3At seven 4)) (τ.dP (PV.RunArgsF.pd3At seven 1))
      hDK hDP hK N d₀ O commitment prompt output aux cm rcd copy _ _ _
  · cases h

end LPFD.Full

#print axioms LPFD.Full.Seam10Steps
#print axioms LPFD.Full.Seam10Whole
#print axioms LPFD.Full.seam10Steps
#print axioms LPFD.Full.seam10Whole
