-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/Seam.lean (the request's item is a letter `it`: Dec/MOneD.lean's head says why): at the full size: THE RIGHT HALF OF THE TIE FROM WHAT RUNS TO THE GOALS' OWN verify(), AT THE
LETTERS OF THE VALUE THAT A RUN CALLS: what a run calls IS the evaluation, at the hash function made of O, of `innerCompiledVerifier r`,
where r is an input THAT DOES NOT NAME O.

Why. The goals' verifier (`VerifierAndGoals.verifyAt`, Ladder.lean) ends in `innerCompiledVerifier (D.input Z c m)`, where c and m are what two
public readings return at the hash function, and D is one value, fixed before the hash function is drawn. So the input at
which the two halves of the tie meet may hang on the hash function through c and m alone. The join (TieJoin.lean) has one letter h₀ on both sides, and a run sheet lays h₀ := `Fmt.HO O`: so the record that a run reaches names O
itself. Here that letter is shown idle in the record, and the join is said with two letters: h₀ in what runs, h₁ in the input.
Main names.
  `mFOne_idle`, `mOneAt_idle`, `tAt_idle`: THE LETTER h₀ IS IDLE in the coding `mOneAt` and so in the record `tAt` (TieAtValues.lean): at any
    two h₀, h₁ the two are equal. How: h₀ is read for the six digests of the chains' parameter bytes alone (`silentKey`,
    `silentProof`, OnBytes/Maker/Page/Silent.lean), and the page lays dK, dP over just these (`PageJ.withPd`): the data of the
    cut are equal by unfolding, and the coding is a function of them: `W4M.mAny_idle` (SeamKit.lean), at letters; called here.
  `seamIn`: THE SEAM: `innerCompilerInputAtFullSize (tAt …)`, a name. `seamProof`: the proof of the verifier's side that is laid of what a
    parser hands over (`proofE`), a name. `back_free`: the way back reads no letter of T.
  `SeamSteps`, `SeamWhole` (each statement a definition of its own); `seamSteps`, `seamWhole`: their proofs: the join, then
    `tAt_idle` under `verifyAtT`, then `verifyAtT_is`: `verifyAtT` is `(innerCompiledVerifier …).evaluate`, by unfolding, AT LETTERS (asked at the values
    Lean's kernel ran out of memory at this size and took a minute at the other).
WHAT IT DOES ABOUT «T NAMES THE HASH», AND WHAT IT LEAVES. Done: the input holds no O: ∀ h₁. Of the hash function it holds c, pdL,
dK, dP alone, AS LETTERS. THE ITEM `it` IS ONE LETTER ON BOTH SIDES (in what runs and in the input), A FUNCTION, WITH NO PREMISE: the input holds the format's
second hash function through it alone; IT IS TO BE LAID OF A FUNCTION THAT IS FIXED BEFORE THE HASH FUNCTION IS DRAWN, NEVER OF O: whoever lays it of O makes an input that
names O, and `SeamSteps` | `SeamWhole` still hold at it: NO TYPE HERE SHUTS THAT. Left to the other half: that a description D lays
`D.input Z c m = seamIn …` at the bytes of what `readConfig` and `readMore` return; the scope's test; the parser. Left to
nobody yet: G (the plan) is a letter here; the G that a sheet lays is made of the three public files by a planner that
calls the second hash function and, for the configuration's digest in its chains' parameter bytes, the format's hash
function by name: no O enters it, so the equation holds at every O; but a reader of D will find these names inside. (G.k and
G.c reach the coding where h₀ does, and nowhere else in it: by reading; not stated here.)
THE PREMISES THAT ARE LEFT, all in the binders: hc: c has 32 bytes · hDK, hDP: `kindsAndWorkBelow256` of both files' data · hK: K + 2 < 2 ^ 49.
LETTERS WITHOUT A VALUE: A · E · P · N · d₀ · h₁ · it.
Limits. Those of TieJoin.lean's, TieAtValues.lean's and TieStatedR.lean's heads, but for «T.m names O itself». IT HOLDS AT ANY
THREE DECISIONS runK runP dec: they stand in T's type and on both sides: it is as true at «always yes». THE ENTRY FILE's DECISION dec IS A THIRD LETTER
(over the frame's twin Johnson/Flat/Dec/); its rounds' data and stored openings stay `dsF`, `xsF`. An equation between terms: nothing on
time; what a native library computes is not said. Nothing on soundness: the conditional theorem's own hypotheses are not touched: over the twin frame these are
keySound · entrySound (a hypothesis there, proved by nobody away from the decision of Johnson/Flat/TwoSizesAt.lean's frame) · proofSound · commitment · the meaning · nine tests on numbers.

-/
import Johnson.Top.Fire.Code.TieJoin
import Johnson.Top.Fire.Code.SeamKit

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

section
variable (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₀ h₁ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (N : NamedSideOfFullD A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) P) (d₀ : Dig 256)

/-- The letter h₀ is idle in the coding, at the type at which its makers lay it. -/
theorem mFOne_idle (rK rP : RecFull) (depthReq : ℕ) (early : XF → XF) (salt K : ℕ) (k : OnBytes.Params.KeyChains)
    (c' : OnBytes.Params.ProofChains) (r₀ : RecFull) (hK' : K + 1 + 1 < 2 ^ 49) :
    PV.MFull.mFOneD DK DP runK runP dec rK rP depthReq early salt K h₀ k c' it r₀ c hc sR pdL dK dP hDK hDP hK' =
      PV.MFull.mFOneD DK DP runK runP dec rK rP depthReq early salt K h₁ k c' it r₀ c hc sR pdL dK dP hDK hDP hK' := by
  unfold PV.MFull.mFOneD
  exact W4M.mAny_idle _ _ _ _ _ _ _ _ _ _ _ h₀ h₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

set_option maxHeartbeats 2000000 in
/-- **The letter h₀ is idle in the coding.** -/
theorem mOneAt_idle :
    mOneAt A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK =
      mOneAt A E G c hc DK DP runK runP dec P h₁ it sR pdL dK dP hDK hDP hK :=
  mFOne_idle c hc DK DP runK runP dec h₀ h₁ it sR pdL dK dP hDK hDP G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) (KF DK DP)
    G.k G.c PV.Front.r0Full hK

/-- **So it is idle in the record T.** -/
theorem tAt_idle :
    tAt A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK N d₀ =
      tAt A E G c hc DK DP runK runP dec P h₁ it sR pdL dK dP hDK hDP hK N d₀ := by
  unfold tAt
  rw [mOneAt_idle A E G c hc DK DP runK runP dec P h₀ h₁ it sR pdL dK dP hDK hDP hK]

end

/-- **THE SEAM**: the input at the letters of the value that a run calls. No O. -/
abbrev seamIn (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₁ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (N : NamedSideOfFullD A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) P) (d₀ : Dig 256) : InnerCompilerInput :=
  innerCompilerInputAtFullSize (tAt A E G c hc DK DP runK runP dec P h₁ it sR pdL dK dP hDK hDP hK N d₀)

/-- The proof of the verifier's side that is laid of what a parser hands over. It reads no A, E, P, N, c, h₁, and no digest. -/
abbrev seamProof (G : FilesParameters XF RecFull) (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
    (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (aux : List Token) (cm : Dig 256) (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) :=
  proofE DK DP runK runP G.rec₀ G.z₀.2 (sTG G) (sBG G) G.early dsF xsF dec aux cm rcd copy fT e fB

/-- **The way back reads no letter of T**: its value hangs on the object and the marks alone, which stand in T's type. -/
theorem back_free {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
    {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool} {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool}
    {rK rP : RecFull} {depthReq : ℕ} {early : X → X} {salt K : ℕ}
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP depthReq early salt).Provers}
    (T T' : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP depthReq early salt K P) :
    (innerCompilerInputAtFullSize T).back = (innerCompilerInputAtFullSize T').back := rfl

/-- `verifyAtT` is the evaluation of `innerCompiledVerifier`: at letters, by unfolding. -/
theorem verifyAtT_is {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
    {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool} {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool}
    {rK rP : RecFull} {sB : Params.LinBindingShape} {early : X → X} {salt K : ℕ}
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP sB.logLeaves early salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP sB.logLeaves early salt K P) (sT : Params.LinBindingShape)
    (hash : Hash) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) :
    verifyAtT T sT hash commitment prompt output aux cm rcd copy fT e fB =
      (innerCompiledVerifier (innerCompilerInputAtFullSize T) commitment prompt output
        ((innerCompilerInputAtFullSize T).back
          (proofE DK DP runK runP rK rP sT sB early ds xs dec aux cm rcd copy fT e fB))).evaluate hash := rfl

/-- **The right half at the value's letters, the steps**: the «and» of the twelve steps. -/
def SeamSteps : Prop :=
  ∀ (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₀ h₁ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (N : NamedSideOfFullD A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) P) (d₀ : Dig 256)
    (O : ByteArray → ByteArray) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn),
    (stepsFAt G c DK DP runK runP dsF xsF dec h₀ (PV.MFull.spI it) okOwnF sR (linkAt G c hc DK DP runK runP dec pdL)
        dK dP O commitment prompt output aux cm rcd copy fT e fB).yes =
      (innerCompiledVerifier (seamIn A E G c hc DK DP runK runP dec P h₁ it sR pdL dK dP hDK hDP hK N d₀) commitment prompt output
        ((seamIn A E G c hc DK DP runK runP dec P h₁ it sR pdL dK dP hDK hDP hK N d₀).back
          (seamProof G DK DP runK runP dec aux cm rcd copy fT e fB))).evaluate (hashOf O)

/-- **The right half at the value's letters, the whole**: the one Bool. -/
def SeamWhole : Prop :=
  ∀ (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₀ h₁ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (N : NamedSideOfFullD A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) P) (d₀ : Dig 256)
    (O : ByteArray → ByteArray) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn),
    fastFAt G c DK DP runK runP dsF xsF dec h₀ (PV.MFull.spI it) okOwnF sR (linkAt G c hc DK DP runK runP dec pdL)
        dK dP O commitment prompt output aux cm rcd copy fT e fB =
      (innerCompiledVerifier (seamIn A E G c hc DK DP runK runP dec P h₁ it sR pdL dK dP hDK hDP hK N d₀) commitment prompt output
        ((seamIn A E G c hc DK DP runK runP dec P h₁ it sR pdL dK dP hDK hDP hK N d₀).back
          (seamProof G DK DP runK runP dec aux cm rcd copy fT e fB))).evaluate (hashOf O)

set_option maxHeartbeats 2000000 in
theorem seamSteps : SeamSteps :=
  fun A E G c hc DK DP runK runP dec P h₀ h₁ it sR pdL dK dP hDK hDP hK N d₀ O commitment prompt output aux cm rcd copy fT e fB =>
  (steps_is_verifyAtT A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK N d₀ O commitment prompt output aux cm rcd copy fT e fB).trans
    ((congrArg (fun T => verifyAtT T (sTG G) (hashOf O) commitment prompt output aux cm rcd copy fT e fB)
      (tAt_idle A E G c hc DK DP runK runP dec P h₀ h₁ it sR pdL dK dP hDK hDP hK N d₀)).trans
    (verifyAtT_is (tAt A E G c hc DK DP runK runP dec P h₁ it sR pdL dK dP hDK hDP hK N d₀) (sTG G) (hashOf O)
      commitment prompt output aux cm rcd copy fT e fB))

set_option maxHeartbeats 2000000 in
theorem seamWhole : SeamWhole :=
  fun A E G c hc DK DP runK runP dec P h₀ h₁ it sR pdL dK dP hDK hDP hK N d₀ O commitment prompt output aux cm rcd copy fT e fB =>
  (run_is_verify A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK N d₀ O commitment prompt output aux cm rcd copy fT e fB).trans
    ((congrArg (fun T => verifyAtT T (sTG G) (hashOf O) commitment prompt output aux cm rcd copy fT e fB)
      (tAt_idle A E G c hc DK DP runK runP dec P h₀ h₁ it sR pdL dK dP hDK hDP hK N d₀)).trans
    (verifyAtT_is (tAt A E G c hc DK DP runK runP dec P h₁ it sR pdL dK dP hDK hDP hK N d₀) (sTG G) (hashOf O)
      commitment prompt output aux cm rcd copy fT e fB))

end LPFD.Full

#print axioms LPFD.Full.mFOne_idle
#print axioms LPFD.Full.mOneAt_idle
#print axioms LPFD.Full.tAt_idle
#print axioms LPFD.Full.back_free
#print axioms LPFD.Full.verifyAtT_is
#print axioms LPFD.Full.SeamSteps
#print axioms LPFD.Full.SeamWhole
#print axioms LPFD.Full.seamSteps
#print axioms LPFD.Full.seamWhole
