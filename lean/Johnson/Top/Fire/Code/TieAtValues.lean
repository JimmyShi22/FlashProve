-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/TieAtValues.lean (the request's item is a letter `it`: Dec/MOneD.lean's head says why): THE TEST FOR EMPTINESS OF THE TIE, AT THE FULL SIZE, AT THE LETTERS OF THE VALUE THAT RUNS: a T is laid, and all premises of
`TieT2R` (TieStatedR.lean) are met TOGETHER at it, at the writing side and the family that a run calls.
  `mOneAt`: coding that is one to one and onto by its type (`PV.MFull.mFOne`) IS TAKEN AT THE TYPE OF T.m (over `typedOracleCarrier` of the frame's object).
  `tAt`: THE T: `tAtR` at that m: GENERAL IN THE THREE DECISIONS runK runP dec;
    over `lettersAtFullD`
    (Johnson/Flat/Dec/TwoLettersAt.lean).
  `depth_at`: sT := `sTG G` has the asked depth, by unfolding.
  `reads_at`: `ReadsAs` at mR := `PV.MFull.mFLaid` and Ff := `PV.MFull.famFQ` at `prepF` and the real bk (`PV.MFull.famFQ_reads`).
  `same_at`: `SameOffSpare mFLaid (tAt …).m.v` (`PV.MFull.sameOffSpare_mFD`, TmAtValues.lean).
  `verifyAtT T sT hash …`: a name for the tie's right side, at letters: the evaluation at hash of the verifier of `innerSystem (innerCompilerInputAtFullSize T)` at the image, under the way back, of the proof that is laid
    of what a parser hands over (`proofE`). A NAME ALONE: whoever reads the join's statement unfolds it.
  `fastAtT T sT Ff hash …`: the like for its left side: `fastF` at the letters of T and a family Ff. `tie_at`: `tieT2R` at the T, the writing side and the family above.
  THE JOIN TO WHAT A RUN CALLS (`fastFAt`, `stepsFAt`): TieJoin.lean.
LETTERS AND CONDITIONS. A · E (the claims; how an index is held) · P (the provers) · N (the named side) · d₀: LETTERS: no value is laid for them here. G · c · DK · DP · h₀ · it · sR · pdL ·
dK · dP: a run's data: LETTERS. FOUR CONDITIONS ON DATA: c.size = 32 · kindsAndWorkBelow256 of both files' data · KF DK DP + 2 < 2 ^ 49. runK | runP | dec: LETTERS: every statement here holds at any three decisions: so at those that a run sheet lays (the …Plan forms) as at `verify-on-bytes`'s.
LIMITS: those of TieStatedR.lean's head. T HOLDS c (in cfg and enc) AND G: IN THE SOUNDNESS THEOREM T IS BOUND OUTSIDE THE PROBABILITY: this is a link at one member. It proves no hypothesis of the
soundness theorem. A ride at the small set is a rehearsal of the member, never a run of the goals' verify.

-/
import Johnson.Top.Fire.Code.TieProvedR
import Johnson.Top.Fire.Code.TmAtValues
import Johnson.Flat.Dec.TwoLettersAt
import Johnson.Top.Fire.Code.Vals.FastFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

noncomputable section

namespace VerifiableInference.OnPublicFiles.SlotsBehindCutD
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run OnBytes OnBytes.Join1

/-- **The tie's right side, at letters.** -/
def verifyAtT {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
    {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull}
    {sB : Params.LinBindingShape} {early : X → X} {salt K : ℕ}
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP sB.logLeaves early salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP sB.logLeaves early salt K P) (sT : Params.LinBindingShape)
    (hash : Hash) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) : Bool :=
  ((innerSystem (innerCompilerInputAtFullSize T)).verify commitment prompt output
    ((innerCompilerInputAtFullSize T).back
      (proofE DK DP runK runP rK rP sT sB early ds xs dec aux cm rcd copy fT e fB))).evaluate hash

/-- **The tie's left side, at letters**: the fast form at the letters of T and a family Ff. -/
def fastAtT {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {DK DP : WholeD}
    {runK : RecFull → PQ.View → PQ.View → PQ.View → Bool}
    {runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool} {ds : List TypedOracleCompiler.Run.PQ.RD} {xs : List _root_.Run.PQ.XO}
  {dec : RecFull × RecFull → PQ.View → Bool} {rK rP : RecFull}
    {sB : Params.LinBindingShape} {early : X → X} {salt K : ℕ}
    {P : (threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP ds xs dec rK rP sB.logLeaves early salt).Provers}
    (T : InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP ds xs dec rK rP sB.logLeaves early salt K P) (sT : Params.LinBindingShape)
    (Ff : Fam (typedOracleFamily 256 (K + 1) (carrierV (DvET T sT).L (List Bool) (DvET T sT).aT (DvET T sT).aL)))
    (hash : Hash) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) : Bool :=
  fastF DK DP runK runP rK rP sT sB early ds xs dec K salt
    T.t T.cfg T.shape T.pl0 T.pl1 T.num (recSeedK recT recLg recS (K + 1) T.hSeed) T.r₀ T.p Ff
    (fun k => T.enc ⟨k.cm, k.rcd⟩) T.build hash commitment prompt output aux cm rcd copy fT e fB

end VerifiableInference.OnPublicFiles.SlotsBehindCutD

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

/-- The three files at the letters of the value that runs, THE THREE DECISIONS LETTERS. -/
abbrev FsAtR (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool) :=
  threeProtocolsAtFullSize A (relationsAndEncodingOfClaims A E) DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G)

/-- The interface of the typed oracles over them. -/
abbrev CsAtR (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) :=
  typedOracleCarrier ((FsAtR A E G DK DP runK runP dec).withProvers P) (List Bool) (FsAtR A E G DK DP runK runP dec).annT (FsAtR A E G DK DP runK runP dec).annL

/-- **The verifier's side at the letters of the value that runs**, m a letter. (Its thirteen fields are `dvEAt`'s letters in Vals/FastFull.lean.) -/
def vAtR (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (c : ByteArray) (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers)
    (m : OracleCoding (typedOracleFamily 256 (KF DK DP + 1) (CsAtR A E G DK DP runK runP dec P)) 256) :
    VerifierSideOfFullD A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) (KF DK DP) P where
  depthReqT := (sTG G).logLeaves
  hSeed := hKF DK DP
  t := PV.MFull.tF
  cfg := PV.MFull.cfgF c
  shape := PV.MFull.shapeF
  pl0 := PV.MFull.plF DK DP runK runP G.rec₀ G.z₀.2 (sBG G).logLeaves G.early
    (linkProtocolOfRoundData (ckP _root_.Fmt.Fld.two) dsF frS.P.T.a xsF dec)
    (_root_.Run.Twin.allLo (SOf (ckP _root_.Fmt.Fld.two) dsF))
  pl1 := PV.MFull.plF DK DP runK runP G.rec₀ G.z₀.2 (sBG G).logLeaves G.early
    (linkProtocolOfRoundData (ckP _root_.Fmt.Fld.two) dsF frS.P.T.a xsF dec)
    (_root_.Run.Twin.allLo (SOf (ckP _root_.Fmt.Fld.two) dsF))
  num := PV.Front.numCopy
  r₀ := PV.Front.r0Full
  p := pAt (saltG G)
  m := m
  enc := fun k => PV.EncId.encF (_root_.Run.bytesToDig c) k.cm k.rcd
  build := Flat.buildReq

/-- **A T at a given m and c.** -/
def tAtR (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (c : ByteArray) (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers)
    (m : OracleCoding (typedOracleFamily 256 (KF DK DP + 1) (CsAtR A E G DK DP runK runP dec P)) 256)
    (N : NamedSideOfFullD A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) P) (d₀ : Dig 256) :
    InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) (KF DK DP) P :=
  lettersAtFullD (vAtR A E G c DK DP runK runP dec P m) N d₀

/-- **The coding that is one to one and onto, taken at the type of T.m.** -/
def mOneAt (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₀ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49) :
    OracleCoding (typedOracleFamily 256 (KF DK DP + 1) (CsAtR A E G DK DP runK runP dec P)) 256 :=
  PV.MFull.mFOneD DK DP runK runP dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) (KF DK DP) h₀ G.k G.c it
    PV.Front.r0Full c hc sR pdL dK dP hDK hDP hK

/-- **THE T.** -/
def tAt (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₀ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (N : NamedSideOfFullD A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) P) (d₀ : Dig 256) :
    InnerCompilerInputAndAnalysisFieldsAtFullSize A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) (KF DK DP) P :=
  tAtR A E G c DK DP runK runP dec P (mOneAt A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK) N d₀

/-- The writing side that is laid for a run, at these letters. -/
abbrev mLaidAt (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32) (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (h₀ : HId) (it : XF → ByteArray) (sR : ℕ)
    (pdL : Dig 256) (dK dP : Pd3) :=
  PV.MFull.mFLaidD DK DP runK runP dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) (KF DK DP) h₀ G.k G.c it
    PV.Front.r0Full c hc sR pdL dK dP

/-- The family that a run calls, at these letters. -/
abbrev famAt (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32) (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (h₀ : HId) (it : XF → ByteArray) (sR : ℕ)
    (pdL : Dig 256) (dK dP : Pd3) (O : ByteArray → ByteArray) :=
  PV.MFull.famFQ DK DP runK runP G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (PV.MFull.lkD dec) PV.MFull.aLD (KF DK DP)
    (PV.MFull.bkFVD DK DP runK runP dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (KF DK DP)) O
    (PV.MFull.prepF DK DP runK runP G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (PV.MFull.lkD dec) PV.MFull.aLD (saltG G) (KF DK DP) h₀ G.k G.c
      (PV.MFull.spI it) okOwnF PV.Front.r0Full c sR
      (W4M.linkFF (PV.MFull.carF DK DP runK runP G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (PV.MFull.lkD dec) PV.MFull.aLD) (Equiv.refl _) (KF DK DP) c hc pdL)
      dK dP)

section
variable (A : (frS.toDecR frZ 402653181).Claims XF) (E : Coding A) (G : FilesParameters XF RecFull) (c : ByteArray) (hc : c.size = 32)
    (DK DP : WholeD) (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool) (runP : XF × RecFull → PQ.View → PQ.View → PQ.View → Bool) (dec : RecFull × RecFull → PQ.View → Bool)
    (P : (FsAtR A E G DK DP runK runP dec).Provers) (h₀ : HId) (it : XF → ByteArray) (sR : ℕ) (pdL : Dig 256) (dK dP : Pd3)
    (hDK : kindsAndWorkBelow256 (DK.at frS.P.T.a) = true) (hDP : kindsAndWorkBelow256 (DP.at frS.P.T.a) = true) (hK : KF DK DP + 1 + 1 < 2 ^ 49)
    (N : NamedSideOfFullD A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (saltG G) P) (d₀ : Dig 256)

/-- sT's premise, at sT := the shape of the key file's binding tree off the plan. -/
theorem depth_at : (sTG G).logLeaves = (tAt A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK N d₀).depthReqT := rfl

/-- The first premise of `TieT2R`, at the writing side that is laid and the family that a run calls. -/
theorem reads_at (O : ByteArray → ByteArray) :
    ReadsAs (mLaidAt G c hc DK DP runK runP dec h₀ it sR pdL dK dP) O (famAt G c hc DK DP runK runP dec h₀ it sR pdL dK dP O) :=
  fun o q => PV.MFull.famFQ_reads DK DP runK runP G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (PV.MFull.lkD dec) PV.MFull.aLD (saltG G) (KF DK DP) h₀ G.k G.c
      (PV.MFull.spI it) okOwnF PV.Front.r0Full c sR
      (W4M.linkFF (PV.MFull.carF DK DP runK runP G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (PV.MFull.lkD dec) PV.MFull.aLD) (Equiv.refl _) (KF DK DP) c hc pdL)
      dK dP (PV.MFull.bkFVD DK DP runK runP dec G.rec₀ G.z₀.2 (sBG G).logLeaves G.early (KF DK DP)) O o q

/-- The second premise, at the T that is laid. -/
theorem same_at (g : Fam (rom 256)) :
    SameOffSpare (mLaidAt G c hc DK DP runK runP dec h₀ it sR pdL dK dP)
      (tAt A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK N d₀).m.v g :=
  PV.MFull.sameOffSpare_mFD DK DP runK runP dec G.rec₀ G.z₀.2 G.early (saltG G) (KF DK DP) h₀ G.k G.c it
    PV.Front.r0Full c hc sR pdL dK dP hDK hDP hK (sBG G).logLeaves g

/-- The tie at the T that is laid, at the writing side and the family that a run calls. -/
theorem tie_at (O : ByteArray → ByteArray) (commitment : Commitment) (prompt output aux : List Token) (cm : Dig 256)
    (rcd : RecFull) (copy : ℕ) (fT : FileIn) (e : EntryIn) (fB : FileIn) :
    fastAtT (tAt A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK N d₀) (sTG G) (famAt G c hc DK DP runK runP dec h₀ it sR pdL dK dP O) (hashOf O)
        commitment prompt output aux cm rcd copy fT e fB =
      verifyAtT (tAt A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK N d₀) (sTG G) (hashOf O)
        commitment prompt output aux cm rcd copy fT e fB :=
  tieT2R A E DK DP runK runP dsF xsF dec G.rec₀ G.z₀.2 (sBG G) G.early (saltG G) (KF DK DP) P
      (tAt A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK N d₀) (sTG G)
      (depth_at A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK N d₀) O
      (mLaidAt G c hc DK DP runK runP dec h₀ it sR pdL dK dP) (famAt G c hc DK DP runK runP dec h₀ it sR pdL dK dP O)
      (reads_at G c hc DK DP runK runP dec h₀ it sR pdL dK dP O)
      (same_at A E G c hc DK DP runK runP dec P h₀ it sR pdL dK dP hDK hDP hK N d₀ (fun _ => hashOf O))
      commitment prompt output aux cm rcd copy fT e fB

end

end LPFD.Full

#print axioms LPFD.Full.mOneAt
#print axioms LPFD.Full.tAt
#print axioms LPFD.Full.depth_at
#print axioms LPFD.Full.reads_at
#print axioms LPFD.Full.same_at
#print axioms LPFD.Full.tie_at
