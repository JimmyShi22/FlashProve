-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ProofPageD.lean: the page of Johnson/Top/ProofPage.lean with its six digests of the two
files' chains' parameter bytes as DATA, the proof file's encoding at its cut, and, under the
premises listed below, three laws on what that encoding reads out of ANY hash function g.

THE LETTERS MEET; THIS IS NO TIE. Definitions, and statements with their proofs. In `pageRec` the
three digests of the proof file's chains' parameter bytes are made by the function h on strings.
Here they are laid anew as the parameter dP, and the key file's three as dK (`PageJ.withPd`,
OnBytes/Maker/Page/WithPd.lean): so g does not occur in the page, the cut or the encoding, and h₀ is
any fixed function. Their other letters may hold answers of a hash function (cfg; the codes of the
seeds and of the leaves): that they are fixed before a hash function is drawn is not claimed.

  `lawsJ_page`         `LawsJ` at the proof file's data of `pageRec`, under the test `fitFill`.
  `pageD`              the page with the digests dK, dP.
  `proofLaws_pageD`    `ProofLaws` at its cut by `fitFill`, at any dK, dP: it comes from laws at
                       the page itself, of which `LawsJ` reads no digest (`proofLaws_withPd`);
                       `ProofLaws` itself reads dP, and dK not at all.
  `mProofPageD`        the encoding.
  `ProofCodedG`        three laws on typed oracle functions gf and a function O on strings: how gf
                       answers the chains' queries that meet `QProof` | `QgProof`, the leaf queries
                       at which the page's spelling writes, and the vertices.
  `proofCodedG_pageD`  the three at `readBlocks (mProofPageD ..) g` and `oB (g ())`, for every g.

To be minded. The laws on the chains' queries speak by the page's data, which hold dP: they serve a
file's run only where the digests that the file's heads bear ARE dP. At a g under which the public
data's digests are others the three laws hold all the same, but the call by which gf answers a
chain's first query bears dP and is not the file's own: the laws on the three first queries
(`proof_s0`, `proof_s4`, `proof_s3`, OnBytes/K/Arm/ProofCoding.lean) take the equation as a
premise, and without it the answers at the three first queries are not tied to the file's: its
chains cannot be followed from their starts. That the digests are g's own is a condition for whoever
follows a run: three equations. The request tree's two laws are not here: `NodeCoded` and
`LeafCoded` (OnBytes/TypedOracleCompiler/Joined/K/Request.lean) are typed at the format's own hash.

Premises: the read-back is one to one where it reads (hrd); `kindsAndWorkBelow256` (hD); the number of blocks is
below 2^49 (hK); cfg has 32 bytes (hc); isP0 and isP1 say yes at p0 and at p1 alone (hp0, hp1); the
three laws that the value S brings along (the head of Johnson/Top/ProofPage.lean). `lawsJ_page` has
all of these but hc (hp0 and hp1 only because they form `pageRec`). Of `proofCodedG_pageD` besides:
`Spells V.lf.put bd` (hS): whatever the code of leaves writes at a leaf query that has a call is the
bits of that call's string; that it writes anywhere is not asked.

ON EMPTINESS. As in the head of Johnson/Top/ProofPage.lean: all is said over a value S of
`FrontSet`.

THE FORMAT: a proof's first statement has four items: table, stored copy, request, the request
file's words (`Params.First.statement`, OnBytes/Params/Chains.lean); sp : X → ByteArray × ByteArray
spells the third and the fourth.

Not claimed. Any premise at any value. That a verifier's queries pass the tests. Nothing under a
probability. Nothing on soundness.

-/
import Johnson.Top.ProofPage
import OnBytes.Maker.Page.WithPd

set_option autoImplicit false

namespace OnBytes.K.Arm.ProofFront

open _root_.Run _root_.Run.PQ Iop Rom
open OnBytes.Maker OnBytes.Maker.Page
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Compile.Batch.Cms (typedOracleCarrier)
open TypedOracleCompiler.Run.SeedPage (LinkCode)
open TypedOracleCompiler.Run.PageG (Leaves)
open _root_.Compile.Joined (JoinMsg)
open OnBytes.K.Arm (ProofCut ProofLaws digBytes mProof Spells QProof QgProof speaks_proof
  leafRowQ_proof nodeIs_proof)
open OnBytes.K.Arm.ProofGlue (proofCutOf)
open OnBytes.K.Arm.FileInj (FitJ LawsJ)

/-- **Three laws on typed oracle functions gf, at a function O on strings.** -/
structure ProofCodedG {I X : Type} {L : TypedOracleCompiler.Iop.BatchProtocolWithLeafBody I X} {K : ℕ} (C : ProofCut L (K + 1))
    (gf : Fam (typedOracleFamily 256 (K + 1) L)) (O : ByteArray → ByteArray) (bd : L.Bd → List Bool) :
    Prop where
  /-- the three chains' queries -/
  chains : SpeaksQ gf .onl C.P.proof O (QProof C) (QgProof C)
  /-- the leaves of the trees over oracles and over stored tables -/
  leaves : LeafRow gf O bd fun q => (C.P.leafX q).isSome
  /-- their vertices -/
  nodes : NodeIs gf (Fmt.HO O) C.P.cfg

variable {I X : Type} {L : HolographicProtocol I X} (Bd : Type) (aT : RoundSplits L.offline.shape) (aL : RoundSplits L.link.shape)
  {K : ℕ} (C : CK) (D : WholeD) (tF : FrontMsg (List E)) (tJ : JoinMsg (List E) ByteArray)
  (t3 : ByteArray)
  (rd : PBt (typedOracleCarrier L Bd aT aL) .onl →
    Option (PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann))
  (h₀ : HId) (c : Params.ProofChains) {sp : X →
      ByteArray × ByteArray} {r₀ : L.Rec} (S : FrontSet L sp r₀)
  (tl : Dig 256 → List E → List (Dig 256))
  (cfg : ByteArray) (sR : ℕ) (keyJ : FileJ (typedOracleCarrier L Bd aT aL) .test)
  (bd : (typedOracleCarrier L Bd aT aL).Bd → List Bool) (p0 p1 : PBt (typedOracleCarrier L Bd aT aL) .test)
  (isP0 isP1 : PBt (typedOracleCarrier L Bd aT aL) .test → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ q, isP0 q = true ↔ q = p0) (hp1 : ∀ q, isP1 q = true ↔ q = p1) (rest : ByteArray)
  (Lk : LinkCode (typedOracleCarrier L Bd aT aL) (K + 1)) (V : Leaves (typedOracleCarrier L Bd aT aL))

/-- **The laws on the proof file's data of the page**, under the test `fitFill`; premises hrd, hD,
hK, hp0, hp1 and the laws in S (the head: Premises). -/
theorem lawsJ_page (hrd : ∀ z z' w, rd z = some w → rd z' = some w → z = z')
    (hD : kindsAndWorkBelow256 D = true) (hK : K + 1 + 1 < 2 ^ 49) :
    LawsJ
      (pageRec Bd aT aL C D tF tJ t3 rd h₀ c cfg sR keyJ bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk
        V sp).proof
      (fitFill Bd aT aL C D tF tJ t3 rd S tl) (K + 1) :=
  laws_fill C D tF tJ t3 rd (silentProof h₀ c (reqOf (L := L) sp)) hrd
    (silentProof_laws h₀ c (reqOf (L := L) sp) S.okX S.hreq tl) hD (K + 1) hK

/-- **The page with its digests as data.** -/
def pageD (sp : X → ByteArray × ByteArray) (dK dP : Pd3) :
    PageJ (typedOracleCarrier L Bd aT aL) (K + 1) :=
  (pageRec Bd aT aL C D tF tJ t3 rd h₀ c cfg sR keyJ bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V
    sp).withPd dK dP

/-- **The laws that the proof file's encoding asks, at any digests dK, dP**; premises hrd, hD, hK,
hc, hp0, hp1 and the laws in S (the head: Premises). -/
theorem proofLaws_pageD (hrd : ∀ z z' w, rd z = some w → rd z' = some w → z = z')
    (hD : kindsAndWorkBelow256 D = true) (hK : K + 1 + 1 < 2 ^ 49) (hc : cfg.size = digBytes) (dK dP : Pd3) :
    ProofLaws (proofCutOf
      (pageD Bd aT aL C D tF tJ t3 rd h₀ c cfg sR keyJ bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V
        sp dK dP)
      (fitFill Bd aT aL C D tF tJ t3 rd S tl)) :=
  proofLaws_withPd _ _
    (lawsJ_page Bd aT aL C D tF tJ t3 rd h₀ c S tl cfg sR keyJ bd p0 p1 isP0 isP1 cfgL sh hp0 hp1
      rest Lk V hrd hD hK)
    (taken_pageFill cfg sR keyJ _ bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V _) hc
    (by show Params.labelFirst ≠ Fmt.recordLabel; decide)
    (by show Params.labelSharedProof ≠ Fmt.recordLabel; decide)
    (by show Params.labelSecondProof ≠ Fmt.recordLabel; decide) dK dP

/-- **The proof file's encoding at the page with its digests as data.** -/
noncomputable def mProofPageD (hrd : ∀ z z' w, rd z = some w → rd z' = some w → z = z')
    (hD : kindsAndWorkBelow256 D = true) (hK : K + 1 + 1 < 2 ^ 49) (hc : cfg.size = digBytes) (dK dP : Pd3)
    (back : StrCode (AllPts 256 (K + 1) (typedOracleCarrier L Bd aT aL))) :
    OracleCoding (typedOracleFamily 256 (K + 1) (typedOracleCarrier L Bd aT aL)) 256 :=
  mProof _
    (proofLaws_pageD Bd aT aL C D tF tJ t3 rd h₀ c S tl cfg sR keyJ bd p0 p1 isP0 isP1 cfgL sh hp0
      hp1 rest Lk V hrd hD hK hc dK dP) back

/-- **The three laws on what the encoding reads out of any hash function g**, under hrd, hD, hK,
hc, hp0, hp1, the laws in S and `Spells V.lf.put bd` (the head: Premises). -/
theorem proofCodedG_pageD (hrd : ∀ z z' w, rd z = some w → rd z' = some w → z = z')
    (hD : kindsAndWorkBelow256 D = true) (hK : K + 1 + 1 < 2 ^ 49) (hc : cfg.size = digBytes) (dK dP : Pd3)
    (back : StrCode (AllPts 256 (K + 1) (typedOracleCarrier L Bd aT aL))) (hS : Spells V.lf.put bd)
    (g : Fam (rom 256)) :
    ProofCodedG
      (proofCutOf
        (pageD Bd aT aL C D tF tJ t3 rd h₀ c cfg sR keyJ bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk
          V sp dK dP)
        (fitFill Bd aT aL C D tF tJ t3 rd S tl))
      (readBlocks
        (mProofPageD Bd aT aL C D tF tJ t3 rd h₀ c S tl cfg sR keyJ bd p0 p1 isP0 isP1 cfgL sh hp0
          hp1 rest Lk V hrd hD hK hc dK dP back) g) (oB (g ())) bd where
  chains := speaks_proof _ _ back g
  leaves := leafRowQ_proof _ _ back g bd hS
  nodes := nodeIs_proof _ _ back g

end OnBytes.K.Arm.ProofFront

#print axioms OnBytes.K.Arm.ProofFront.lawsJ_page
#print axioms OnBytes.K.Arm.ProofFront.proofLaws_pageD
#print axioms OnBytes.K.Arm.ProofFront.proofCodedG_pageD
