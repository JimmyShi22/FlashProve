-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/ProofPage.lean: a page over ANY interface with records, with the proof file's data laid
by `fillJ`, and the test `fitFill` on the proof file's chain queries. The proof file's encoding at
the page's cut by that test, and the laws on what it reads out of every hash function:
Johnson/Top/ProofPageD.lean.

THE LETTERS MEET; THIS IS NO TIE. Definitions, and one statement with its proof. The page of the two
makers' values and an entry's part (`pageM`, Johnson/Maker/Page/At.lean) is written for one
interface. Here its text is said once for all: so a description's own carrier of typed oracles gets
a page and a test by laying letters.

  `pageFill`        the page: digest, number of salt bytes, the two files' data and the reading of
                    bodies are letters; the four spellings that a page takes as they are come from
                    `withHoles` (OnBytes/Maker/Page/Holes.lean).
  `taken_pageFill`  `TakenCallsP` at every cut `proofCutOf` of that page.
  `fitFill`         the test on the proof file's chain queries.
  `pageRec`         `pageFill` with the proof file's data laid by `fillJ` at
                    `silentProof h c (reqOf sp)`.

PARAMETERS NOT LAID HERE: of `pageFill`'s written arguments all but proofJ, which `pageRec` lays:
p0, p1, isP0, isP1, cfgL, sh, rest (the seeds' two queries and their code), Lk (the entry file's
code), V (the code of leaves), keyJ, cfg (the code of vertices is made of it), sR, bd, and the
proofs hp0, hp1 (isP0 and isP1 say yes at p0 and at p1 alone). What the key file's, the entry file's
and the proof file's encodings have to share where they serve one verifier is not said here. No
statement of this file names `mKey`, `implL2` or `ThreeAgree`. By reading, the cut does not read bd,
which stands in the laws of Johnson/Top/ProofPageD.lean. The other parameters of the section Records
are free too: I, X, the interface L, K, Bd, aT, aL, C, D, tF, tJ, t3, rd, h, c, sp, r₀, S, tl; in
the section Page also proofJ, which `pageRec` lays.

The set of requests and the test on the records come as one value S of `FrontSet`
(Johnson/Top/FrontSet.lean): sp is one to one on what passes S.okS; S.isR lets r₀ alone through.

THE FORMAT: a proof's first statement has four items: table, stored copy, request, the request
file's words (`Params.First.statement`, OnBytes/Params/Chains.lean); sp : X → ByteArray × ByteArray
spells the third and the fourth.

ON EMPTINESS. Where both strings held the tokens through digests of the second hash function alone,
no value S would let all real requests through, by counting; with the request file's bytes as the
second string one value has them all, under premises on the object (`FrontSet.ownWords`,
Johnson/Flat/FrontSetOwnAt.lean). That the second string is a request file's bytes is said of no sp
here. What is said over a value S is said of the requests that S has, and of no other: a set of
early parts on which the pair is one to one; that it is named before the hash is drawn is meant, and
is asked nowhere here (the head of OnBytes/K/Arm/ProofCoded.lean says the like). An encoding made
from the test writes the format's string at no first query of a call whose request lies outside that
set (by reading; no theorem). At one inside it writes that string only where the other tests pass
too, among them: the instance's two records pass S.isR (so both are r₀), both strings and the copy's
number are short, `cmsFit`, `tableSmall` (`fFrontP`, OnBytes/Maker/Page/FitSilent.lean; `okItems`,
Johnson/Top/FrontItems.lean); besides, the query has no root and a salt of 256 bits, its plain part
is read as the front round's, and the call lies in the hash's domain (`fitPart`, `fitFb`,
OnBytes/K/Arm/FileInj.lean; `frontAt`, OnBytes/Maker/Page/FitAt.lean). None of these is shown here.
At `h := Fmt.HO Fmt.oracle` the page holds three digests that are values of the hash function: an
encoding at its cut is then chosen after the hash.

Not claimed. That a verifier's queries pass the tests. Nothing on soundness.

-/
import Johnson.Top.FrontItems
import Johnson.Top.FrontSet
import OnBytes.Maker.Page.FitSilent
import OnBytes.K.Arm.ProofGlue
import OnBytes.K.Arm.ProofCoded
import OnBytes.Maker.Page.Holes

set_option autoImplicit false

namespace OnBytes.K.Arm.ProofFront

open _root_.Run _root_.Run.PQ Iop Rom
open OnBytes.Maker OnBytes.Maker.Page
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run
open TypedOracleCompiler.Compile.Batch.Cms (typedOracleCarrier)
open TypedOracleCompiler.Run.SeedPage (LinkCode)
open TypedOracleCompiler.Run.PageG (Leaves)
open _root_.Compile.Joined (JoinMsg)
open OnBytes.K.Arm (TakenCallsP takenCallsP_of)
open OnBytes.K.Arm.ProofGlue (proofCutOf)
open OnBytes.K.Arm.FileInj (FitJ)

/-! ## The page, at any interface -/

section Page
variable {I X : Type} {L : TypedOracleCompiler.Iop.BatchProtocolWithLeafBody I X} {K : ℕ} (cfg : ByteArray) (sR : ℕ)
  (keyJ : FileJ L .test) (proofJ : FileJ L .onl) (bd : L.Bd → List Bool) (p0 p1 : PBt L .test)
  (isP0 isP1 : PBt L .test → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ q, isP0 q = true ↔ q = p0) (hp1 : ∀ q, isP1 q = true ↔ q = p1) (rest : ByteArray)
  (Lk : LinkCode L K) (V : Leaves L)

/-- **The page.** -/
def pageFill : PageJ L K :=
  withHoles L p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest K
    { cfg := cfg
      key := keyJ
      proof := proofJ
      sR := sR
      leaf := leafOf bd
      link := fun _ => none
      seeds := fun _ => none
      leafX := fun _ => none
      other := fun _ => none } Lk V

/-- **What is asked of the page's two spellings holds at every cut `proofCutOf` of it.** -/
theorem taken_pageFill (Φ : FitJ L .onl) :
    TakenCallsP (proofCutOf
      (pageFill cfg sR keyJ proofJ bd p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest Lk V) Φ) :=
  takenCallsP_of _ V rfl p0 p1 isP0 isP1 cfgL sh hp0 hp1 rest rfl

end Page

/-! ## The test, and the page with the proof file's data laid, at any interface with records -/

section Records
variable {I X : Type} {L : HolographicProtocol I X} (Bd : Type) (aT : RoundSplits L.offline.shape) (aL : RoundSplits L.link.shape)
  {K : ℕ} (C : CK) (D : WholeD) (tF : FrontMsg (List E)) (tJ : JoinMsg (List E) ByteArray)
  (t3 : ByteArray)
  (rd : PBt (typedOracleCarrier L Bd aT aL) .onl →
    Option (PlainPart (chainsOf C D tF tJ t3).sh (chainsOf C D tF tJ t3).ann))
  (h : HId) (c : Params.ProofChains) {sp : X →
      ByteArray × ByteArray} {r₀ : L.Rec} (S : FrontSet L sp r₀)
  (tl : Dig 256 → List E → List (Dig 256))
  (cfg : ByteArray) (sR : ℕ) (keyJ : FileJ (typedOracleCarrier L Bd aT aL) .test)
  (bd : (typedOracleCarrier L Bd aT aL).Bd → List Bool) (p0 p1 : PBt (typedOracleCarrier L Bd aT aL) .test)
  (isP0 isP1 : PBt (typedOracleCarrier L Bd aT aL) .test → Bool) (cfgL : List (Dig 256)) (sh : Bits)
  (hp0 : ∀ q, isP0 q = true ↔ q = p0) (hp1 : ∀ q, isP1 q = true ↔ q = p1) (rest : ByteArray)
  (Lk : LinkCode (typedOracleCarrier L Bd aT aL) (K + 1)) (V : Leaves (typedOracleCarrier L Bd aT aL))

/-- **The test on the proof file's chain queries.** -/
def fitFill : FitJ (typedOracleCarrier L Bd aT aL) .onl :=
  fitAt C D tF tJ t3 rd (fFrontP tl (reqOf (L := L) sp) S.okX) (fJoin tl) fSeam

/-- The page with the proof file's data laid by `fillJ`. sp: the spelling of a request. -/
def pageRec (sp : X → ByteArray × ByteArray) : PageJ (typedOracleCarrier L Bd aT aL) (K + 1) :=
  pageFill cfg sR keyJ (fillJ C D tF tJ t3 rd (silentProof h c (reqOf (L := L) sp))) bd p0 p1 isP0
    isP1 cfgL sh hp0 hp1 rest Lk V

end Records

end OnBytes.K.Arm.ProofFront

#print axioms OnBytes.K.Arm.ProofFront.taken_pageFill
