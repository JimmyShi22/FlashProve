-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Arm/GuardCut.lean: the test "the cut of a file's encoding writes at this query", for the
key file's cut and for the proof file's, as the second test of the guarded run
(OnBytes/Maker/Page/GuardFit.lean). Definitions alone.

Why. The encodings under the soundness theorem write a string of the format only where their cut
writes (`cutKey`, OnBytes/K/Arm/KeyCut.lean; `cutProof`, OnBytes/K/Arm/ProofCut.lean): at a query
that passes the cut's tests of fitness and whose call lies in the domain of the format's hash. Every
other query they write behind an escape. The page's family `gJ` (OnBytes/Maker/Page/Frame.lean)
asks neither test. A run under `gJ` that is to stand where the statements on these encodings stand
has to refuse at a query at which the cut does not write.

Main definitions.
  `okCall`: there is a call, and it lies in the domain (`inDom`).
  `writesK C`, `writesP C`: the cut writes at a point. They build no string of bits: they ask the
    cut's own tests, kind by kind.
  `fitOf w`: a test on points as a test on queries: at every block of the answer; at a chain's
    first call (`tailOnly`, OnBytes/Maker/Page/Guard.lean) at the tail's block alone. The oracles
    `fbw` and `other` are turned away; `ann`, which has no block, is passed.
  `fitCutK C`, `fitCutP C`: `fitOf` at the two. To be laid for the letter `fit` of `okFitJ`,
    `runGuardFit`, `verifyGuardFit` at the page `C.P`.
OnBytes/K/Arm/GuardCutLaws.lean [not in this library]: they say what the cuts do.

To be minded. LEAVES. A cut writes a leaf by the page's field `leafX` alone; `gJ` falls back on the
field `leaf` where `leafX` does not write. So these tests turn away every leaf that `leaf` alone
writes. Whether the queries of one honest file pass hangs on what `leafX` is at the page meant: at a
page whose `leafX` writes nothing every run that asks a leaf ends with no value, and the guarded
verdict is a constant no. Each cut writes under its own file's tag, and under the key file's tag the
proof file's cut writes the seeds' spelling alone: a run of the other file's verifier is refused.
At a chain's first call the K blocks in front of the tail's are not tested: there `gJ` answers zeros
and an encoding answers by the hash behind its escape.

What is not claimed. No law is stated here. That an honest file's queries pass. That a yes of the
guarded run is a yes under an encoding's family: at a chain's first call the two families' answers
differ in the K front blocks, and that the compiled verifier reads none of these is shown nowhere.
Nothing on soundness.


-/
import OnBytes.K.Arm.ProofCut
import OnBytes.Maker.Page.GuardFit

set_option autoImplicit false

namespace OnBytes.K.Arm
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop TypedOracleCompiler.Run Rom
open OnBytes.Maker.Page
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- There is a call, and it lies in the domain of the format's hash. -/
def okCall : Option Fmt.OQ → Bool
  | some c => inDom c
  | none => false

/-- The point of a chain query and a block. -/
def fbPt (t : Tag) (q : FbIn 256 L t) (j : Fin (K + 1)) : RealPts 256 K L :=
  .inr (.inr (.inr (.inr (.inl ⟨t, q, j⟩))))

/-- The point of a query for the slot value. -/
def gPt (t : Tag) (q : JoiningRoundQuery 256 L t) : RealPts 256 K L :=
  .inr (.inr (.inr (.inr (.inr ⟨t, q⟩))))

/-- **The key file's cut writes at the point.** -/
def writesK (C : KeyCut L K) : RealPts 256 K L → Bool
  | .inl q => (C.P.leafX q).isSome
  | .inr (.inl q) => fitTree q
  | .inr (.inr (.inl q)) => okCall (rleafCall C.P.cfg C.P.sR q)
  | .inr (.inr (.inr (.inl q))) => fitTree q && okCall (rnodeCall C.P.cfg q)
  | .inr (.inr (.inr (.inr (.inl ⟨.test, x⟩)))) =>
    (C.P.seeds x).isSome || (C.fitFb x && okCall (fbCallJ C.P.key K x.1 x.2))
  | .inr (.inr (.inr (.inr (.inl ⟨.link, _⟩)))) => false
  | .inr (.inr (.inr (.inr (.inl ⟨.onl, _⟩)))) => false
  | .inr (.inr (.inr (.inr (.inr ⟨.test, q⟩)))) => C.fitG q && okCall (gCallJ C.P.key q)
  | .inr (.inr (.inr (.inr (.inr ⟨.link, _⟩)))) => false
  | .inr (.inr (.inr (.inr (.inr ⟨.onl, _⟩)))) => false

/-- **The proof file's cut writes at the point.** -/
def writesP (C : ProofCut L K) : RealPts 256 K L → Bool
  | .inl q => (C.P.leafX q).isSome
  | .inr (.inl q) => fitTree q
  | .inr (.inr (.inl q)) => okCall (rleafCall C.P.cfg C.P.sR q)
  | .inr (.inr (.inr (.inl q))) => fitTree q && okCall (rnodeCall C.P.cfg q)
  | .inr (.inr (.inr (.inr (.inl ⟨.onl, x⟩)))) =>
    C.fitFb x && okCall (fbCallJ C.P.proof K x.1 x.2)
  | .inr (.inr (.inr (.inr (.inl ⟨.test, x⟩)))) => (C.P.seeds x).isSome
  | .inr (.inr (.inr (.inr (.inl ⟨.link, _⟩)))) => false
  | .inr (.inr (.inr (.inr (.inr ⟨.onl, q⟩)))) => C.fitG q && okCall (gCallJ C.P.proof q)
  | .inr (.inr (.inr (.inr (.inr ⟨.test, _⟩)))) => false
  | .inr (.inr (.inr (.inr (.inr ⟨.link, _⟩)))) => false

/-- **A test on points as a test on queries.** -/
def fitOf (w : RealPts 256 K L → Bool) : (o : OracleName) → domOf 256 L o → Bool
  | .leaf, q => w (.inl q)
  | .node, q => w (.inr (.inl q))
  | .rleaf, q => w (.inr (.inr (.inl q)))
  | .rnode, q => w (.inr (.inr (.inr (.inl q))))
  | .fb t, q =>
    w (fbPt t q (Fin.last K)) &&
      (tailOnly (t := t) q || (List.finRange K).all fun k => w (fbPt t q k.castSucc))
  | .fbw _ _, _ => false
  | .g t, q => w (gPt t q)
  | .ann, _ => true
  | .other, _ => false

/-- **The key file's cut writes at the query.** -/
def fitCutK (C : KeyCut L K) : (o : OracleName) → domOf 256 L o → Bool := fitOf (writesK C)

/-- **The proof file's cut writes at the query.** -/
def fitCutP (C : ProofCut L K) : (o : OracleName) → domOf 256 L o → Bool := fitOf (writesP C)

end OnBytes.K.Arm
