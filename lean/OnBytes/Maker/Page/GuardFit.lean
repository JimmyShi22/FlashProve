-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/GuardFit.lean: the guarded run of Guard.lean with a second test on every query,
and the compiled verifier of one request run in this way.

States. Definitions only. `runGuardFit P O fit` is `detG` at "`okJ P` and `fit` both pass" and
`gJ P O`. `verifyGuardFit` is the value of `verifyBSR` (GuardVerify.lean) under it; no value counts
as no. Why: the table `P` encodes queries one to one only among well-formed ones (nonces n and n + 2
^ 64 share a string), and the encodings under the soundness theorem write the format's string only
at a query that passes their own tests (`KeyCut.lean`,
`ProofCut.lean`).
Under. No hypotheses: the file has no theorem.
Does not show.
  1. Which test `fit` is: it is a free parameter, a test on each oracle's queries.
  2. As a theorem, that `verifyGuardFit` at the test that passes everything is `verifyGuard`.
  3. More than Guard.lean and GuardVerify.lean show: all that their notes warn of holds here too.
  4. A verdict at every wiring: only where each round whose query is a chain's first (head f1, f3 or
     f4) has a verifier message that can take one value only (Guard.lean, limit 2).
  5. A verdict under the tag `.link` or where the hash chain does not join: always no.
  6. A yes where `P.leaf` and `P.leafX` write nothing: no to every proof string that opens a leaf of
     a tree over oracle messages or a stored table (oracle `leaf`).
  7. A yes where `P.sR` is not the file's salt length: no to that file, however it is converted.
  8. A yes where the instance is handed on in a later round (`L.late` is not none): under the proof
     file's tag, no to every proof string.
  9. Any theorem: this file states none.
 10. That any test `fit` is the test of one of these encodings.
 11. That the queries of an honest file pass `fit`.
 12. Anything on soundness.
Notes in full, with every limit at length, stand at the end of this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Maker.Page.GuardVerify

set_option autoImplicit false

namespace OnBytes.Maker.Page

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol ProtocolQueryLayout
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- `okJ P` passes the query, and the query fits. -/
def okFitJ (P : PageJ L K) (fit : (o : OracleName) → domOf 256 L o → Bool) (o : OracleName) (q : domOf 256 L o) :
    Bool :=
  okJ P o q && fit o q

/-- **The run under the page's family that refuses at a query which `okJ` turns away or which does
not fit.** -/
def runGuardFit {α : Type} (P : PageJ L K) (O : ByteArray → ByteArray)
    (fit : (o : OracleName) → domOf 256 L o → Bool) : OComp (typedOracleFamily 256 K L) α → Option α :=
  detG (S := typedOracleFamily 256 K L) (okFitJ P fit) (gJ P O)

/-- **The compiled verifier of a slot behind the test of `rsalt`, run so.** -/
def verifyGuardFit (P : PageJ L K) (O : ByteArray → ByteArray)
    (fit : (o : OracleName) → domOf 256 L o → Bool) (sMT sFS : ℕ) (t : Tag) {Y : Type}
    {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout 256 K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Y) (π : OneProtocolProof 256 Q) : Bool :=
  (runGuardFit P O fit
    (verifyBSR P.sR sMT sFS t Q wq embS embP xin embE depthReq cms x π)).getD false

end OnBytes.Maker.Page

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/Maker/Page/GuardFit.lean: the run that refuses at a query which `okJ` turns away
(OnBytes/Maker/Page/Guard.lean), with a second test on each query that is asked; and the compiled
verifier of a slot run so. Definitions alone.

Why. The page's coding of typed queries is one to one only among queries that fit: a round's nonce n
and n + 2 ^ 64 spell one string, and a query may hold fields that its call does not read. The
encodings under the soundness theorem write a format's string only at a query that passes their
tests, and every other query behind an escape (OnBytes/K/Arm/KeyCut.lean,
OnBytes/K/Arm/ProofCut.lean). So a run that is to stand where these statements
stand must refuse where an asked query does not fit, not only where `okJ` turns it away.

Main definitions.
  `runGuardFit P O fit`: `detG` at "`okJ P` and `fit` say yes" and `gJ P O`.
  `verifyGuardFit`: the value of `verifyBSR` (OnBytes/Maker/Page/GuardVerify.lean), at the page's
    own sR, by `runGuardFit`; no value is a no.
`fit` is a letter: a test on each oracle's queries. At the test that passes everything these are
`runGuard` and `verifyGuard` (of the run: `runGuardFit_all`, OnBytes/Maker/Page/GuardFitLaws.lean;
of the verdict: by unfolding, stated by no law).

To be minded. What the heads of OnBytes/Maker/Page/Guard.lean and
OnBytes/Maker/Page/GuardVerify.lean give to be minded holds of these terms too. The test `okJ` asks,
at a chain's first call (head f1, f3 or f4), for a string of the tail's block alone: so a term here
is a verdict only where the rounds that are asked under these heads have one verifier's message.
Under the link's tag and at a chain that does not join each of them is the constant no; at a page
whose `leaf` and `leafX` write nothing each says no to every string that opens a leaf; at a page
whose `sR` is not the file's, to every typing of that file; where the carrier hands an instance on
in a later round (`late` is not none), under the proof file's tag, to every string.

What is not claimed. No law is stated here. That any test `fit` is an encoding's own. That an honest
file's queries fit. Nothing on soundness.


-/
