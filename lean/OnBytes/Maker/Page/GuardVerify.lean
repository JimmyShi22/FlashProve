-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/GuardVerify.lean: the compiled verifier of one request behind a test on the field
`rsalt` of the proof string, and its verdict by the guarded run of Guard.lean.

States. Definitions only. `rsaltFit sR depthReq π`: `rsalt` has 8 sR + 64 bits, and its last 64 bits
are the number 2 ^ depthReq + π.slot. `verifyBSR`: the compiled verifier `verifyOneProtocol` where `rsaltFit`
passes; otherwise no, with no query. `verifyGuard`: the value of `verifyBSR` under `runGuard`; no
value counts as no. Why: once the hash chain has joined, `verifyOneProtocol` tests neither the length of
`rsalt` nor anything inside it; `rsalt` is hashed with the request's slot value; the protocol's
decision never sees it.
Under. No hypotheses: the file has no theorem.
Does not show.
  1. A yes where the hash chain does not join (a protocol of local rounds only): there the strict
     format wants `rsalt` empty, so no proof string passes both that test and `rsaltFit`.
  2. A verdict on an entry file: under the tag `.link` `verifyGuard` says no at every input (by
     reading the definitions), and every theorem about its yes is vacuous there.
  3. The right index from depthReq = 64 on: the 64-bit number wraps (the programs' trees have at
     most 48 levels).
  4. Two lengths of salt: a table `P` has one sR for the key file's and the proof file's requests.
  5. Any change of `verifyOneProtocol`: it is used as it is.
  6. A verdict at every wiring: only where each round whose query is a chain's first (head f1, f3 or
     f4) has a verifier message that can take one value only (Guard.lean, limit 2); the wiring `wq`
     is a parameter here.
  7. A yes where the instance is handed on in a later round (`L.late` is not none): that round's
     query has no string under the proof file's tag, so the verdict is no, at every `P` and O.
  8. That any real file gets a yes.
  9. Any theorem: the theorems are in GuardLaws.lean.
 10. That an honest file, converted to a proof string, passes `rsaltFit`.
 11. Anything on soundness.
Notes in full, with every limit at length, stand at the end of this file.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Maker.Page.Guard
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier

set_option autoImplicit false

namespace OnBytes.Maker.Page

open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Iop Rom
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol ProtocolQueryLayout
open _root_.Run

variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {K : ℕ}

/-- **The field `rsalt` is a salt of sR bytes and the word of the leaf's index.** -/
def rsaltFit (sR depthReq : ℕ) {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (π : OneProtocolProof 256 Q) :
    Bool :=
  decide (π.rsalt.length = 8 * sR + 64) &&
    decide (π.rsalt.drop (8 * sR) = bytesToBits (Fmt.u64n (2 ^ depthReq + π.slot)))

/-- **The compiled verifier of a slot behind the test of `rsalt`.** -/
def verifyBSR (sR sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E)
    (wq : ProtocolQueryLayout 256 K Q) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Y) (π : OneProtocolProof 256 Q) :
    TypedOracleComputation 256 K L Bool :=
  if rsaltFit sR depthReq π then verifyOneProtocol sMT sFS t Q wq embS embP xin embE depthReq cms x π
  else pure false

/-- **Its verdict under the page's family, by the guarded run.** -/
def verifyGuard (P : PageJ L K) (O : ByteArray → ByteArray) (sMT sFS : ℕ) (t : Tag) {Y : Type}
    {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout 256 K Q)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (cms : List (Dig 256)) (x : Y) (π : OneProtocolProof 256 Q) : Bool :=
  (runGuard P O (verifyBSR P.sR sMT sFS t Q wq embS embP xin embE depthReq cms x π)).getD false

end OnBytes.Maker.Page

/-
Notes in full (other files' comments call these notes "the head of" this file).

OnBytes/Maker/Page/GuardVerify.lean: the compiled verifier of a slot behind a test of the field
`rsalt`, and its verdict under the page's family by the guarded run (`runGuard`,
OnBytes/Maker/Page/Guard.lean). Definitions alone.

Why. The input of the request tree's leaf is the slot value with the field `rsalt` of the proof
string behind it. The compiled verifier (OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean, `verifyOneProtocol`) tests
neither the length of `rsalt`, once the chain has joined, nor anything inside it. The page reads
of that string the salt's 8 sR bits and one word of 64 bits, the leaf's index in its tree, which
becomes the index of the format's call (`rleafCall`, OnBytes/Maker/Page/Frame.lean). The protocol's
decision does not see `rsalt`: so the test stands in front of the compiled verifier, not in it.

Main definitions.
  `rsaltFit sR depthReq π`: `rsalt` has 8 sR + 64 bits, and its last 64 are the word of
    2 ^ depthReq + π.slot, as a typing of a file lays them (`rsOf`, OnBytes/Maker/TypingW.lean).
  `verifyBSR`: `verifyOneProtocol` where `rsaltFit` says yes; else no, with no query. An oracle algorithm.
  `verifyGuard`: the value of `verifyBSR`, at the page's own sR, by `runGuard`; no value is a no.

To be minded. `rsaltFit` refuses every string of a protocol whose chain does not join: there the
strict format wants `rsalt` empty. UNDER THE TAG OF THE ENTRY FILE (`.link`) `verifyGuard` SAYS NO
AT EVERY INPUT, by the texts: a chain that does not join fails one of these two tests, and a chain
that joins asks the oracle `g` under that tag, for which the page writes nothing. So this term is no
verdict on an entry file, and the laws on its yes are empty there. The word of the index wraps from
depthReq = 64 on (`Fmt.u64n`); the program's shapes have at most 48 levels. A page has one sR for
the key file's and the proof file's request leaves. `verifyOneProtocol` itself does not turn. `okJ` asks, at
a chain's first call (head f1, f3 or f4), for a string of the tail's block alone
(OnBytes/Maker/Page/Guard.lean, "To be minded"): so `verifyGuard` is a verdict only where the rounds
that are asked under these heads have one verifier's message; wq is a letter here. Where the carrier
hands an instance on in a later round (`late` is not none) the query of that round has no string:
under the proof file's tag the guarded chain then has no value, at every page and every O. NO REAL
FILE IS SHOWN HERE TO GET A YES.


What is not claimed. No law is stated here (OnBytes/Maker/Page/GuardLaws.lean). That a typing of an
honest file passes. Nothing on soundness.


-/
