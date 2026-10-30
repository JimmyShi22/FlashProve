-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/RunIsPage.lean: under the hypotheses of its statement, the definition's run of "the lenient
parser's tree, then the compiled verifier of one slot over the one oracle" at one fixed oracle,
`oBits ()`, is the point mass at the value of plain functions. This is Run/ParserHash.lean's last
statement (`ph_run`) at the coding by the format's own strings, with on the right the plain verifier
and the family of typed oracles in the forms that are written for an evaluator.

The definition's run of a tree of queries c at an oracle f is `c.run f` (ZKCP/Defs.lean): its output
distribution at f. The tree here (`thenV`, `exitV`), the coding m of typed queries into the one
oracle's strings and "the parser's text" are told in Run/RunIsV.lean.

One definition and one statement; the proof is in Run/RunIsPageProofs.lean. A join: two rewrites;
nothing else is shown here. Generic in the protocol's data.

Run/ParserHash.lean: `ph_run` holds for any coding m, and has on its right `verifyP` at
`famM (fun _ => L) K m oBy`. Here m := `theImpl C` (Run/CodingPage.lean), and
   in the place of `verifyP` is `verifyPB` (Run/ThinBits.lean: digests as lists of bits;
   `verifyPB_eq`: the same values, for every family);
   in the place of `famM .. (theImpl C) oBy` is `famC (fun _ => L) C oBy` (Run/CodingThin.lean: the
   writing side of the coding alone; `famC_famM`: the same family).

Main names:
  `pageVerdict`: its doc comment tells it.
  `Spec.run_page`: the title's statement, with the parser's text at `Fmt.HO Fmt.oracle` (the key
    compared). No hypothesis but that N bounds the parser's count, beside whatever the arguments
    hold as proofs.

Limits: this file does not say that the value of `pageVerdict` is the verdict of the format page's
own verifier on the file (the strict reader of Fmt/Rules8.lean with a run's decision: form, work,
openings, the protocol's checks): this ties a run to the term `verifyOneProtocol` at a protocol P, a typing
T, a coding's data C and descriptions sp that are any under `hN`: that they are a given run's, and
that `verifyOneProtocol` there accepts and refuses the files that the page's verifier does, is nowhere in
this chain.
"The coding by the format's own strings": that `theImpl C` writes a typed query that fits the plan
as the page's string for that use is Run/CodingPage.lean's word: not shown here.
What the heads of Run/ParserHash.lean, Run/RunIsThinFam.lean and Run/RunIsThin.lean list as not said
is not said here either: no scheme, no bound: a run tied to a term, not to a security statement; the
parser's text stands at `Fmt.HO Fmt.oracle`, not at `Fmt.formatHash`; `pageVerdict`, like `famVerdict`, is a
term to state with: it takes the interface L as a value: that the term which a run evaluates (the
interface behind a function, `L.early` and `L.late` written out) is its value at a closed
description is not shown here.
This file does not say that `verifyPB` and `famC` run fast, or at all: tests (#guard) in other files
(Run/ThinBitsGuard.lean, Run/PageQRun.lean) and the measured runs that their own files' heads tell
speak of that; no theorem can.
Nothing in this chain of files ties the value of `pageVerdict` to the format's own verifier. For the
data that the generic construction makes from a description it is shown elsewhere: the term that a
test (#guard) evaluates is tied to the run of the tree at these data (`tree1`), and so by
`run_pageW` (Run/RunIsPageH.lean) to `pageVerdict`, in Run/Run1Is.lean (`run1_is`); its verdict is
the format's own verifier's (`Fmt.verify`, Fmt/M1View.lean: this library's rendering of it; that it
renders the format page is no theorem) in one direction (what that verifier accepts, the run
accepts; not the converse) on every file that passes the tests on sizes (Run/PageIsOne.lean [not in this library]), and in
both on files whose roots differ (Run/PageIsCoreOne.lean [not in this library]); each under the tests that its statement
names.

Terms: lean/GLOSSARY.md.
-/
import Run.ParserHash
import Run.ThinBits
import Run.CodingThin

set_option autoImplicit false

namespace Run
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin

/-- The plain verifier with digests as bits (`verifyPB`) at the family `famC` of the coding by the
format's strings, given what the parser gave. -/
def pageVerdict {I X : Type} {K : ℕ} (L : BatchProtocol I X) {Y : Type} {E : ExtSpec} (sMT sFS : ℕ) (t : Tag)
    (P : PS Y E) (wq : ProtocolQueryLayout 256 K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
    (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (embE : E.Sym → Body L) (depthReq : ℕ) (C : PageC L K t) (ivk : List (Dig 256)) (x : Y) :
    Option (OneProtocolProof 256 P.up) → Bool
  | none => false
  | some π =>
    verifyPB (fun _ => L) (famC (fun _ => L) C oBy) L.early L.late sMT sFS t P wq embS embP
      xin embE depthReq ivk x π

/-- States, under the hypotheses below, `ph_run` at the coding by the format's own strings, with
`pageVerdict` on the right. -/
def Spec.run_page : Prop :=
  ∀ (I X : Type) (K : ℕ) (L : BatchProtocol I X) (Y : Type) (E : ExtSpec) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
      (wq : ProtocolQueryLayout 256 K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (C : PageC L K t) (sp : Y → _root_.Fmt.Spec)
      (T : Typing P.up) (N : ℕ) (hN : ∀ x, laxN (sp x) ≤ N) (ivk : List (Dig 256)) (x : Y)
      (b : ByteArray),
    ((paOfLax sp T N hN).thenV
          (exitV (theImpl C) (verifyOneProtocol (L := L) sMT sFS t P.up wq embS embP xin embE depthReq))
          ivk x b).run (oBits ()) =
      PMF.pure (pageVerdict L sMT sFS t P wq embS embP xin embE depthReq C ivk x
          (keep ivk (parseLaxW (m := Id) (_root_.Fmt.HO _root_.Fmt.oracle) (sp x) T b)))

end Run
