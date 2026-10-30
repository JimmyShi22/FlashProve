-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/RunIsPageH.lean: under the hypotheses of its statements, the definition's run of "the lenient
parser's tree, then the compiled verifier of one slot over the one oracle" at one fixed oracle,
`oBits ()`, is the point mass at the value of plain functions. This is Run/RunIsPage.lean's
statement (`run_page`) with the parser's text at the format's hash itself (`Fmt.formatHash`), given the four
bounds on sizes of Run/LaxDom.lean.

The definition's run of a tree of queries c at an oracle f is `c.run f` (ZKCP/Defs.lean): its output
distribution at f. The tree here (`thenV`, `exitV`), a coding of typed queries into the one oracle's
strings and "the parser's text" are told in Run/RunIsV.lean.

Three statements; the proofs are in Run/RunIsPageHProofs.lean. Joins: one rewrite, then one more,
then one more; nothing else is shown here. Generic in the protocol's data.

Run/RunIsPage.lean: `run_page` has on its right the lenient parser's text in the identity monad at
`Fmt.HO Fmt.oracle` (the format's hash made from the format's oracle); a run by an evaluator takes
`Fmt.formatHash`, and the fast reader is proved equal to the parser's text at `Fmt.formatHash`. Run/LaxDom.lean:
`lax_HO`: the two give one parse if `smallB S b` holds: the parameters' bytes, the statement's, the
file's and the number of rounds stay within what the hash's domain allows.

Main names:
  `Spec.run_pageH`: `smallB (sp x) b = true` → `run_page` with the parser's text at `Fmt.formatHash`. No
    further hypothesis but that N bounds the parser's count, beside whatever the arguments hold as
    proofs.
  `Spec.run_pageW`: the same, for a typing T at the skeleton (Run/ParseThin.lean: `TypingP P`; on
    the left its `T.up`), with on the right the parser of Run/ParseThin.lean at `Fmt.formatHash`
    (`parseLaxWP`).
  `Spec.run_pageF`: the same, with on the right the reader written for a run at real sizes
    (`parseLaxFP`, Run/ParseLaxFast.lean).
  `smallB` is a test that can be run at a given description and file.

Limits: what the head of Run/RunIsPage.lean lists as not said is not said here either, but for its
clause on `Fmt.HO Fmt.oracle`, which this file closes under `smallB`. Written out, since this is the
chain's last link:
This file does not say that the value of `pageVerdict` is the verdict of the format page's own
verifier on the file (the strict reader of Fmt/Rules8.lean with a run's decision: form, work,
openings, the protocol's checks): the protocol P, the typing T, the coding's data C and the
descriptions sp are any under `smallB` and `hN`: that they are a given run's, and that `verifyOneProtocol`
there accepts and refuses the files that the page's verifier does, is nowhere in this chain.
That `theImpl C` writes a typed query that fits the plan as the page's string for that use is
Run/CodingPage.lean's word: not shown here.
No scheme, no bound: a run tied to a term, not to a security statement.
`pageVerdict` is a term to state with (it takes the interface as a value): that the term which a run
evaluates is its value at a closed description is not shown here.
This file does not say that the right side computes, or in what time.
Nothing in this chain of files ties the value of `pageVerdict` to the format's own verifier. For the
data that the generic construction makes from a description it is shown elsewhere: the term that a
test (#guard) evaluates is tied to the run of the tree at these data (`tree1`), and so by
`run_pageW` to `pageVerdict`, in Run/Run1Is.lean (`run1_is`); its verdict is the format's own
verifier's (`Fmt.verify`, Fmt/M1View.lean: this library's rendering of it; that it renders the
format page is no theorem) in one direction (what that verifier accepts, the run accepts; not the
converse) on every file that passes the tests on sizes (Run/PageIsOne.lean [not in this library]), and in both on files
whose roots differ (Run/PageIsCoreOne.lean [not in this library]); each under the tests that its statement names.

Terms: lean/GLOSSARY.md.
-/
import Run.RunIsPage
import Run.LaxDom
import Run.ParseLaxFast

set_option autoImplicit false

namespace Run
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin

/-- States `run_page` with the parser at the format's hash, if `smallB (sp x) b` holds and N bounds
the parser's count (`hN`). -/
def Spec.run_pageH : Prop :=
  ∀ (I X : Type) (K : ℕ) (L : BatchProtocol I X) (Y : Type) (E : ExtSpec) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
      (wq : ProtocolQueryLayout 256 K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (C : PageC L K t) (sp : Y → _root_.Fmt.Spec)
      (T : Typing P.up) (N : ℕ) (hN : ∀ x, laxN (sp x) ≤ N) (ivk : List (Dig 256)) (x : Y)
      (b : ByteArray),
    smallB (sp x) b = true →
    ((paOfLax sp T N hN).thenV
          (exitV (theImpl C) (verifyOneProtocol (L := L) sMT sFS t P.up wq embS embP xin embE depthReq))
          ivk x b).run (oBits ()) =
      PMF.pure (pageVerdict L sMT sFS t P wq embS embP xin embE depthReq C ivk x
          (keep ivk (parseLaxW (m := Id) _root_.Fmt.formatHash (sp x) T b)))

/-- States the same, under the hypotheses below, with the parser of Run/ParseThin.lean. -/
def Spec.run_pageW : Prop :=
  ∀ (I X : Type) (K : ℕ) (L : BatchProtocol I X) (Y : Type) (E : ExtSpec) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
      (wq : ProtocolQueryLayout 256 K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (C : PageC L K t) (sp : Y → _root_.Fmt.Spec)
      (T : TypingP P) (N : ℕ) (hN : ∀ x, laxN (sp x) ≤ N) (ivk : List (Dig 256)) (x : Y)
      (b : ByteArray),
    smallB (sp x) b = true →
    ((paOfLax sp T.up N hN).thenV
          (exitV (theImpl C) (verifyOneProtocol (L := L) sMT sFS t P.up wq embS embP xin embE depthReq))
          ivk x b).run (oBits ()) =
      PMF.pure (pageVerdict L sMT sFS t P wq embS embP xin embE depthReq C ivk x
          (keep ivk (parseLaxWP (m := Id) _root_.Fmt.formatHash P (sp x) T b)))

/-- States the same, under the hypotheses below, with the reader that is written for a run. -/
def Spec.run_pageF : Prop :=
  ∀ (I X : Type) (K : ℕ) (L : BatchProtocol I X) (Y : Type) (E : ExtSpec) (sMT sFS : ℕ) (t : Tag) (P : PS Y E)
      (wq : ProtocolQueryLayout 256 K P.up) (embS : (p : OPos (up P.S)) → OSym (up P.S) p → Body L)
      (embP : PlainPart (up P.S) P.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
      (embE : E.Sym → Body L) (depthReq : ℕ) (C : PageC L K t) (sp : Y → _root_.Fmt.Spec)
      (T : TypingP P) (N : ℕ) (hN : ∀ x, laxN (sp x) ≤ N) (ivk : List (Dig 256)) (x : Y)
      (b : ByteArray),
    smallB (sp x) b = true →
    ((paOfLax sp T.up N hN).thenV
          (exitV (theImpl C) (verifyOneProtocol (L := L) sMT sFS t P.up wq embS embP xin embE depthReq))
          ivk x b).run (oBits ()) =
      PMF.pure (pageVerdict L sMT sFS t P wq embS embP xin embE depthReq C ivk
          x (keep ivk (parseLaxFP P (sp x) T b)))

end Run
