-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/Run1Is.lean: the outcome of the run function over a single oracle on a file is the run, in the
sense of this library's definitions, of a tree of oracle queries, under three tests told under 3.

A test (#guard) evaluates a run function, `run1 S dec file` (Run/PageQRun.lean), whose outcome is
"accepted" or the first stage that refuses. The definitions of this library (ZKCP/Defs.lean) speak
of something else: the run of a tree of oracle queries at an oracle. This file ties the two, for
every description S, decision dec and file that pass three tests. The tree is "the lenient reader,
then the compiled verifier over the single oracle, with all blocks of an answer asked for"; the
oracle is `oBits`, this library's extension of the format's oracle to all bit strings (at the bits
of a byte string whose first byte is not 4 it is the format's oracle at that string: `oBits_bytes`,
Run/OracleBits.lean). (The lenient reader, `laxWhole` in Run/ParseLax.lean, only cuts the file into
its parts. The lenient reader also refuses some files (what it refuses: part 1 of the head of
Run/ParseLax.lean). It still recomputes the hash chain, because the drawn positions say how long the
parts are; it tests no proof of work, walks no path and compares no root. Behind it the compiled
verifier makes these checks itself.)

Why this file exists. Run/RunIsPageH.lean (`run_pageW`) ends in a term that is good to state with:
that term takes the interface as a value (`pageVerdict`) and compares the list that comes with the
typed argument string with a key (`keep`, Run/ParsePaO.lean). A test evaluates another term, `run1`:
the interface stands behind a function of Unit, its two fields are written out, and that list is
handed on to the verifier. Here the two are tied, not only at a closed description but for all S and
dec.

The conditions on a wiring: `OKG` in the code.

Sources. No text from outside enters. On the conditions on a wiring (under 4) the heads of
Run/PlanQSLaws.lean and Run/PlanPull.lean were read; nothing of it is proved here.

1. What the file contains.
   `specKey S`: the key. It is a function of the description alone; no file sets it.
   `PQ.tree1 S dec h file`: the tree of queries. All data are made from S and dec; the protocol, its
     wiring and typing by Run/PlanQS.lean, the encoding's data by Run/PageQ.lean.
   Two statements (`Run.Spec.key_keep`, `Run.PQ.Spec.run1_is`).

2. What is checked when the file compiles. Nothing beyond the types; there are no tests here.

3. Theorems. Both statements are proved in Run/Run1IsProofs.lean.
   `key_keep`: its doc comment tells it.
   `run1_is`: the title's statement of `tree1` at `oBits ()`, under ok S = true, OKQ S = true and
     smallB S file = true.
   The three tests can be run: ok S and OKQ S (the run function makes them itself; where one fails
   it says "limits"), and smallB S file (Run/LaxDom.lean).
   So a test "run1 S dec file == accepted" at a closed S, dec, file, together with the three tests,
   says: the run of that tree at that oracle gives "true" with probability 1; and "not accepted"
   says: "false" with probability 1.

4. What is not claimed.
   All that the head of Run/RunIsPageH.lean leaves out is left out here too, but for its clause on
   the term that a test evaluates, which this file ties.
   No statement on soundness follows. No scheme and no bound. `verifyOneProtocol` taken alone belongs to no
   scheme under a theorem. A run is tied to a term, not to a security statement.
   `tree1`'s protocol and wiring have challenges as sampled values (`ck`, `chalOf`: a round's
   verifier message is the values that the format draws, field elements and positions among them).
   By the heads of Run/PlanQSLaws.lean and Run/PlanPull.lean, one of the conditions on a wiring,
   "uniform blocks give an exactly uniform verifier message", is false there at every round that
   draws a field element. So, at a description with a round that draws a field element, no theorem
   of the library that asks for the conditions on a wiring applies to this term as it stands. At no
   description are these conditions proved in Run/ at (`ck`, `chalOf`): `wqS_okg`
   (Run/PlanQSLaws.lean) has `ChalUnif` (Run/PlanQWireLaws.lean) as a hypothesis. The conditions
   hold with challenges as hash blocks, under the hypotheses of `planPull_okg` (Run/PlanPull.lean:
   `ckP`, `planPull_okg`); the tie there is Run/Run1Kit.lean [not in this library].
   Two things are not shown in this file; other files show them in part, each under the hypotheses
   stated there: that the two choices of challenge types give one verdict: Run/PageIs.lean
   (`pi_kits`),
   Run/PageIsRun.lean (`run_two`), Run/PageIsOne.lean [with its `one_two` not in this library; so
   here read: not proved in this library]. That this verdict is the verdict
   of the format's own verifier as this library renders it (`Fmt.verify`; that it renders the format
   page is not a theorem: Run/PageIsOne.lean [not in this library], under 4) on the file: in one direction on every file
   that passes the tests on sizes (Run/PageIsOne.lean [not in this library; so here read: not proved
   in this library]), in both on files whose roots differ
   (Run/PageIsCoreOne.lean [not in this library; so here read: not proved in this library]).
   That the strings which theImpl (pageQ ..) writes are the format page's is said by
   Run/CodingPage.lean and Run/PageQ.lean; Run/PageQFit.lean ties them to the spellings of
   Run/PlanQS.lean.
   `oBits` is this library's extension of the format's oracle (where it is the format's oracle is
   told above:
   `oBits_bytes`).
   It is not claimed that `run1` comes back in a given time.
   Whether the reader or the verifier refused is not carried over, only "accepted" or not.
   The run function over typed oracle functions (`runLaxS`, Run/PlanQS.lean) is not treated here.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.PageQRun
import Run.RunIsPageH

set_option autoImplicit false

namespace Run
open Rom Iop Compile Compile.Batch Run.Twin Run.Thin

/-- The key of a description: the one digest that the parser puts in front of the argument string:
the parameters' digest. -/
def specKey (S : _root_.Fmt.Spec) : List (Dig 256) :=
  [bytesToDig (_root_.Fmt.formatHash 169 0 1 _root_.Fmt.zero32 S.params)]

/-- States: the parser's own list is the key: `keep (specKey S)` keeps all that the lenient parser
`parseLaxWP` gives at `Fmt.formatHash`. -/
def Spec.key_keep : Prop :=
  ∀ (Y : Type) (E : ExtSpec) (P : PS Y E) (S : _root_.Fmt.Spec) (T : TypingP P) (b : ByteArray),
    keep (specKey S) (parseLaxWP (m := Id) _root_.Fmt.formatHash P S T b) =
      (parseLaxWP (m := Id) _root_.Fmt.formatHash P S T b).map Prod.snd

namespace PQ

/-- The tree of queries of which the run's verdict speaks: the lenient parser, then the compiled
verifier of one slot over the one oracle, all blocks asked. -/
def tree1 (S : _root_.Fmt.Spec) (dec : View → Bool) (h : OKQ S = true) (file : ByteArray) :
    ZKCP.OComp 256 Bool :=
  (paOfLax (fun _ : Unit => S) (TYS S (ck S.plan.field) dec).up
      (laxN S) (fun _ => Nat.le_refl _)).thenV
    (exitV (theImpl (pageQ S (ck S.plan.field) dec (kOf S + 1) h))
      (verifyOneProtocol (lam := 256) (K := kOf S + 1) (L := LbS (ck S.plan.field) (rds S) dec)
        (256 + 8 * S.plan.salt) 256 .onl (PSof (ck S.plan.field) (rds S) dec).up
        (wqS (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) (rds S) dec)
        (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS (ck S.plan.field) (rds S) dec) some
        (fun s => some (.inl s)) 0))
    (specKey S) () file

/-- States, for `ok S = true`, `h : OKQ S = true` and `smallB S file = true`: the run of
`tree1 S dec h file` at `oBits ()` is the point mass at the truth value of "`run1 S dec file` is
accepted". -/
def Spec.run1_is : Prop :=
  ∀ (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray), ok S = true →
    ∀ (h : OKQ S = true), smallB S file = true →
      (tree1 S dec h file).run (oBits ()) = PMF.pure (decide (run1 S dec file = .accepted))

end PQ
end Run
