-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/StrictDom.lean: the format's strict reader gives the same result at two hash functions that
agree on the hash function's domain, given bounds on sizes and answers of the right length (true of
`Fmt.formatHash`); so the strict verifier gives the same verdict at `Fmt.HO Fmt.oracle` and at `Fmt.formatHash`.

The strict reader is Fmt/Rules8.lean's `wholeChain`, this library's rendering of the reader that
the format page (docs/format/FORMAT.md, which comes with the programs; here in an edition that is
not the one that ships) prescribes;
followed by a
decision it is the strict verifier (Fmt/M1View.lean). The format's hash function `Fmt.formatHash` and
`Fmt.HO Fmt.oracle`, the same function rebuilt from the format's oracle, agree on the hash
function's domain (Fmt/Rules23.lean: `hDom`), and beyond it no agreement of the two is stated in
Run/ or Fmt/ (see Run/LaxDom.lean, the head, 4). The files of the same kind are Run/LaxDom.lean
(the lenient reader) and Run/FullDom.lean (the reader that fills in whole paths).

1. What the file contains. Three statements (`Run.Spec.strict_dom`, `Run.Spec.strict_HO`,
`Run.Spec.run_strict`). No other definition.
   The test that they require is Run/FullDom.lean's `smallF S b`. It consists of: `smallB S b`
   (Run/LaxDom.lean: the parameters, the statement, the file, the number of rounds); S.cfg has 32
   bytes; at every opening of every round `smallSh` holds (Run/OpenDom.lean: the tree's number, its
   depth, a column's words, and that a stored tree has the number 0) and, for a tree given from
   outside, its start has 32 bytes. `smallF` can be run.

2. What is checked when the file compiles. Nothing beyond the types; there are no tests (#guard)
here.

3. Theorems. All three are proved in Run/StrictDomProofs.lean.
   `strict_dom`, `strict_HO`: their doc comments tell them.
   `run_strict`: Run/PageIsRun.lean's `run_half` with the format's verifier at the format's own
      hash function: ok S = true → smallF S file = true → Fmt.verify S (fun _ => dec) () file =
      true → runLaxSP S dec file = accepted ∧ runLaxS S dec file = accepted. (`runLaxSP` and
      `runLaxS` are the run functions for the compiled verifier behind the lenient reader; see the
      head of Run/PageIsRun.lean.)

   Which way `run_strict` carries. The format's verifier accepts ⇒ the run function accepts. Read
   backwards: the run function refuses ⇒ the format's verifier refuses. A run function's acceptance
   does not carry over by this statement. `run_strict`'s direction is the one by which a soundness
   statement on the compiled verifier would reach the format's verifier. The converse is the
   direction by which a completeness statement would, and it is what one needs in order to take a
   run function's "accepted" for the format's verifier's. The converse holds on files whose roots
   differ: Run/PageIsCore.lean.

4. What is not claimed.
   It is not claimed that the bounds are needed. `smallF` is a sufficient test, not a rendering of
   the format page's rule on sizes. (`smallSh`'s bound on depths is the page's own, R7.16; see
   Run/OpenDom.lean.)
   The converse of `run_strict` is not claimed (see above).
   Neither a soundness nor a completeness statement exists in Run/ or Fmt/ for the protocols on
   whose files these run functions have been evaluated, beyond conditions that are empty. The empty
   conditions are the fields `sound` and `low` of the record `Met`; their generic forms are
   `lts_sound`, `metOf` (Run/M1Door.lean) and `lb_sound`, `metB` (Run/BatchDoor.lean). The library
   has the building blocks of such protocols (sum-check, folds, code switches, base case:
   Cb/*/Ld*.lean) with soundness statements. Nothing in Run/ or Fmt/ connects the two: these
   protocols and the building blocks.
   All that the head of Run/PageIsRun.lean leaves out is left out here too, but for what
   `run_strict` states.

Sources. No text from outside enters beyond what Run/LaxDom.lean, Run/OpenDom.lean and
Run/FullDom.lean name in their heads.

Terms: lean/GLOSSARY.md.
-/
import Run.FullDom
import Run.PageIsRun
import Fmt.M1View

set_option autoImplicit false

namespace Run
open _root_.Fmt (hDom dlen)

namespace Spec

/-- States, of the strict reader at two hashes in the identity monad that agree on the domain: if
the answers of h have `dlen n` bytes and `smallF S b = true`, `Fmt.wholeChain` gives the same at h'
and at h. What is not claimed: the head, 4. -/
def strict_dom : Prop :=
  ∀ (h h' : HId), (∀ n t i s b, hDom n t i s b = true → h' n t i s b = h n t i s b) →
    (∀ n t i s b, ByteArray.size (h n t i s b) = dlen n) →
    ∀ (S : _root_.Fmt.Spec) (b : ByteArray), smallF S b = true →
      _root_.Fmt.wholeChain (m := Id) h' S b = _root_.Fmt.wholeChain (m := Id) h S b

/-- States, under `smallF S b = true`: the page's strict verifier at the oracle's hash is the one
at the format's hash. What is not claimed: the head, 4. -/
def strict_HO : Prop :=
  ∀ (Y : Type) (S : _root_.Fmt.Spec) (dec : Y → _root_.Fmt.View → Bool) (y : Y) (b : ByteArray),
    smallF S b = true →
    _root_.Fmt.verifyW (m := Id) (_root_.Fmt.HO _root_.Fmt.oracle) S dec y b =
      _root_.Fmt.verify S dec y b

/-- States (F1) of Run/PageIs.lean at the run functions, the page's verifier at the format's own
hash: under `PQ.ok S = true` and `smallF S file = true`, what `Fmt.verify` accepts, `PQ.runLaxSP`
and `PQ.runLaxS` accept. A run function's acceptance does not carry over by this statement: the
head, 3 and 4. -/
def run_strict : Prop :=
  ∀ (S : _root_.Fmt.Spec) (dec : PQ.View → Bool) (file : ByteArray), PQ.ok S = true →
    smallF S file = true → _root_.Fmt.verify S (fun (_ : Unit) => dec) () file = true →
    PQ.runLaxSP S dec file = .accepted ∧ PQ.runLaxS S dec file = .accepted

end Spec
end Run
