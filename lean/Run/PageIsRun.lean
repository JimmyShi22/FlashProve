-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageIsRun.lean: four statements on three of the run functions behind the lenient reader
(`runLaxC`, `runLaxS`, `runLaxSP`) and on the compiled verifier behind that reader (`laxV`,
Run/PageIs.lean); part 3 below lists them with their hypotheses.

Run/PageIs.lean defines `laxV`, the compiled verifier behind the lenient reader, as a term to state
theorems with. Tests (#guard) evaluate other terms: `runLaxC` and `runLaxS` (Run/PlanQS.lean) and
`runLaxSP` (Run/PlanQSP.lean), which this library calls run functions. (The lenient reader,
`laxWhole` in
Run/ParseLax.lean, only cuts the file into its parts. The lenient reader also refuses some files
(what it refuses: part 1 of the head of Run/ParseLax.lean). It still recomputes the hash chain,
because the drawn positions say how long the parts are; it tests no proof of work, walks no path and
compares no root. Behind it the compiled verifier makes these checks itself.)
There is no slower form beside these run functions: `runLaxC` is itself written in the forms made
for a toy's full parameters (the fast lenient reader, the set of positions read split round by
round, the hash function's state kept). By a search of the tree, the names `runLaxS` and `runLaxSP`
stand in tests at the tiny and at the full parameters, among others in Run/M1RunP.lean,
Run/M1RunPF.lean, Run/M1RunF.lean.

1. What the file contains. Four statements. No other definition. Many statements of this library are
written twice: a definition in the namespace `Spec` states a proposition, and a theorem of the same
name outside that namespace proves it (lean/GLOSSARY.md).

2. What is checked when the file compiles. Nothing beyond the types; there are no tests here.

3. Theorems. All four are proved in Run/PageIsRunProofs.lean. Each holds under two tests that can be
run: `ok S = true` (the limits of the generic construction, Run/PlanQTypes.lean) and
`smallB S file = true` (Run/LaxDom.lean: sizes within the hash function's domain; it lets the
format's hash function `Fmt.formatHash`, by which the run functions read, stand for `Fmt.HO Fmt.oracle`, at
which `laxV` is stated). C is a choice of challenge types, and chal makes a verifier message from K
hash blocks (see the head of Run/Run1Kit.lean [not in this library]).
   `run_who`: for every C, K, chal, the outcome of `runLaxC`: its doc comment tells it.
   `run_lax`: its doc comment tells it.
   `run_two`: the two choices in use (`runLaxS`: challenges as sampled values; `runLaxSP`:
     challenges as hash blocks) give the same outcome on every file that passes the test on sizes.
   `run_half`: statement (F1) of Run/PageIs.lean at the run functions: what the format's strict
     verifier with the decision (`Fmt.verifyW` at `Fmt.HO Fmt.oracle`) accepts, both run functions
     accept.

   Which way `run_half` carries. It says: the format's strict verifier accepts ⇒ the run function
   accepts. Read backwards: the run function refuses ⇒ the format's strict verifier (at Fmt.HO
   Fmt.oracle) refuses. So a run function's refusal of a file carries over. A run function's
   acceptance does not, by this statement: that a file which a run function accepts is accepted by
   the format's strict verifier is the converse. Put otherwise: that the compiled verifier behind
   the lenient reader is at least as strict as the format's is not shown here.
   What each direction is good for. (F1) is the direction by which a soundness statement on the
   compiled verifier would reach the format's verifier: whatever such a statement says of the
   strings that the compiled verifier accepts holds of all that the format's verifier accepts; that
   the compiled verifier may accept more costs nothing there. The converse is the direction by which
   a completeness statement would; and it is what one needs in order to take a run function's
   "accepted" for the format's verifier's, which is a question about runs, not about soundness.

4. What is not claimed.
   The converse of `run_half`. It holds where the roots that the file sends differ, under a somewhat
   stronger test on sizes (`smallF` in the place of `smallB`): Run/PageIsCore.lean (there at
   `Fmt.verify`).
   Neither a soundness nor a completeness statement exists in Run/ or Fmt/ for the protocols on
   whose files these run functions have been evaluated, beyond conditions that are empty. The empty
   conditions are the fields `sound` and `low` of the record `Met`; their generic forms are
   `lts_sound`, `metOf` (Run/M1Door.lean) and `lb_sound`, `metB` (Run/BatchDoor.lean). The library
   has the building blocks of such protocols (sum-check, folds, code switches, base case:
   Cb/*/Ld*.lean) with soundness statements. Nothing in Run/ or Fmt/ connects the two: these
   protocols and the building blocks.
   The strict side stands here at `Fmt.HO Fmt.oracle`; at `Fmt.formatHash` (`Fmt.verify`) see `run_strict`,
   Run/StrictDom.lean. The run functions over a single oracle (`run1PF`, `run1K`):
   Run/PageIsOne.lean [not in this library]. The run functions behind the strict reader or the reader that fills in whole
   paths are not treated here.
   That Fmt/Rules8.lean renders the format page is not a theorem.

Sources. No text from outside enters.

Terms: lean/GLOSSARY.md.
-/
import Run.PageIs
import Run.PlanQSP

set_option autoImplicit false

namespace Run.PQ
namespace Spec

/-- States, for `ok S = true` and `smallB S file = true`, the outcome of `runLaxC`: the reader, if
the lenient reader at `Fmt.HO Fmt.oracle` gives nothing; else accepted if `laxV` is true, and the
verifier if not. -/
def run_who : Prop :=
  ∀ (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Iop.Dig 256) → C.Ch e k)
      (dec : View → Bool) (file : ByteArray),
    ok S = true → smallB S file = true →
    runLaxC S C K chal dec file =
      match laxWhole (m := Id) (_root_.Fmt.HO _root_.Fmt.oracle) S file with
      | none => Who.reader
      | some _ =>
        if laxV _root_.Fmt.oracle S C K chal dec file = true then Who.accepted else Who.verifier

/-- States, for `ok S = true` and `smallB S file = true`: `runLaxC`'s "accepted" is `laxV`. -/
def run_lax : Prop :=
  ∀ (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Iop.Dig 256) → C.Ch e k)
      (dec : View → Bool) (file : ByteArray),
    ok S = true → smallB S file = true →
    decide (runLaxC S C K chal dec file = .accepted) = laxV _root_.Fmt.oracle S C K chal dec file

/-- States, for `ok S = true` and `smallB S file = true`: the two choices of challenge types in use
give the same outcome on the file. -/
def run_two : Prop :=
  ∀ (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray),
    ok S = true → smallB S file = true → runLaxS S dec file = runLaxSP S dec file

/-- States, for `ok S = true` and `smallB S file = true`: (F1) of Run/PageIs.lean at the run
functions `runLaxSP` and `runLaxS`. -/
def run_half : Prop :=
  ∀ (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray), ok S = true →
    smallB S file = true →
    _root_.Fmt.verifyW (m := Id) (_root_.Fmt.HO _root_.Fmt.oracle) S
        (fun (_ : Unit) => dec) () file = true →
    runLaxSP S dec file = .accepted ∧ runLaxS S dec file = .accepted

end Spec
end Run.PQ
