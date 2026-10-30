-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageIsCore.lean: the compiled verifier behind the lenient reader gives the verdict of the
format's verifier on every file whose roots differ and whose sizes pass a test, for a description
within the limits of the generic construction (the run functions over typed oracle functions).

Two verifiers for a proof file are compared. The first is `Fmt.verify` (Fmt/M1View.lean): this
library's rendering in Lean of the strict verifier that the format page (docs/format/FORMAT.md,
which comes with the programs; here in an edition that is not the one that ships) prescribes,
followed by a decision on what was read. The second is the verifier that the compiler of this
library produces from a typed protocol. It runs behind the lenient reader (`laxWhole`,
Run/ParseLax.lean; "lax" in names), which only cuts the file into its parts. The lenient reader also
refuses some files (what it refuses: part 1 of the head of Run/ParseLax.lean).
The lenient reader still recomputes the hash chain, because the drawn positions say how long the
parts are; it tests no proof of work, walks no path and compares no root. Behind it the compiled
verifier makes these checks itself, here through queries to typed oracle functions. `runLaxSP` and
`runLaxS` (Run/PlanQSP.lean, Run/PlanQS.lean) are the run functions for this second verifier that
the tests (#guard) of other files evaluate (a run function maps a file to an outcome: "accepted", or
the first stage that refuses); they differ in the choice of challenge types (challenges as hash
blocks, challenges as sampled values).

Sources. The statement joins pi_core (statement (F2) of Run/PageIs.lean) with run_lax, run_two
(Run/PageIsRun.lean), fit_pull (Run/PageIsProofs.lean) and strict_HO (Run/StrictDom.lean).

1. What the file contains. One statement (`Run.PQ.Spec.core_lax`). No other definition.

2. What is checked when the file compiles. Nothing beyond the type of the statement; there are no
tests here.

3. Theorems. The statement is proved in Run/PageIsCoreProofs.lean, which also has the proof of
`pi_core`.
   The three tests can be run. ok S: the description lies within the limits of the generic
   construction (Run/PlanQTypes.lean). smallF S file: all sizes lie within the hash function's
   domain (Run/FullDom.lean). rootsDiffer Fmt.formatHash S file: the Merkle roots that the file sends are
   pairwise different as bytes (Run/PageIs.lean, whose head explains why this is asked).
   Whether the reader or the verifier refuses is no part of Fmt.verify's truth value and is not
   compared.
   Without the test on roots one direction holds, on every file that passes the other two tests:
   what Fmt.verify accepts, the run functions accept (Run/StrictDom.lean: `run_strict`).

4. What is not claimed.
   No statement on soundness follows. No scheme and no bound. Neither a soundness nor a completeness
   statement exists in Run/ or Fmt/ for the protocols on whose files these run functions have been
   evaluated, beyond conditions that are empty. The empty conditions are the fields `sound` and
   `low` of the record `Met`; their generic forms are `lts_sound`, `metOf` (Run/M1Door.lean) and
   `lb_sound`, `metB` (Run/BatchDoor.lean). The library has the building blocks of such protocols
   (sum-check, folds, code switches, base case: Cb/*/Ld*.lean) with soundness statements. Nothing in
   Run/ or Fmt/ connects the two: these protocols and the building blocks.
   That Fmt/Rules8.lean renders the format page is not a theorem. It is supported by tests: the
   page's known answers and files from outside.
   The run functions over a single oracle are treated in Run/PageIsCoreOne.lean [not in this library]. The run functions
   that read whole Merkle paths (Run/PageIsFull.lean [not in this library]) and run functions behind the strict reader are
   not treated here.

Terms: lean/GLOSSARY.md.
-/
import Run.StrictDom

set_option autoImplicit false

namespace Run.PQ

/-- States that, within the limits (`ok S`) and on a file whose sizes pass `smallF`, where the roots
that the file sends differ, the run functions over typed oracle functions behind the lenient reader
give the verdict of the page's strict verifier. -/
def Spec.core_lax : Prop :=
  ∀ (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray),
    ok S = true → smallF S file = true → rootsDiffer _root_.Fmt.formatHash S file = true →
    decide (runLaxSP S dec file = .accepted) = _root_.Fmt.verify S (fun (_ : Unit) => dec) () file ∧
    decide (runLaxS S dec file = .accepted) = _root_.Fmt.verify S (fun (_ : Unit) => dec) () file

end Run.PQ
