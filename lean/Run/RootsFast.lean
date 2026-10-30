-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/RootsFast.lean: the test "the roots that the file sends are pairwise different" in a form that
can be evaluated at full parameters.

Run/PageIs.lean defines the test `rootsDiffer h S file`: the lenient reader is run on the file at
the hash function h, and the Merkle roots that it finds are compared as bytes. The statements that
give the compiled verifier and the format's strict verifier one verdict (`core_lax`,
Run/PageIsCore.lean; `core_one`, `core_tree`, Run/PageIsCoreOne.lean [not in this library]) require it at the format's
hash function `Fmt.formatHash`. Evaluated as it stands, that test is slow on the files at full parameters.
This file gives the same test on the fast form of the lenient reader (`laxWholeF`,
Run/ParseLaxFast.lean), so that it can be a test (#guard) at every file.

Sources. No text from outside enters. The reason for the test is rule R7.14 of the format page
(docs/format/FORMAT.md, which comes with the programs); the head of Run/PageIs.lean explains it.

1. What the file contains.
   `rootsDifferF S file`: its doc comment tells it.
   One statement (`Run.PQ.Spec.rootsF_eq`).

2. What is checked when the file compiles. Nothing beyond the types; there are no tests here.

3. Theorems. The statement is proved in Run/RootsFastProofs.lean.

4. What is not claimed.
   Nothing on time: that the fast form is fast is measured, not proved. (Measured once each, by
   Lean's evaluator, whole runs with loading. By the fast form: the list of 23 files of the first
   toy at full parameters, 22 s; the list of 22 files of the second toy at full parameters, 26 s. By
   the form of Run/PageIs.lean at Fmt.formatHash: one run over all lists together, tiny and full parameters
   of both toys and the entry file, was stopped at 1,200 s without an answer; the same run without
   the two lists at full parameters took 122 s.)
   S is a `Fmt.Spec`: the entry file's descriptions (`Fmt.SpecX`) are not covered.
   No statement on soundness follows.

Terms: lean/GLOSSARY.md.
-/
import Run.PageIs
import Run.ParseLaxFast

set_option autoImplicit false

namespace Run.PQ

/-- The roots that the file sends are pairwise different, by the fast lenient reader; true where
that reader does not read the file. -/
def rootsDifferF (S : _root_.Fmt.Spec) (file : ByteArray) : Bool :=
  match laxWholeF S file with
  | none => true
  | some o => decide ((rootsB o).map ByteArray.data).Nodup

/-- States: the fast form is the test of Run/PageIs.lean at the format's hash function. -/
def Spec.rootsF_eq : Prop :=
  ∀ (S : _root_.Fmt.Spec) (file : ByteArray), rootsDifferF S file = rootsDiffer _root_.Fmt.formatHash S file

end Run.PQ
