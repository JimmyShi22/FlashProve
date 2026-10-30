-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Key/Plan/Two.lean: the two tests on the plan of a key file's second chain, the shared
chain (not the field that the program calls `second`: see Johnson/Desc/Key/Where.lean): at the
rounds of the test on Omega's group and of the test on the folded row's group, and at the rounds in
front of each, the plan's entries say what the shape, the codes and the stages ask. Definitions with
code; two Bool tests; public data only: no view and no value of the field is read.

What is compared (`Want.meets`, Johnson/Desc/Key/Plan/Test.lean): names, bytes, roots, answers,
elements drawn, how many of them must not be 0, the range of the positions at every round that
draws positions, the rows at every round that batches. Where the rounds lie is found from the
plan's names (`whereOmega`, `whereFolded`, Johnson/Desc/Key/Where.lean).

Main names.
  `wantsOmegaHead`, `wantsFoldedHead`: four rounds each: from the seeds of the message with Omega
    to SPLIT; from LIN point to LOC.
  `rowsOmega`, `rowsFolded`, `wantsOmega`, `wantsFolded`: the rows that the two tests batch; the
    two tests' entries.
  `okOmega`, `okFolded`: the two tests on the plan.

Limits. Written for the shape that splits: the folded row and Omega differ in code, so that each has
a test of its own and the plan has SPLIT and two rounds BAT. Any other shape is refused by both
tests. A plan with any number of answers to a sample but one is refused, though the wants are
written for any number. Where `linWithU` returns nothing the message with the folded row counts as
the folded row alone: that is not refused here. An entry's bits of work are not read; the number of
positions is read at LOC alone, where it must be the shape's number of columns. The rounds between
the stretches, and the seal, are not asked. No theorem. Nothing on soundness.

-/
import Johnson.Desc.Key.Where
import Johnson.Desc.Key.Plan.Test

set_option autoImplicit false

namespace VerifiableInference.Desc.Key.Plan

open OnBytes OnBytes.Params

/-- The four rounds from the seeds of the message with Omega to SPLIT. -/
def wantsOmegaHead (P : SharedPub) : List Want :=
  let m := linMessageOmega P.S
  [wantSeed P.samples (treesSent P.codes m) (largestCube P.codes (m.toList.map (·.shape))),
   wantAnswer P.samples (m.toList.filter fun n => n.shape.answers != 0).length,
   { name := "LIN zeta", drawE := P.S.kRow },
   { name := "SPLIT", msg := 24 }]

/-- The four rounds from the shared point to LOC. -/
def wantsFoldedHead (P : SharedPub) : List Want :=
  let m : Array OracleNotice := #[⟨P.S.fold.u, P.S.fold.leafClass⟩] ++ (linWithU P.S).getD #[]
  [{ name := "LIN point", drawE := P.S.kCol },
   wantSeed P.samples (treesSent P.codes m) (largestCube P.codes (m.toList.map (·.shape))),
   wantAnswer P.samples (m.toList.filter fun n => n.shape.answers != 0).length,
   { name := "LOC", logN := some P.S.fold.index.code.logN }]

/-- The rows that the test on Omega's group batches: one open row, and the sample rows of Omega and
of the split's mask message. -/
def rowsOmega (P : SharedPub) : Nat := 1 + 2 * P.samples

/-- The rows that the test on the folded row's group batches: the sum that the planner forms
(`foldedRows`, OnBytes/Params/DeriveLin.lean): the answers of the table's own sample, one open row,
two messages' sample rows, and the columns that are drawn. -/
def rowsFolded (P : SharedPub) : Nat :=
  P.S.fold.index.answers + 1 + 2 * P.samples + P.S.fold.columns

/-- The entries of the test on Omega's group, from its batching round on. The written 1: the first
fold sends its own mask. -/
def wantsOmega (P : SharedPub) : List Want :=
  wantsTest P.codes P.samples P.S.testOmega (rowsOmega P) 1 P.S.choice.masksRide

/-- The entries of the test on the folded row's group, from its batching round on. -/
def wantsFolded (P : SharedPub) : List Want :=
  wantsTest P.codes P.samples P.S.testU (rowsFolded P) (if P.S.masksAhead then 0 else 1)
    P.S.choice.masksRide

/-- **The plan's side of the test on Omega's group.** One answer to a sample; the places are found;
the four rounds from the seeds of the message with Omega on, and the test's rounds from the second
BAT on, meet their wants. -/
def okOmega (P : SharedPub) : Bool :=
  P.samples == 1 &&
  match whereOmega P with
  | .error _ => false
  | .ok W => okFrom (wantsOmegaHead P) P.e W.seed && okFrom (wantsOmega P) P.e W.bat

/-- **The plan's side of the test on the folded row's group.** One answer to a sample; the places
are found; the four rounds from LIN point on, the four from the seeds of the message with Omega on,
and the test's rounds from the first BAT on meet their wants; LOC draws as many positions as the
shape has columns. -/
def okFolded (P : SharedPub) : Bool :=
  P.samples == 1 &&
  match whereFolded P with
  | .error _ => false
  | .ok W =>
    okFrom (wantsFoldedHead P) P.e W.point &&
    ((P.e[W.loc]?).map (·.poss)) == some P.S.fold.columns &&
    okFrom (wantsOmegaHead P) P.e W.seedO && okFrom (wantsFolded P) P.e W.bat

end VerifiableInference.Desc.Key.Plan
