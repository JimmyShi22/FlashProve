-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/TestNoSplit.lean: the test on the table where the folded row has Omega's code.

In the example parameter files the table's folded row and the message Omega stand under two codes,
so a row is split between two groups. If the two lines name one code, Omega joins the folded row's
group, no split is made, and one proximity test fewer is run. This file takes record.f2.txt of
blocks/frame/examples with the folded row's lines set to Omega's. The numbers that are expected were
taken from the prints of the C++ planning program (blocks/frame/cp_frame.cpp, `-plan request`) on
that file, with its stand-ins for the sub-proofs; no print gives the last number, the rounds of all
seven chains. Then the conditions of OnBytes/Params/Gate.lean are tried on such a shape: they hold,
and fail with one entry less. Each test is checked when the file compiles. The file is no part of
the program.
-/
import OnBytes.Params.Configure
import OnBytes.Plan.TestStandIn

namespace OnBytes.Params.TestNoSplit
open TestExamples TestStandIn

/-- Lines with some lines put in others' places, by their numbers from 0. -/
def change (l : List String) (c : List (Nat × String)) : List String :=
  c.foldl (fun l x => l.set x.1 x.2) l

/-- Lines with the folded row's lines set to Omega's, in a batch and in the committer's files. -/
def noSplit (l : List String) : List String :=
  let to := fun (i : Nat) (a b : String) => ((l.getD i "").replace a b)
  change l [(16, to 18 "group omega" "group folded"), (17, to 19 "stages omega" "stages folded"),
    (22, to 24 "group once-omega" "group once-folded"),
    (23, to 25 "stages once-omega" "stages once-folded")]

/-- The planning program's stand-ins, with one made-up range check. -/
def shapes : Shapes :=
  { sub := standIn, layout := ⟨List.replicate 25 []⟩, identifiers := List.range 25,
    ranges := Plan.TestStandIn.standIn, rangeChecks := [⟨64, 512, 128, 129, 2 ^ 22, (11, 12)⟩] }

/-- What `configure` makes of lines, with the lines as they were read. -/
def made (l : List String) : Option (Lines × Configured) :=
  (readLines (TestFile.fileOf l)).toOption.bind fun x =>
    (configure x.1 shapes Fmt.zero32 0).toOption.map fun c => (x.1, c)

/-- What the planning program prints: the folded row's test and a request's own test, in a batch
and in the committer's files; the columns of a batch; the batches that a stored copy bears; the
columns of the one-time test; the rounds of all seven chains together. Nothing if a split is
made. -/
def sizesOf (l : List String) : Option (List Printed × Nat × Nat × Nat × Nat) :=
  (made l).bind fun x =>
    let z := x.2.sized
    let b := z.proof.batch
    let k := z.key.once
    if b.shape.sharedSplitNeeded || k.shape.sharedSplitNeeded then none
    else some
      ([printed z.set b.folded.stages, printed z.set b.own.stages, printed z.set k.folded.stages,
        printed z.set k.own.stages],
       b.shape.fold.columns, b.batches, k.shape.fold.columns,
       ((x.2.proof ++ x.2.key ++ [x.2.entry]).map (·.rounds.length)).foldl (· + ·) 0)

#guard sizesOf (noSplit record) == some
  ([(159, [(262144, 3571, 64, 51, 237, 51),
      (16384, 51, 512, 51, 415, 51),
      (1024, 51, 256, 51, 711, 51),
      (1024, 41, 1024, 41, 681, 41)]),
    (159, [(262144, 3571, 256, 55, 237, 55),
      (16384, 55, 1024, 55, 415, 55),
      (2048, 55, 512, 55, 624, 55),
      (256, 46, 256, 46, 798, 46),
      (256, 44, 1024, 44, 785, 44)]),
    (158, [(262144, 98, 64, 49, 238, 49),
      (16384, 49, 64, 49, 415, 49),
      (1024, 49, 64, 49, 712, 49),
      (1024, 39, 512, 39, 787, 39)]),
    (158, [(262144, 98, 256, 49, 238, 49),
      (16384, 49, 128, 49, 415, 49),
      (2048, 49, 64, 49, 625, 49),
      (256, 41, 64, 41, 1002, 41),
      (256, 29, 256, 29, 981, 29)])],
   64, 688127, 62, 71464)

/-- One random entry less in a main code. -/
def lessMain (i : Nat) (c : Codes) : Codes :=
  { c with base := c.base.modify i fun x => { x with r := x.r - 1 } }

/-- One random entry less in a mask code. -/
def lessMask (i : Nat) (c : Codes) : Codes :=
  { c with mask := c.mask.modify i fun x => { x with r := x.r - 1 } }

/-- What the gate says of the test on the table in a batch: of its part on one test, under the codes
as they are, with one random entry less in the main code of the folded row's first stage, and with
one less in that stage's mask code; and of the leaves of the three prover's messages. -/
def gateSays : Option (Bool × Bool × Bool × Bool) :=
  (made (noSplit record)).bind fun x =>
    let b := x.2.sized.proof.batch
    match x.2.proof, b.shape.testU.head? with
    | [_, shared, second], some s =>
      let says := fun (f : Codes → Codes) => missedInOneTest x.1
        ⟨b, f x.2.sized.proof.codes, shared, second, standIn.pendingRows, 0⟩
      some (says id, says (lessMain s.code), says (lessMask s.maskCode),
        missedInTheTablesLeaves b.shape)
    | _, _ => none

-- The conditions hold. The first stage's main rows, Omega among them, are opened at the batch's
-- list and at every request's own: 51 + 64 * 55 = 3571 random entries, and not one less. Its mask
-- rows are opened at the batch's list alone: 51, and not one less.
#guard gateSays == some (false, true, true, false)

end OnBytes.Params.TestNoSplit
