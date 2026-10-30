-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2Close.lean: the second toy (a chain of three links): what a closing batches, written as the
text lists it: every open row of the group, on the group's own tables, in the text's order, then
their sum under the powers of the batching element.

Definitions that compute. Core Lean; every function is total; generic in the sizes, in the blocks
and in the function that makes a draw's rows (`DrawL`). Fmt/M2Dec.lean says what the second toy is
and defines its verifier's decision. A group consists of the oracle messages that are tested
together, its members (`memsOf`, Fmt/M2Types.lean). A row on a group (`KRow`) is a linear claim:
vectors of coefficients, called forms, on the group's tables and on a kept member's table, with a
target value. At the closing of a group the verifier draws one element theta and sums all open rows
of the group under its powers. A draw is a position that the verifier has drawn and at which the
former group's tree is opened. The head of Fmt/M2Loc.lean says what the switch between two links,
the carrying message and the kept message sent anew are.
The order and the number of the rows are those of the programs' description of the toy in its second
issue (its part on the frame, 5 (a)): 9 + 4 t rows at a closing behind a link with a kept message.

Main names:
  `rowsLit`: (their part on the frame, 5 (a)) the rows of group m, numbered from 0. If something
    waits from the former link (in the decision: m > 1): the claim carried over; the old sample row
    of the former link's kept message, if it has one. Then the rows `plain`, in the decision the
    link's three rows (none at the last group) and the sample rows, member by member in the order of
    joining. Then for each draw of the list, in the order drawn, repeats counted, the rows that `dl`
    makes; at `drawL` (Fmt/M2Loc.lean): main, kept row (if the former group has one), old mask,
    fresh mask. Each laid on the group's tables. None if a drawn position has no column.
  `batchLit`: their sum under 1, theta, theta^2, ..
  `agrees`: `batch` and `batchLit` give the same row, entries beyond an array's end counting as 0
    (`sameK`), or both none: a test, to be evaluated at given data.
  `decLit`: the whole decision with `batchLit` in the place of `batch`.

Why: `batch` (Fmt/M2Dec.lean), which the decision runs, does not write the rows out: it batches them
member by member, takes the draws' rows as one sum from a block of its own, and lays the result into
the group's table once. At the programs' full parameters (`toyPar`) group 3's closing has 301 rows
on a table of 32,768 entries. This file has the meaning of `batch`, every row written out, for
readers; it can be evaluated at small sizes (`agrees`), but no test in Fmt/ or Run/ does so.

Limits: this file does not say that these rows are what the programs (the C++ implementation that
comes with this Lean code) batch: no theorem says so; the tests on the programs' own files
(Fmt/M2EngineLT.lean, Fmt/M2EngineLR.lean, Fmt/M2EngineLF.lean) compare verdicts and 34 intermediate
values.

That `batch` = `batchLit`, at the blocks of Fmt/M2All.lean, the draws' rows of Fmt/M2Loc.lean
(`drawL`) and under conditions on sizes, is proved in Fmt/M2BatchEq.lean. That the two decisions, at
the same blocks and draws' rows, are one function, for all sizes and views, no condition:
Fmt/M2DecEq.lean.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M2Dec

namespace Fmt.M2
open Fmt.M1

/-- The type of a function that makes the rows of one draw; at `drawL` (Fmt/M2Loc.lean): main, kept
row (if there is one), old mask, fresh mask. -/
abbrev DrawL : Type := Fld → Code → Code → Bool → KSRow → Nat → KCol → List LRow

/-- All draws' rows, in the order drawn; none if a drawn position has no column. -/
def drawsLit (dl : DrawL) (P : Par) (kept : Bool) (S : KSRow) (col : Nat → Option KCol) :
    List Nat → Option (List LRow)
  | [] => some []
  | x :: xs =>
    match col x, drawsLit dl P kept S col xs with
    | some c, some rest => some (dl P.fld P.C P.Z kept S x c ++ rest)
    | _, _ => none

/-- The rows of group m, in the order of batching. -/
def rowsLit (B : Blocks) (dl : DrawL) (P : Par) (V : M1.View) (m : Nat)
    (wait : Option Wait) (plain : List MRow) : Option (List KRow) :=
  let ms := memsOf P.links m
  let up : MRow → KRow := toK ms P.C.l P.Z.l
  match wait with
  | none => some (plain.map up)
  | some w =>
    let kept := decide (m - 1 < P.links)
    (drawsLit dl P kept w.S
        (fun x => (colAt V (m - 2) x).bind (groupCol (memsOf P.links (m - 1)) 1))
        w.xs).map fun ds =>
      (frontRows B P kept w).map (fun R => up (R.toM ms.length)) ++
        (plain.map up ++ ds.map fun R => up (R.toM ms.length))

/-- The sum of the rows of `rowsLit` under the powers of theta. -/
def batchLit (B : Blocks) (dl : DrawL) (P : Par) (V : M1.View) (m : Nat) (wait : Option Wait)
    (plain : List MRow) (theta : E) : Option KRow :=
  (rowsLit B dl P V m wait plain).map (sumK P.fld theta)

/-- Two arrays have the same entries, those beyond an end counting as 0. -/
def sameV (u v : Array E) : Bool := padL v.size u.toList == padL u.size v.toList

def sameK (a b : KRow) : Bool := sameV a.c b.c && sameV a.kp b.kp && sameV a.d b.d && a.t == b.t

/-- A test: at these data `batch` and `batchLit` give the same row (by `sameK`), or both none. -/
def agrees (B : Blocks) (dl : DrawL) (P : Par) (V : M1.View) (m : Nat) (wait : Option Wait)
    (plain : List MRow) (theta : E) : Bool :=
  match batch B P V m wait plain theta, batchLit B dl P V m wait plain theta with
  | some a, some b => sameK a b
  | none, none => true
  | _, _ => false

/-- The decision with every row written out. -/
def decLit (B : Blocks) (dl : DrawL) (P : Par) (V : M1.View) : Bool :=
  decBy B P V (batchLit B dl P V)

#guard sameV #[(1, 0, 0)] #[(1, 0, 0), (0, 0, 0)] && !sameV #[(1, 0, 0)] #[(1, 0, 0), (2, 0, 0)]

end Fmt.M2
