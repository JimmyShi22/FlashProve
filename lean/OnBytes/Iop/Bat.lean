-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Iop/Bat.lean: the block BAT: many rows into one, by a random combination.
C++ counterpart: blocks/iop/bat.h (bat_verify, bat_sigma_verify, Bat::combine).

The prover sends nothing. The verifier sends one element x of the extension field. Row number i is
multiplied by x^i and the rows are added up, coefficients and targets alike. The block makes no test
on a value. It comes in two forms.
 - BAT, the first step of a proximity test on a group (the oracle messages that one test reads
   together). All open rows of the group, and the sample rows of all its oracle messages (one row
   for each answer to a message's out-of-domain sample), become one row on the group's tables. The
   test that follows is designed to show only that some code word near the group's word satisfies
   that row. The sample rows in it are what is meant to tie that code word to the messages that the
   samples fix. So a caller cannot choose them: batVerify takes all rows from the statement
   (Blk.beginRun), in a fixed order. Round: "BAT".
 - BAT-sigma: rows on any sampled oracle messages become one row on these messages, before any
   proximity test on them begins. Round: "BAT-sigma". No protocol of this program calls
   batSigmaVerify. Other blocks close their own rounds of that name (OnBytes/Iop/Batt.lean).
In both forms the number of rows must be the number that the plan's entry counts; the run on a view
tests that.

Order. Every row, its target included, must be fixed before x is drawn. batVerify closes the group
first, so that nothing is added to it afterwards. That a target follows from the statement, from
what was sent and from earlier challenges is the duty of whoever makes the row. One exception, by
design: inside a proximity test x comes in one verifier's message with the positions, so the rows
that a change of code makes from the opened positions are added after x is drawn; they are fixed by
the roots and the positions. Such a caller (csVerify, OnBytes/Iop/Cs.lean) draws x itself and calls
Bat.combine.

Main definitions: Bat.combine, Bat.combineRows, batVerify, batSigmaVerify. Laws on Bat.combine and
Bat.combineRows: OnBytes/Iop/RowLaws.lean and MaskLaws.lean.

Not claimed here: soundness or hiding.
-/
import OnBytes.Iop.Ground

namespace OnBytes

namespace Bat

/-- The sum of x^i times row number i, as a row on the group g. For batVerify, and for a caller that
has drawn x itself (csVerify). input is meant to come from Blk.beginRun: nothing here tests that it
holds the sample rows. The rows' written-out runs and single entries are added up first and carried
to the group's tables once. Nothing if a row names what the layout does not have. -/
def combine (S : Statement) (g : Nat) (input : RunInput) (x : E) : Option GroupRow := do
  let start : GroupRow × Row × E := ({ group := g }, {}, oneE)
  let s ← input.rows.foldlM (fun (s : GroupRow × Row × E) r => do
    let structured : Row := { r with units := #[], runs := #[] }
    let acc ← addToGroupRow S input.layout structured s.2.2 s.1
    let written : Row := { units := r.units, runs := r.runs }
    pure (acc, s.2.1.addScaled written s.2.2, mulE s.2.2 x)) start
  addToGroupRow S input.layout s.2.1 oneE s.1

/-- The sum of x^i times row number i, for rows that stay rows on oracle messages. -/
def combineRows (rows : Array Row) (x : E) : Row :=
  (rows.foldl (fun (s : Row × E) r => (s.1.addScaled r s.2, mulE s.2 x)) ({}, oneE)).1

end Bat

/-- BAT on group g: closes the group, draws x and batches. Returns the row on the group and the
group's layout. -/
def batVerify (g : Nat) : Blk (GroupRow × GroupLayout) := do
  let input ← Blk.beginRun g
  let x ← Blk.closeOne "BAT"
  Blk.requireRows input.rows.size
  let S ← Blk.statement
  let row ← Blk.getOnView { group := g } fun _ => Bat.combine S g input x
  pure (row, input.layout)

/-- BAT-sigma: batches rows on sampled oracle messages into one such row. Fails if a row names a
message that is not sampled. On a view it also fails if there is no row, if the number of rows is
not the one that the plan's entry counts, or if a sample row is among them: a sample row stays with
its oracle message until a proximity test takes it. -/
def batSigmaVerify (rows : Array Row) : Blk Row := do
  Blk.testOnView fun _ => !rows.isEmpty && rows.all (·.kind != .sample)
  rows.forM Blk.requireSampled
  let x ← Blk.closeOne "BAT-sigma"
  Blk.requireRows rows.size
  Blk.onView {} fun _ => Bat.combineRows rows x

end OnBytes
