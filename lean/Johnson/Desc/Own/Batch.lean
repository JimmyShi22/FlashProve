-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/Batch.lean: the batching of the rows on a group, as a named part of the
description.

In front of a proximity test the verifier draws one element x and replaces the rows on a group of
oracle messages, in their fixed order, by one row: the sum of x^i times row number i (from 0). A row
speaks of the members' own tables; the one row speaks of the group's tables. So each coefficient is
carried from its member's table to the group's: a member's rows stand in a block of the group's main
table (and its mask rows in a block of the group's mask table) that begins at the row which the
layout names; a kept member's main rows stand in no block, and the coefficients on them are kept as
a form on that member's own main table.

  `entryInto`: acc plus x times one coefficient on one entry of a member's table.
  `termInto`: acc plus x times a vector of product form on a member's table.
  `runInto`: acc plus x times a run of coefficients, entry by entry.
  `formInto`: acc plus x times a whole form on a member's main table.
  `rowInto`: acc plus x times a row: its terms, single entries, runs and forms, and its target.
  `batch`: the sum of x^i times row number i. The rows' written-out runs and single entries are
    added up first and carried to the group's tables once.

WHERE IT RETURNS NOTHING, AND WHAT EACH REFUSAL CHECKS. A mark [n] behind a line numbers the case:
twelve lines, five cases. All hang on what a row names and on the layout: numbers and sizes alone;
none reads a coefficient, a target or x. `runInto`, `rowInto` and `batch` hand a "nothing" on and
add none.
  [1] the oracle message that a summand names is no member of the layout
  [2] the member has no block of mask rows, and the summand is on its mask table
  [3] the entry, carried to the group, lies beyond the group's mask table (whose length
      GroupRow.ready sets from the layout's numbers)
  [4] the member is not kept and has no block of main rows, and the summand is on its main table
  [5] the member's table has more row bits than the group's
NOT BOUNDED HERE: an index on a main table: whoever lays an open row bounds it, and the sampling
makes the sample rows.

HOW FAR THE TEXT IS ITS OWN. It is the program `verify-on-bytes`'s Bat.combine
(OnBytes/Iop/Bat.lean) with addEntryTo, addTermTo, addRunTo, addFormTo and addToGroupRow
(OnBytes/Iop/Ground.lean) taken over line for line under new names; GroupLayout.find is written as
members.idxOf?. IT ADDS NO SECOND, INDEPENDENT EYE ON WHAT THE BATCHING SHOULD DO. It is a drop-in
at the same arguments. That it, and each of its five steps, returns the same at all arguments is
proved in BatchAgree.lean, beside this file, which no block's text imports.

Of that verifier this file names records and functions that always return: the field's mulE and
maddE; Statement.rowBits; groupIndex; onKept; GroupRow.ready; Tensor.scale, insertChoice, addTo;
Form.add, addEntry, addForm, insertChoice; Coeffs.get; Row.addScaled. By a walk by constants beneath
`batch`, three definitions of that verifier's files return a yes or no: the equality of two
elements; isZeroE (inside Tensor.addTo: a factor 0 is passed over, which saves work and changes no
result); Run.liesAs (inside Row.addScaled: a run on the same entries as an earlier one is added into
that one). NO REFUSAL HANGS ON ANY OF THE THREE: each steers how a sum is laid, inside a function
that always returns. The walk counts by the result type as written, in modules under OnBytes and Fmt
alone.

Definitions with code; no theorem. Nothing on soundness, on an honest prover or on hiding.

-/
import OnBytes.Iop.Bat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own
open OnBytes

/-- acc plus x times coeff on one entry of a member's table, carried to the group's tables. -/
def entryInto (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow) (o : Nat) (part : Part)
    (index : Nat) (coeff : E) : Option GroupRow :=
  match L.members.idxOf? o with
  | none => none                                                                         -- [1]
  | some i =>
    let a := S.rowBits o part
    match part with
    | .mask =>
      match L.maskFirst.getD i none with
      | none => none                                                                     -- [2]
      | some first =>
        let j := groupIndex index a first L.h
        if j < acc.d.size then some { acc with d := acc.d.modify j fun y => maddE y x coeff }
        else none                                                                        -- [3]
    | .main =>
      if L.kept.getD i false then
        some { acc with kept := onKept acc.kept o fun f => f.addEntry index (mulE x coeff) }
      else
        match L.mainFirst.getD i none with
        | none => none                                                                   -- [4]
        | some first =>
          some { acc with c := acc.c.addEntry (groupIndex index a first L.k) (mulE x coeff) }

/-- acc plus x times a vector of product form on a member's table. -/
def termInto (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow) (t : Term) :
    Option GroupRow :=
  match L.members.idxOf? t.oracle with
  | none => none                                                                         -- [1]
  | some i =>
    let v := t.v.scale x
    let a := S.rowBits t.oracle t.part
    match t.part with
    | .main =>
      if L.kept.getD i false then
        some { acc with kept := onKept acc.kept t.oracle fun f => f.add v }
      else
        match L.mainFirst.getD i none with
        | none => none                                                                   -- [4]
        | some first =>
          if L.k < a then none                                                           -- [5]
          else some { acc with c := acc.c.add (v.insertChoice a (L.k - a) (first / 2 ^ a)) }
    | .mask =>
      match L.maskFirst.getD i none with
      | none => none                                                                     -- [2]
      | some first =>
        if L.h < a then none                                                             -- [5]
        else some { acc with d := (v.insertChoice a (L.h - a) (first / 2 ^ a)).addTo acc.d }

/-- acc plus x times a run of coefficients, entry by entry. -/
def runInto (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow) (w : Run) :
    Option GroupRow :=
  (List.range w.coeffs.size).foldlM (fun acc j =>
    entryInto S L x acc w.oracle w.part (w.first + w.step * j) (w.coeffs.get j)) acc

/-- acc plus x times a whole form on a member's main table. -/
def formInto (S : Statement) (L : GroupLayout) (x : E) (acc : GroupRow) (f : MainForm) :
    Option GroupRow :=
  match L.members.idxOf? f.oracle with
  | none => none                                                                         -- [1]
  | some i =>
    if L.kept.getD i false then
      some { acc with kept := onKept acc.kept f.oracle fun c => c.addForm f.c x }
    else
      let a := S.rowBits f.oracle .main
      match L.mainFirst.getD i none with
      | none => none                                                                     -- [4]
      | some first =>
        if L.k < a then none                                                             -- [5]
        else some { acc with c := acc.c.addForm (f.c.insertChoice a (L.k - a) (first / 2 ^ a)) x }

/-- acc plus x times the row, with every coefficient carried from its member's table to the group's
tables. Nothing if the row names an oracle message or a table that the layout does not have, or if
an entry is beyond the group's mask table. An index on a main table is not bounded here. -/
def rowInto (S : Statement) (L : GroupLayout) (row : Row) (x : E) (acc : GroupRow) :
    Option GroupRow := do
  let acc1 ← row.terms.foldlM (termInto S L x) (acc.ready L)
  let acc2 ← row.units.foldlM (fun acc u =>
    entryInto S L x acc u.oracle u.part u.index u.coeff) acc1
  let acc3 ← row.runs.foldlM (runInto S L x) acc2
  let acc4 ← row.forms.foldlM (formInto S L x) acc3
  pure { acc4 with target := maddE acc4.target x row.target }

/-- **The batching**: the sum of x^i times row number i, as a row on the group g. -/
def batch (S : Statement) (g : Nat) (input : RunInput) (x : E) : Option GroupRow := do
  let start : GroupRow × Row × E := ({ group := g }, {}, oneE)
  let s ← input.rows.foldlM (fun (s : GroupRow × Row × E) r => do
    let structured : Row := { r with units := #[], runs := #[] }
    let acc ← rowInto S input.layout structured s.2.2 s.1
    let written : Row := { units := r.units, runs := r.runs }
    pure (acc, s.2.1.addScaled written s.2.2, mulE s.2.2 x)) start
  rowInto S input.layout s.2.1 oneE s.1

end VerifiableInference.Desc.Own
