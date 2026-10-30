-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/SmpRows.lean: THE SAMPLE OF A TENANT, OFF THE CHAIN's OWN RECORD. Definitions, with
code. It imports OnBytes/Iop/Send.lean: for the plain records (`Statement`, `Oracle`, `Row`,
`TreeBook`, `SampleSeed`) and, in `seedOf` alone, for two plain functions of a shape (`Send.cube`,
`Send.pad`). NOTHING IS PROVED IN THIS FILE.

Why. A committed word is near a list of code words; what names one member of the list is the
tenant's out-of-domain sample (Johnson/Desc/Msg.lean: `PIN`, `NoColl`;
Johnson/Desc/Sound/MsgSig.lean: `PinAt`, `CfAt`). There the sample is a letter (`smp`). Here it is
named: the first chain's carried record holds the session's statement and the book of trees; the
statement holds, for each oracle message, its sample rows, one for each answer, from the moment the
answers have been received; the book says which oracle message is which tenant of which tree.
  `oracleNo book j t`: the number, in the session's statement, of the oracle message that is tenant
    t of tree j.
  `smpRows st book j t`: **the sample of tenant t of tree j, as the record holds it**: its rows.
    Nothing where the book has no such tenant, the oracle message is not marked as sampled, its
    shape has no answer, or the rows are not as many as the answers.
  `seedOf codes s r`, `smpSeed`: CODE FOR A RUN, NO NOTION IN ANY STATEMENT: the seed (point and
    factor) read back off the kept row of answer 0, by the text of `Send.form`. NO LAW LEANS ON IT.
    That it gives back the seed of which the row was made is shown by nobody: a run can hold its
    value against the seed that the view's round of seeds drew.
  `smpHeld`: the record holds the sample, and a seed can be read back: a test that a run can
    evaluate at every boundary.
So `Reading.smp` (Msg.lean) is meant as `fun a j t => smpRows a.st a.book j t`, at Smp := the rows.
Limits. A TREE's NUMBER IN THE BOOK is its place among the trees that the session has sent: in the
first chain that is MEANT to be its number through the file (both count the trees from 0 in the
order of sending): NOT SHOWN, by reading or by a run; of the other two chains nothing is said here.
A row holds the coefficients that were made of the seed, and the answer as its target: THE SEED
ITSELF IS NO FIELD OF THESE RECORDS (by the structures' texts). In the statements the seed stands
under a "there is", tied to the record by the rows (`SeedIs`, Johnson/Desc/Sound/Seed.lean);
`seedOf` serves a run alone. That the block which hears the answers lays just these rows is that
block's matter.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Iop.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-- The number, in the session's statement, of the oracle message that is tenant t of tree j. -/
def oracleNo (book : OnBytes.TreeBook) (j t : Nat) : Option Nat :=
  (List.range book.place.size).find? fun o => book.place[o]? == some (j, t)

/-- **The sample of tenant t of tree j, as the record holds it**: its rows, one for each answer. -/
def smpRows (st : OnBytes.Statement) (book : OnBytes.TreeBook) (j t : Nat) :
    Option (Array OnBytes.Row) :=
  (oracleNo book j t).bind fun o => (st.oracles[o]?).bind fun x =>
    if x.sampled && decide (0 < x.shape.answers) && x.sampleRows.size == x.shape.answers then
      some x.sampleRows
    else none

/-- CODE FOR A RUN, NO NOTION IN ANY STATEMENT: the seed read back off a kept sample row (the row of
answer 0) and the shape, by the text of `OnBytes.Send.form`: the row's terms are the equality
tensors of the point's low coordinates on the main and on the mask table: each coordinate is the
second half of a pair; with both tables the point's top coordinate stands in the larger table's
scalar (1 - top on the main table, top on the mask table); the factor is the first pad place's unit
plus that tensor's entry there (the basis at that place is 1). -/
def seedOf (codes : OnBytes.Codes) (s : OnBytes.OracleShape) (r : OnBytes.Row) :
    Option OnBytes.SampleSeed := do
  let c := OnBytes.Send.cube codes s
  let places ← OnBytes.Send.pad codes s
  let onMain := r.terms.toList.find? fun x => x.part == .main
  let onMask := r.terms.toList.find? fun x => x.part == .mask
  let z ←
    if c.hasMain && c.hasMask then
      if c.maskBits ≤ c.mainBits then
        onMain.map fun x => x.v.pairs.map (·.2) ++ [OnBytes.subE OnBytes.oneE x.v.scalar]
      else onMask.map fun x => x.v.pairs.map (·.2) ++ [x.v.scalar]
    else if c.hasMain then onMain.map fun x => x.v.pairs.map (·.2)
    else onMask.map fun x => x.v.pairs.map (·.2)
  let p ← places.head?
  let u ← r.units[0]?
  let x ← if p.part == .main then onMain else onMask
  pure ⟨z, OnBytes.addE u.coeff (x.v.entry p.index)⟩

/-- The seed and the answers of tenant t of tree j, as a run reads them off the record. -/
def smpSeed (st : OnBytes.Statement) (book : OnBytes.TreeBook) (j t : Nat) :
    Option (OnBytes.SampleSeed × List OnBytes.E) :=
  (oracleNo book j t).bind fun o => (st.oracles[o]?).bind fun x =>
    (smpRows st book j t).bind fun rows => (rows[0]?).bind fun r =>
      (seedOf st.codes x.shape r).map fun sd => (sd, rows.toList.map (·.target))

/-- The record holds the sample: its rows lie there, and a seed can be read back off the first. -/
def smpHeld (st : OnBytes.Statement) (book : OnBytes.TreeBook) (j t : Nat) : Bool :=
  (smpSeed st book j t).isSome

end VerifiableInference.Desc
