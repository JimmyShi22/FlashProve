-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/KeyOneTime.lean: the parameter bytes of a key file's first chain, from the public
files.

A key file's first chain holds: the sending of the index-mask message (an oracle message of mask
rows only); the proof that the entries of the committed matrix are in their ranges, with the joining
of the rows that it leaves on the table (such a pending row is a linear claim on the matrix that the
test on the table has still to settle); the first part of the test on the table; and the seal. Where
tables have a record, the chain's plan begins with the entry RECORD, which is no round
(docs/format/09-key-and-leaf-files.md, R13.15). This file sizes these blocks in the order in
which the C++ routines size them, plans their rounds, and spells the chain's parameter bytes: the
plan, the digest of the public files, and five items. So a verifier derives this chain's parameter
bytes itself and need not be handed them.

The order matters for the numbers of the codes: the list of the key's codes gets those of the test
on the table first, then those of the proof of the ranges.

Main definitions: KeySized, keySized, keyOk, oneTimeRounds, oneTimePlan, oneTimeItems,
oneTimeParams.
C++ counterpart: the key's part of sized() and file_key() in blocks/frame/files.h; key_fixed() in
blocks/frame/key_fixed.h; bind_one_time_chain() in blocks/frame/check_key.h.

Not claimed here: no theorem is stated.
-/
import OnBytes.Plan.Ranges
import OnBytes.Key.Fixed

namespace OnBytes.Plan

open OnBytes.Params

/-- What follows from the public files for a key's chains. -/
structure KeySized where
  /-- the setting -/
  set : Setting
  /-- the test on the table, as the committer's one-time test -/
  once : LinSized
  /-- the proof of the ranges -/
  ranges : RangesSized
  /-- the codes of the key's chains, under their numbers -/
  codes : Codes

/-- Sizes a key's blocks. shape: what the proof of the ranges looks up; its number of columns is
taken from the lines. No line says how many mask rows the index-mask message has: the number follows
from the entries that are taken of it (Wf.indexMaskEntries). That number depends only on the lookups
and their parts in its first argument, so the other fields of what it is handed here do not
matter. -/
def keySized (l : Lines) (shape : Shape) : Option KeySized := do
  let s := settingOf l
  let T ← deriveTable s l
  let L ← rangesLines { shape with kCol := l.blockLog } l.onceRanges l.rangesPart
  let count : WfPublic :=
    { lookups := L.lookups, message := default, messageId := L.messageId, stages := [],
      choice := ⟨true⟩ }
  let inputMaskRows := Send.maskRowsFor (Wf.indexMaskEntries count ⟨L.kCol, L.matrixRows⟩)
    (2 ^ l.onceOwn.maskLogL) l.answers
  if inputMaskRows == 0 then none
  let (once, codes) ← linSized s (linLines l L.matrixRows inputMaskRows true) T {}
  let (ranges, codes) ← rangesSized s L codes
  pure ⟨s, once, ranges, codes⟩

/-- The shape of a key's binding tree: one leaf, with the setting's bytes of salt. -/
def KeySized.binding (z : KeySized) : LinBindingShape := ⟨0, z.set.saltBytes⟩

/-- What only several of a key's values together can show. The conditions are in Key.fixedOk, which
the check of a key file asks too. -/
def keyOk (z : KeySized) : Bool :=
  Key.fixedOk z.codes z.once.shape z.once.input z.ranges.x z.binding

/-- The entries of the plan of a key's first chain, as a routine that plans: the entry for the
table's record, and then the rounds. -/
def oneTimeRounds (z : KeySized) : Planning Unit := do
  planRecord z.once.table
  planSend [⟨cubeBitsOf z.codes z.once.input.shape, [z.once.own.first]⟩] 1
  rangesPlan z.codes z.ranges
  linPlanFirst z.codes z.once
  planSeal

/-- The plan of a key's first chain. It is refused when a block refuses, and when its own
verdict (Planned.holds, OnBytes/Params/Planner.lean) is no; that verdict asks, besides other things,
that each round's error be within the target once that round's bits of work are credited. -/
def oneTimePlan (z : KeySized) : Except String Planned :=
  finishHeld z.set .once (oneTimeRounds z)

/-- The items of the parameter bytes of a key's first chain that come after the digest of the public
files. -/
def oneTimeItems (z : KeySized) : List (String × ByteArray) :=
  [("index-mask message", spellNotice z.once.input), ("ranges", spellRanges z.ranges.x),
   ("binding tree", spellBinding z.binding), ("codes", spellCodes z.codes),
   ("the test on the table", spellLin z.once.shape)]

/-- The parameter bytes of a key's first chain, from the lines of the parameter file, the digest of
the public files and what the proof of the ranges looks up. Refused if no admissible numbers follow,
or if a round of the plan does not hold at the target, its proof of work counted. -/
def oneTimeParams (l : Lines) (cfg : ByteArray) (shape : Shape) : Except String ByteArray := do
  let z ← orRefuse (keySized l shape)
  if !keyOk z then throw notAdmitted
  let p ← oneTimePlan z
  pure (Fmt.paramsBytes p.plan cfg (oneTimeItems z))

end OnBytes.Plan
