-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/LinkRecord.lean: the link as data (OnBytes/Maker/LinkValue.lean, `linkValue`) at
records over the field. Definitions alone; the laws are in OnBytes/Maker/LinkRecordLaws.lean.

A record over the field is a pair: for each of s answers a point of lg coordinates and a factor
other than 0; and the answers of each of the 2 ^ v rows (`RecP`, OnBytes/Slice/KeyOfRec.lean). The
first part is the record's seed. `keyOf` of that file writes such a pair as the program's key of a
table.

What the file contains.
  `Fac`: the factors, the elements of the field other than 0.
  `RecF v lg s`: the records with such factors. It is a product: seeds, then answers.
  `keyRec`: `keyOf` at these factors.
  `linkValueRec`: `linkValue` at these records and that way of writing a key.
  `RecAt p`, `linkValueAt`: the same at the three numbers of the tables' shape in the parameter
    bytes, at the depth `linkDepth p`, with hash blocks at the plan's field as the verifier's
    messages (`ckP`).

What is not claimed. No law is stated here.


-/
import OnBytes.Maker.LinkValue
import OnBytes.Slice.KeyOfRec

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ OnBytes.Slice

/-- The factors: the elements of the field other than 0. -/
abbrev Fac : Type := { β : GE // β ≠ 0 }

/-- The records over the field: seeds, then answers. -/
abbrev RecF (v lg s : ℕ) : Type := RecP Fac v lg s

/-- A record written as the program's key of a table, with the item 0. -/
def keyRec {v lg s : ℕ} (rec : RecF v lg s) : TableKey := keyOf (fun β : Fac => β.val) rec

/-- **The link as data at records over the field.** -/
@[reducible] def linkValueRec (C : CK) (a v lg s : ℕ) (p : Params.Link) :
    IOR (RecF v lg s × RecF v lg s) (twoExternalStrings (2 ^ a) SgX) Unit extNone :=
  linkValue C a keyRec p

/-- The records at the three numbers of the tables' shape. -/
abbrev RecAt (p : Params.Link) : Type :=
  RecF p.link.table.v p.link.table.cubeBits p.link.table.answers

/-- **The link as data, all from the parameter bytes**: the verifier's messages are hash blocks at
the plan's field. -/
@[reducible] def linkValueAt (p : Params.Link) :
    IOR (RecAt p × RecAt p) (twoExternalStrings (2 ^ linkDepth p) SgX) Unit extNone :=
  linkValueRec (ckP p.given.plan.field) (linkDepth p) _ _ _ p

end OnBytes.Maker
