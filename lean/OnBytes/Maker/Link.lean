-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Link.lean: the link, the protocol of an entry file, as an interactive oracle reduction
whose instance is the pair of the two stored tables' records. Definitions alone.

The verifier program checks an entry's chain by one block, `linkVerify` (OnBytes/Iop/Link.lean), at
two keys of tables (`TableKey`, OnBytes/Iop/Foldeq.lean). A key holds the number of the statement's
item with the table's root, and the table's record as the program writes it. Here the two keys are
written of the instance: `key` says how a record is written as a key, and the item's number is laid
here, 0 for the first table and 1 for the copy.

What the file contains.
  `linkBlock`: the block at the keys written of a pair of records.
  `linkData`: the library's form (`Run.PQ.XD`) of the description of an entry's chain with given
    rounds. Of it the reduction takes the rounds' data and the openings alone; the statement's bytes
    are left empty, and nothing here reads them.
  `iorLink`: the reduction. Its type is that of the field `link` of Hiop/RecSubs.lean's `SubsR` at a
    configuration with strings of length 2 ^ a over `SgX` and the record R. The tables' depth a is
    the caller's letter, so that the reductions of a key file, an entry file and a proof file can
    stand over strings of one length by their types.

What is owed by the caller. `r` must be the rounds that the dry run of `linkBlock key p rr` gives
from `Entry.start p`, for every rr: an `IOR` has one shape for all instances. a must be the depth
that the description gives the two tables, `(linkData p r).a`. C, the choice of the types of
verifier messages (Run/PlanQTypes.lean, `CK`), must be the one at which the program draws,
`ckP p.given.plan.field` (Run/PlanPull.lean): a `CK` may have one message for each round, and then
nothing is drawn. None of the three is asked here.

What is not claimed. No law is stated here.


-/
import OnBytes.Maker.Terminal
import OnBytes.Params.EntryRounds

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ

/-- The block of an entry's chain at the keys written of a pair of records. -/
def linkBlock {R : Type} (key : R → TableKey) (p : Params.Link) (rr : R × R) : Blk Unit :=
  linkVerify p.link { key rr.1 with item := 0 } { key rr.2 with item := 1 }

/-- The description of an entry's chain with the rounds r, in the library's form, without a
statement. -/
def linkData (p : Params.Link) (r : Params.Rounds) : XD :=
  Tie.xdOf (Params.entrySpecOf p r ByteArray.empty) fun _ _ => ByteArray.empty

/-- **The link as data**: the instance is the pair of records. -/
@[reducible] def iorLink {R : Type} (C : CK) (a : ℕ) (key : R → TableKey) (p : Params.Link)
    (r : Params.Rounds) : IOR (R × R) (twoExternalStrings (2 ^ a) SgX) Unit extNone :=
  iorBlkX C (linkData p r).ds a (linkData p r).xs (linkBlock key p) (Entry.start p)

end OnBytes.Maker
