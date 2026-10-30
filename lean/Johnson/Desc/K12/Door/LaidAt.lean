-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Door/LaidAt.lean: **THE PLAN's LISTS LAID AT THE RECORD's OWN CODES.** One
definition with code; no Mathlib.
`laidOfChain c` (Johnson/Desc/K12/Door/DoorBools.lean) lays the planner's sendings at the planner's
own codes (c.codes). A record of the first chain bears the codes of the chain's start. Under the
four premises of `codes_one_in_scope` (Johnson/Second/Seam/CodesOneInScope.lean), `madePinnedAt`
among them, the two are one; else it is no theorem (the start's are read back from the planner's
bytes; the round trip of the codes' spelling is proved nowhere). So the lists are laid at any codes:
  `laidAtCodes codes c`: the same sendings, in the same order, laid at codes.
  `laidOfChain_is`: at c.codes it is `laidOfChain c`.
  `sameLaidB codes c`: A TEST WITH CODE, for a walk: the two give one pair of lists.
MEANT: L := `laidAtCodes` at the start's codes: then "the record's codes are those at which L was
laid" asks no equation between two makers.
NOTHING HERE HAS RUN.

-/
import Johnson.Desc.K12.Door.DoorBools

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Door
open OnBytes OnBytes.Params

/-- The planner's sendings, in the order of their entries, laid at the codes named. -/
def laidAtCodes (codes : Codes) (c : Johnson.G.ChainSends) : Option Laid :=
  laidOf codes ((c.sends.mergeSort fun a b => a.entry ≤ b.entry).map (·.sent))

theorem laidOfChain_is (c : Johnson.G.ChainSends) : laidOfChain c = laidAtCodes c.codes c := rfl

/-- The two give one pair of lists. -/
def sameLaidB (codes : Codes) (c : Johnson.G.ChainSends) : Bool :=
  match laidAtCodes codes c, laidOfChain c with
  | some A, some B => A.places == B.places && A.shapes == B.shapes
  | _, _ => false

end VerifiableInference.Desc.K12.Door
