-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/K10Border.lean: AT WHICH NUMBER OF THE CONSTANT's LIST OF PLACES THE CLOSING KIND's
OWN
SUB-PROTOCOL OF A LINK STANDS: closed facts, by the kernel.

What is said. At.ps: the constant's list of places; batchAt fullLinks At.ps m: the table's number of
link m's batching.
  `k10_border`: at every m < 24: batchAt fullLinks At.ps m + 3 = 14 m + 12: THE NUMBER AT WHICH
    the theorems on the group's members, and ShapesReached.lean's on ShapesAre, stand.
  `k10_border_head`: at m = 24: 350.
  `k10_kind_at`: at every m < 25 the place at batchAt .. m + 3 is of the kind K10 and of link m.
  `k10_kind_off`: THE NEGATIVE LINE: one number further (+ 4) no such place is of that kind.

Limits. Closed facts on the written list. Nothing on soundness.

-/
import Johnson.LPFK9R.SitsAtConstant

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFK9
open VerifiableInference.Desc (KindName)
open VerifiableInference.Desc.LinkJoin (batchAt)
open P5J (fullLinks)

set_option maxRecDepth 1000000 in
/-- The closing kind's own sub-protocol's number, at the links but the head's. -/
theorem k10_border : ∀ m < 24, batchAt fullLinks P5J.At.ps m + 3 = 14 * m + 12 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At the head's link. -/
theorem k10_border_head : batchAt fullLinks P5J.At.ps 24 + 3 = 350 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- There stands a place of the kind K10, of link m. -/
theorem k10_kind_at : (List.range 25).all (fun m =>
    (P5J.At.ps[batchAt fullLinks P5J.At.ps m + 3]?).any fun p =>
      p.kind == KindName.K10 && p.link == some m) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative line: one number further none is of that kind. -/
theorem k10_kind_off : (List.range 25).any (fun m =>
    (P5J.At.ps[batchAt fullLinks P5J.At.ps m + 4]?).any fun p =>
      p.kind == KindName.K10) = false := by decide +kernel

end LPFK9

#print axioms LPFK9.k10_border
#print axioms LPFK9.k10_border_head
#print axioms LPFK9.k10_kind_at
#print axioms LPFK9.k10_kind_off
