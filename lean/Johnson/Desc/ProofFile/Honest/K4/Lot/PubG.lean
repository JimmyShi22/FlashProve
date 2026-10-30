-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Lot/PubG.lean: ONE DEFINITION WITH CODE. No statement.

What is here. `k4PubG Zp g`: the public data of the place of the feed-forward layers' own rounds
(sub-protocol K4) in group g, AS A TERM OF THE PUBLIC PART AND THE GROUP's NUMBER ALONE: the layers'
public data and the group's plan are those of the public part's own structure (`P5J.At.X Zp`); the
link and the segment are 2 g, the piece is 3 (`k4PubAtX`, Law/FitsX.lean); the rounds in front are
counted off the public part's table of named steps, up to the step of K4's stretch in group g
(`k4StepOf`, Law/FrontClosed.lean). Nothing where the structure has no plan for g or the table has
no such step. Why it lies here, outside the files of laws: a lot of entries for a laying of the
honest prover's messages takes the group's number alone and makes the public data of it, so that the
message's number, the places and the coins come of one g.

Not shown here. NOTHING IS SHOWN HERE: a definition claims nothing. What it returns, field by field,
and that it is what `k4PubOf` returns at the parameters of the member of group g where that member
is laid: Law/W/PubGOf.lean. That it returns (under the head at the maker's return):
Law/ClosingLinePayers.lean. IT DOES NOT ASK THE TEST
`k4TableFits`, which the lot's honest side asks before it lays a half (`k4HLot`,
Honest/K4/Part.lean): it can return where the prover has no half. THE SEGMENT's NUMBER, 2 g, IS THE
LINK's NUMBER ONLY WHERE THE PROOF COVERS ATTENTION, as the docstring of `k4PubOf`
(Honest/K4/Part.lean) says of its own. A program's walk from import to import, which reads import
lines alone and stops unopened at Johnson/Goal/, ThirdParty/, Johnson/D/, Johnson/Bridge/ and
Cb/Bridge*, stopped at 10 modules under Johnson/Goal/ and at 3 under Johnson/Bridge/: floors; the
first come with `P5J.At.X` (Johnson/P5J/LettersAt.lean). Nothing on soundness, on completeness or on
any other property. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.FrontClosed
import Johnson.Desc.ProofFile.Honest.K4.Law.FitsX
import Johnson.P5J.Rad3Seat3At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.Lot
open OnBytes.Desc.First.K4.Honest (K4Pub)

/-- **The public data of K4's place in group g, of the public part and g alone.** This is a
definition; it claims nothing. -/
def k4PubG (Zp : ProofFile.Pub) (g : ℕ) : Option K4Pub :=
  ((P5J.At.X Zp).G[g]?).bind fun hp =>
    (Zp.roundsBefore? (k4StepOf g)).map fun r0 => k4PubAtX (P5J.At.X Zp) hp g r0

end ProofFile.Honest.K4.Lot
