-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/G/LinkLit.lean: the sampled messages of each link of a proof's first chain at the full-size
example, out of the written list of Johnson/G/PackLit.lean, and the test of Johnson/Pack/Check.lean
at each link's whole list, as a theorem by an evaluation in Lean's kernel.

Definitions, one theorem, and one test by evaluation.
Main names:
  `frameFullLit`: the 76 sendings of the frame: those elements of `packFullLit` that come first
    under the proof's codes.
  `linksFullLit`: 26 lists: for each of the 25 links the sampled messages of its three sendings, in
    order; then the last group's.
  `linksFullLit_meets`: `Johnson.Pack.allMeet` at the proof's codes is true at each of the 26.
The test: the 26 lists are those that Johnson/G/LinkSig.lean computes from the public files.
Whence the numbers: Johnson/G/PackLit.lean's head says from which files its list was made.
Limits: those of Johnson/G/PackLit.lean and Johnson/G/LinkSig.lean. The theorem speaks of the
written list; that it is the planner's is held by tests by evaluation only. That the frame's
sendings are the first 76 under the proof's codes, three a link, is held by the test here.
-/
import Johnson.G.PackLit
import Johnson.G.LinkSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G

open OnBytes

/-- The frame's sendings: each one's sampled messages. -/
def frameFullLit : List (List (OracleShape × Nat)) :=
  ((packFullLit.dropWhile fun x => decide (x.1 ≠ codesFull2)).take 76).map (·.2)

/-- Lists joined three by three; what is left at the end is joined too. -/
def byThree {α : Type} : List (List α) → List (List α)
  | a :: b :: c :: t => (a ++ b ++ c) :: byThree t
  | [] => []
  | l => [l.flatten]

/-- The sampled messages of each link, and of the last group. -/
def linksFullLit : List (List (OracleShape × Nat)) := byThree frameFullLit

set_option maxRecDepth 1000000 in
/-- The test holds at each link's whole list. -/
theorem linksFullLit_meets :
    (linksFullLit.all fun l => Johnson.Pack.allMeet codesFull2 l) = true := by
  decide +kernel

-- the 26 lists and the codes are those that are computed from the public files
#guard
  let R := rowsFull
  linksFullLit == (List.range 26).map (linkList R) &&
    ((linkRows R 0).head?.map (·.codes)) == some codesFull2

end Johnson.G

#print axioms Johnson.G.linksFullLit_meets
