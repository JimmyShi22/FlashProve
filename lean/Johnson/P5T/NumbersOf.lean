-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/NumbersOf.lean: NO PART OF THE DESCRIPTION: THE TABLE OF JOINTS' LETTER `Numbers`
(Johnson/Desc/First/Borders.lean), MADE AT A PLAN's SEATS, WITH CODE. THE VERY TEXT OF Johnson/P5T/PlanNumbers.lean
(not in this library), MOVED BY PROGRAM, no word turned: so that the letter hangs on P5T/PlanSeats.lean and the table alone, and on
no file of the radii (Johnson/G/LinkSig.lean), which the members' lists beside it need.
  numbersOf ps: sent m t: the sampled messages of "link m, moment t", but a message atStart · keptOf m: those of link m's
    group whose message (original or copy) link m + 1 sends again as a kept copy · index: the first message atStart ·
    w: the sampled message of the sending "W" · inside, SAID POSITIVELY, not as what is left over: every message without a
    sample, and every message of a sending that is no link's and not "W" (the last test's switches).
It reads nothing and writes nothing: the caller hands it values.
-/
import Johnson.P5T.PlanSeats
import Johnson.Desc.First.Borders

open VerifiableInference.Desc VerifiableInference.Desc.First

namespace P5T

def PSeat.smpd (p : PSeat) : Bool := decide (0 < p.shape.answers)
def PSeat.seat (p : PSeat) : Nat × Nat := (p.j, p.t)
def PSeat.isStart (p : PSeat) : Bool := match p.role with | .atStart _ => true | _ => false

/-- **The table's numbers, off the plan.** -/
def numbersOf (ps : List PSeat) : Numbers where
  sent := fun m t => (ps.filter fun p => p.seg == some (m, t) && p.smpd && !p.isStart).map (·.seat)
  keptOf := fun m =>
    let next := (ps.filter fun p => p.seg == some (m + 1, 0)).filterMap fun p =>
      match p.role with
      | .kept l k => some ((0, l, k) : Nat × Nat × Nat)
      | _ => none
    (ps.filter fun p => p.seg.map (·.1) == some m && p.smpd && !p.isStart && next.contains (keyOf p)).map (·.seat)
  index := ((ps.find? (·.isStart)).map (·.seat)).getD (0, 0)
  w := ((ps.find? fun p => p.label == "W" && p.smpd).map (·.seat)).getD (0, 0)
  inside := (ps.filter fun p => !p.smpd || (p.seg.isNone && p.label != "W")).map (·.seat)

end P5T
