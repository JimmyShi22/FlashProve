-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/AtS.lean: kind K9 at the state that the proof file's first chain carries
(Johnson/Desc/First/State.lean: S): the lens. Definitions with code; no theorem.

What the kind reads of S: rowsOwed; the open segment's book-keeping (link?), ledger (fork?) and the
smallness test's record (tl?: for the number of indices that its equations take); the statement, the
book of trees and the number of roots; and the number of slots that the segment's messages have
taken, which stands at another field in each sort of segment: the smallness test's slotB (layers),
the ledger's counter (attention), slot (the head). mergeOf, for the tests behind the adding: the
slot of the merge's end value, as the merge returned it (layers: own.wo.sFv; the head: wo.sFv;
attention has no merge).
rowsOwed HAS TWO FORMS FOR "NOTHING IS OWED": none, and some 0 (a step that stores what its closed
entry counts as it stands stores some 0). The kind's text asks "is none": so THE LENS HANDS some 0
ON AS none (owedOf): else the draw would refuse an honest file behind such a step.
THREE OF THESE FIELDS ARE THERE ONLY ONCE THEIR STEP HAS WRITTEN THEM (the head's slot; the merge's
record at a layers' segment and at the head): until then usedOf and mergeOf answer nothing. Without
the slots' number the lens gives no part, and the block refuses; without the merge's slot the test
on the free slot asks a coefficient other than 0 at every slot, which an honest run does not meet.
What it writes: rowsOwed; the book-keeping; the ledger; the statement. The book and the roots are
handed to the two effects on the statement and are not turned by them; they are not written back.


-/
import Johnson.Desc.First.State
import Johnson.Desc.First.Batch.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

/-- The rows that are still owed a count; "some 0" is "none". -/
def owedOf (s : S) : Option Nat :=
  match s.rowsOwed with
  | some 0 => none
  | x => x

/-- The slots that the open segment's messages have taken. -/
def usedOf (s : S) : Option Nat :=
  match s.here with
  | .lay a => some a.tl.slotB
  | .att a => some a.F.next
  | .head a => if a.opened then a.slot else none
  | _ => none

/-- The slot of the merge's end value in the open segment: for the tests behind the adding
(Johnson/Desc/First/Batch/TestsAtS.lean). -/
def mergeOf (s : S) : Option Nat :=
  match s.here with
  | .lay a => a.own.map (·.wo.sFv)
  | .head a => a.wo.map (·.sFv)
  | _ => none

/-- The indices that the smallness test's equations take: the matrices' equations as they were
numbered, and a step for each read that was laid. Nothing before these claims have been made. In own
words: HTailF2.equationsLaidF (OnBytes/Model/Tail.lean) says the same. -/
def laidOf (tl : HTailF2) : Option Nat :=
  if tl.eqFirst.size != tl.NM + 1 then none
  else some (tl.eqFirst.getD tl.NM 0 + tl.nX4Laid * tl.stepF)

/-- **The lens.** -/
def atS : Lens S where
  get? := fun s => do
    let L ← s.link?
    let F ← s.fork?
    let tl ← s.tl?
    let used ← usedOf s
    pure { owed := owedOf s, used := used, laid := laidOf tl, L := L, F := F,
           d := { st := s.st, book := s.book, roots := s.roots, opened := [], loc := () } }
  set := fun s p => { (s.putLink p.L).putFork p.F with st := p.d.st, rowsOwed := p.owed }

end VerifiableInference.Desc.K9
