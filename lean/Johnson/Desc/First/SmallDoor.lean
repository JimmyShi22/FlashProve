-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/SmallDoor.lean: names are taken out of the table's list of extra public tests
(`More`, Johnson/Desc/First/Borders.lean). Definitions with code and four equations. No Mathlib.
Why. Between two sub-protocols of a request's own rounds the table asks public tests of the
verifier's state. `More` says, name by name, which sub-protocol makes such a test true, which asks
it and which drops it, and which are asked from the start on. A test that is asked from the start
and never dropped, or over many segments, must be kept by (nearly) every sub-protocol: by every
author, for every other author's name. Such a test says a fact on the verifier's state that holds
at every state that the verifier reaches: it is proved once, along the run, and is not asked by
the table.
  `leavesName n`: the thirteen names that leave: eight without a segment ("K12.bookInOrder",
    "K12.seatsCarried", "K12.bookFits", "K12.msgShapes", "K13.weightsOk", "K13.pileMasks",
    "K13.pileWithin", "K13.oneRow"); five with one ("pile.room", "frame.liveIs", "K8.lay7",
    "K8.onThird", "K8.funsThird": the last three are asked by one sub-protocol alone, whose
    authors take them from the reached states by a lemma of their own).
  `MoreRow.strike p`, `More.strike p`: the names n with p n = true are taken out of what a row
    makes, asks and drops, and out of what is asked from the start.
  `strike_start`, `strike_rows`, `strike_merge_start`, `strike_none`: what that is, by unfolding.
Limits: definitions. The names go by their spelling: a name that is spelt otherwise, or stands
with a segment where this list has none, is NOT taken out, silently. WHOEVER SPENT A NAME THAT
LEAVES MUST NOW TAKE ITS FACT FROM ELSEWHERE (a lemma on reached states): nothing here gives it.
No soundness is claimed.

-/
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First

/-- The names that leave the table's list of extra public tests. -/
def leavesName : MoreName → Bool
  | (none, s) =>
    ["K12.bookInOrder", "K12.seatsCarried", "K12.bookFits", "K12.msgShapes", "K13.weightsOk",
      "K13.pileMasks", "K13.pileWithin", "K13.oneRow"].contains s
  | (some _, s) =>
    ["pile.room", "frame.liveIs", "K8.lay7", "K8.onThird", "K8.funsThird"].contains s

/-- A row without the names at which p says true. -/
def MoreRow.strike (p : MoreName → Bool) (r : MoreRow) : MoreRow where
  asks := r.asks.filter fun n => !p n
  makes := r.makes.filter fun n => !p n
  drops := r.drops.filter fun n => !p n

/-- **The list of extra public tests without the names at which p says true.** -/
def More.strike (p : MoreName → Bool) (M : More) : More where
  rows l q := (M.rows l q).strike p
  start := M.start.filter fun n => !p n

theorem strike_start (p : MoreName → Bool) (M : More) :
    (M.strike p).start = M.start.filter fun n => !p n := rfl

theorem strike_rows (p : MoreName → Bool) (M : More) (l : List ModelPart) (q : Desc.Place) :
    (M.strike p).rows l q = (M.rows l q).strike p := rfl

theorem strike_merge_start (p : MoreName → Bool) (A B : More) :
    ((A.merge B).strike p).start = (A.strike p).start ++ (B.strike p).start := by
  show (A.start ++ B.start).filter _ = _
  rw [List.filter_append]
  rfl

theorem strike_none (M : More) : (M.strike fun _ => false).start = M.start := by
  show M.start.filter _ = _
  simp

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.strike_start
#print axioms VerifiableInference.Desc.First.strike_rows
#print axioms VerifiableInference.Desc.First.strike_merge_start
#print axioms VerifiableInference.Desc.First.strike_none
