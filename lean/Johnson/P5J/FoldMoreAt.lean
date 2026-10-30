-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/FoldMoreAt.lean: THE NUMBER OF SLOTS OF A SEGMENT's LEDGER, AS A CLOSED TERM BESIDE THE
COMPOSED MEANING's CONSTANT. One definition, one test with code, two theorems.

Why. `FoldMore Rch at_ nsAt ps` (Johnson/Desc/First/FoldMore.lean) reads a function nsAt. Here it is
a term with code of the public parameters Zp.

What is said. `At.nsAt Zp m`: the planning program's segment m's number of slots: the value of
`At.nsOf Zp m` (Johnson/P5J/LettersAt.lean); 0 where the planning program has no segment m.
`At.nsThereB Zp`: a test that can fail: the planning program has a segment for every member of the
written list of segments: under it the 0 is never answered at a segment of that list.
`nsAt_of`: where nsOf answers n, nsAt is n. `nsOf_of_there`: under the test, at m below the list's
length, nsOf answers nsAt.

Limits. Definitions and unfoldings. Nothing on soundness. The fact "slots" was evaluated on an
honest run at both stored sizes, with the library's compiled code loaded, at this number laid
inline.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.LettersAt
import Johnson.Desc.First.FoldMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At

variable (Zp : ProofFile.Pub)

/-- Segment m's ledger's number of slots, off the planning program's record. -/
def nsAt (m : ℕ) : ℕ := (nsOf Zp m).getD 0

/-- A test that can fail: the planning program has a segment for each member of the written list. -/
def nsThereB : Bool := (List.range links.length).all fun m => (nsOf Zp m).isSome

theorem nsAt_of {m n : ℕ} (h : nsOf Zp m = some n) : nsAt Zp m = n := by
  unfold nsAt
  rw [h]
  rfl

theorem nsOf_of_there (h : nsThereB Zp = true) {m : ℕ} (hm : m < links.length) :
    nsOf Zp m = some (nsAt Zp m) := by
  unfold nsThereB at h
  have h1 := List.all_eq_true.mp h m (List.mem_range.mpr hm)
  obtain ⟨n, hn⟩ := Option.isSome_iff_exists.mp h1
  rw [hn, nsAt_of Zp hn]

end P5J.At

#print axioms P5J.At.nsAt_of
#print axioms P5J.At.nsOf_of_there
