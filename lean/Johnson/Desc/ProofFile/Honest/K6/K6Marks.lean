-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K6/K6Marks.lean: the marks of the sub-protocol "the output head's own
rounds" (K6) at the proof file's first chain, as one list. A light file: one definition and three
small theorems, over what the definition's code reads.

What a mark is, after Honest/Law/Marks.lean: a place, a test on the challenges, and a stated number.
It names an event of the challenges at which the verifier rejects nothing, and after which a
condition of some bound can fail.

  `part4Marks`           the list: two marks, both at `headPlace 24 4`: the 24 is a written
                         numeral, the number of the last link at the full size
  `part4Marks_seat`      each mark's place passes `markSeat` (Honest/Law/CoverSeats.lean)
  `part4Marks_length`    the list has two members
  `part4Marks_places`    both stand at `headPlace 24 4`

TWO STRUCTURES ARE WRITTEN OUT HERE, AND EACH IS A SECOND TEXT OF A DEFINITION OF OUR OWN: of
`goodK6Mark` (Honest/K6/GoodMark.lean) and of `linkedK6TMark` (Honest/K6/LinkedMark.lean). Each has
three fields. WHAT TIES THEM TO THEIR FIRSTS: `part4Marks_eq` (Honest/K6/Law/K6MarksLaw.lean): the
list is the list of these two marks: by `rfl`, without a hypothesis. THE FIRSTS STAY THE DEFINITIONS
OF WHICH THIS SUB-PROTOCOL's LAWS SPEAK: the laws on what stands at the marks' place and on what is
owed go through that equation, and the marks' own laws stand in their own files; the three small
ones in this file (the seat, the length, the places) read the list as it is written. WHY THE FIRSTS
ARE NOT IMPORTED: these two files also hold what is owed for the marks, and stand over more than
seventy files beyond the sealed library; whoever only names the list draws in some twenty. The tests
and the stated numbers are imported and called by name; none is written anew. No definition that is
sealed is written anew. A mark is a structure for a bound: it is no part of the prover, and runs in
nobody's stead. Honest/K6/GoodMark.lean, Honest/K6/LinkedMark.lean and Honest/K6/Law/K6MarksLaw.lean
are not in the library.

The two arguments. The list reads the ground's public structure G₀.W alone: the sub-protocol's
public numbers are `headParAt G₀` (Honest/K6/Part.lean). The public part Zp is not read: it stands
for the form's sake, which is one for all lists of marks. No argument is left open.

What each mark is for.
  * The first speaks where `goodK6` (Honest/K6/Good.lean) rejects: where the first element sampled
    at one of the rounds `goodRounds` is 0. It is for the verifier's later test that every sent
    scalar stands in a claim, at this sub-protocol's scalars.
  * The second speaks where `linkedK6T` (Honest/K6/LinkedTest.lean) rejects: where the first
    element sampled at one of the rounds `linkedRounds` is 0 or 1. It is for the verifier's later
    test that no weight on the reads' row is 0, at three of the head's five matrices. The tables on
    the two others are made of the lookup's challenges or of public numbers.
  Both sentences are readings of the verifier's text. Even by these readings a mark's silence does
  not give the test that it is for: it says nothing of the batching element, at which a coefficient
  or a weight that is not the zero polynomial can still come to 0, and the second mark says nothing
  of the ties' row.

Limits.
  * Each mark's share is a written pair of numbers and no bound.
  * No theorem ties either mark to the verifier's test that it is for.
  * `part4Marks_length` holds at every ground, since the list looks nothing up. That a member of the
    chain stands at the marks' place, that each mark names a round at the full size, and how many,
    stands in Honest/K6/Law/K6MarksLaw.lean.
  * All limits of Honest/K6/Good.lean and Honest/K6/LinkedTest.lean hold here too.
  * Nothing on any property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.K6.LinkedTest
import Johnson.Desc.ProofFile.Honest.K6.Part
import Johnson.Desc.ProofFile.Honest.Law.Marks
import Johnson.Desc.ProofFile.Honest.Law.CoverSeats

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6

/-- **The sub-protocol's marks at the proof file's first chain.** G₀: the ground; its public
structure is read. The public part is not read. Both shares are written pairs of numbers, no bounds.
The two structures are `goodK6Mark` and `linkedK6TMark` written out: see the head. -/
def part4Marks (_Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) : List ProofFile.Honest.Mark :=
  [{ place := headPlace 24 4
     test := fun _ own => goodK6Says (headParAt G₀) own
     share := goodK6Odds (headParAt G₀) },
   { place := headPlace 24 4
     test := fun _ own => linkedK6TSays (headParAt G₀) own
     share := linkedK6TOdds (headParAt G₀) }]

/-- Each mark stands where a mark of the first chain may stand. -/
theorem part4Marks_seat (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) :
    ∀ mk ∈ part4Marks Zp G₀, ProofFile.Honest.markSeat mk.place = true := by
  intro mk hmk
  unfold part4Marks at hmk
  rcases List.mem_cons.1 hmk with rfl | h2
  · rfl
  · rcases List.mem_cons.1 h2 with rfl | h3
    · rfl
    · exact absurd h3 List.not_mem_nil

/-- Two marks, at every public part and ground: nothing is looked up. -/
theorem part4Marks_length (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) : (part4Marks Zp G₀).length = 2 :=
  rfl

/-- Both at `headPlace 24 4`, at every ground: the 24 is a written numeral. -/
theorem part4Marks_places (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) :
    (part4Marks Zp G₀).map (·.place) = [headPlace 24 4, headPlace 24 4] :=
  rfl

#print axioms part4Marks_seat
#print axioms part4Marks_length
#print axioms part4Marks_places

end ProofFile.Honest.K6
