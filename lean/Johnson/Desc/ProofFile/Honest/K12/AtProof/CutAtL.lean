-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/CutAtL.lean: what the first chain's blocks round the
proximity test declare, under the library's head: how many rounds, and at which places. No
definition; ten theorems, four of them helpers.

First, its reach. All of it is under the head. At a public part beyond the head it says nothing.

  `written_353`, `written_354`, `written_front`, `written_places`   four closed facts on the written
                 list, by the kernel
  `lens_at_head`   how many rounds each block of the first chain declares is the third field of the
                 library's written cut (`cutFirstFull`, Johnson/Desc/Ok/PlanWritten/CutLit.lean)
  `finish_two_rounds`   the block in front of the test, number 353, declares two rounds
  `test_rounds_L`   the test's own block, number 354, declares 33
  `front_rounds_L`   the blocks in front of number 354 declare 48237 rounds together
  `places_at_L`    number 353 stands at the last code switch's place, number 354 at `placeL`
  `any_placeL_at_head'`   so a block of the chain stands at `placeL`, at every letter for the
                 earlier hash (`any_placeL_at_head`, LotAtDoorTests.lean: at the concrete one)

Why. `heardL` (JobL.lean) takes all challenges but the last two for those in front of the finish:
that wants, among other things (the first limit), that the block in front of the test declares two
rounds. And a front "shows just the rounds in front" where it shows as many as `front_rounds_L`
counts.

By what. Sealed: `OnBytes.Road.K4.cut_of_head` (Johnson/Road/K4/K4HeadWritten.lean): under the head
the cut of the description's first chain is the written one: that theorem, which is
`P5J.pins_of_laid`'s second half, ties the written list to the description; `First.roundsLen_cut`,
`First.told_at_cut` (Johnson/Desc/First/CutAtNumbers.lean). The closed facts on the written list: by
the kernel, each under a raised `maxRecDepth`.

Neighbours. The equation of `cut_of_head` stands in the library and beside it several times more:
`P5J.pins_of_laid`'s second half; `pins_at_head`'s
(Johnson/Desc/First/Att/Door/Law/K5CondOfHead.lean); `tests_at_head`'s second conjunct
(Johnson/Desc/K2/Honest/Returns/UnderHead.lean); `file_head`'s third
(Honest/Law/CoverHeadFile.lean). General in the block's number, under the stronger head at the
concrete earlier hash: `k6_row_at_head` (Honest/K6/Law/RoundsWritten.lean): the written list's row
number n is the block's name, place, number of rounds and so on: `finish_two_rounds`,
`test_rounds_L` and `places_at_L` say, under the plainer head and at every earlier hash, what it
says at 353 and 354 with the closed facts; `k6_roundsIn_of_cut`, `k6_member_at` and five closed rows
(337 to 341) stand there too: not called here. `lens_at_head` stands as a step inside a proof of
Johnson/LPFE1R/RowsQAt.lean (`rows_q_at`), at the concrete earlier hash; that file's `lensW` is its
right side and its `offW 354` the number of `front_rounds_L`: not called here. `member_at_354`,
`place_at_354` (Johnson/Desc/K12/Honest/Shape/TestKeepsAt354.lean): at the concrete earlier hash.

Limits.
- How much of "`heardL` takes the right challenges" this pays: the block in front of the test
  declares two rounds and stands at the last code switch's place. It does not say that this block is
  that kind's finish (the library's `IM.k2_finish_of`, Johnson/IMR/K2Seat.lean: that kind's lot's
  block alone: a mute one, or the finish at the plan's numbers), nor that its honest side is one
  part, nor that each declared round draws just one challenge.
- `front_rounds_L` speaks of the first 354 blocks. That these are the blocks in front of `placeL`
  is `front_is_take_L` (K12/Blind/KeepsAtFinish.lean), at the concrete earlier hash.
- Nothing on what the rounds hold. Nothing is played here.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Road.K4.K4HeadWritten
import Johnson.Desc.First.CutAtNumbers
import Johnson.P5J.AtMg
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Block Place)
open VerifiableInference.PlanWritten (cutFirstFull)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **How many rounds each block of the first chain declares is the written cut's third field.** -/
theorem lens_at_head (h : P5J.AtMg o Z D r₀ Zp Np cF) :
    cF.blocksInOrder.map (·.rounds.length) = cutFirstFull.map (·.2.2.1) := by
  rw [VerifiableInference.Desc.First.roundsLen_cut, OnBytes.Road.K4.cut_of_head h]

set_option maxRecDepth 1000000 in
theorem written_353 : (cutFirstFull.map (·.2.2.1))[353]? = some 2 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem written_354 : (cutFirstFull.map (·.2.2.1))[354]? = some 33 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem written_front : ((cutFirstFull.map (·.2.2.1)).take 354).sum = 48237 := by decide +kernel

set_option maxRecDepth 1000000 in
theorem written_places :
    (cutFirstFull.map (·.2.1))[353]? = some ⟨1, none, 1, .K2⟩ ∧
      (cutFirstFull.map (·.2.1))[354]? = some placeL := by decide +kernel

/-- **The block in front of the proximity test declares two rounds.** -/
theorem finish_two_rounds (h : P5J.AtMg o Z D r₀ Zp Np cF) {b : Block P5J.TS ProofFile.Cl}
    (hb : cF.blocksInOrder[353]? = some b) : b.rounds.length = 2 := by
  have e : (cF.blocksInOrder.map (·.rounds.length))[353]? = some 2 := by
    rw [lens_at_head h]
    exact written_353
  rw [List.getElem?_map, hb] at e
  exact Option.some.inj e

/-- The test's own block declares 33. -/
theorem test_rounds_L (h : P5J.AtMg o Z D r₀ Zp Np cF) {b : Block P5J.TS ProofFile.Cl}
    (hb : cF.blocksInOrder[354]? = some b) : b.rounds.length = 33 := by
  have e : (cF.blocksInOrder.map (·.rounds.length))[354]? = some 33 := by
    rw [lens_at_head h]
    exact written_354
  rw [List.getElem?_map, hb] at e
  exact Option.some.inj e

/-- **The blocks in front of number 354 declare 48237 rounds together.** -/
theorem front_rounds_L (h : P5J.AtMg o Z D r₀ Zp Np cF) :
    ((cF.blocksInOrder.take 354).flatMap (·.rounds)).length = 48237 := by
  rw [List.length_flatMap, List.map_take, lens_at_head h]
  exact written_front

/-- **The places.** -/
theorem places_at_L (h : P5J.AtMg o Z D r₀ Zp Np cF) :
    (∃ b, cF.blocksInOrder[353]? = some b ∧ b.place = ⟨1, none, 1, .K2⟩) ∧
      ∃ b, cF.blocksInOrder[354]? = some b ∧ b.place = placeL := by
  have e : cF.blocksInOrder.map (·.place) = cutFirstFull.map (·.2.1) :=
    (VerifiableInference.Desc.First.told_at_cut (OnBytes.Road.K4.cut_of_head h)).1
  obtain ⟨w1, w2⟩ := written_places
  have e1 := (congrArg (·[353]?) e).trans w1
  have e2 := (congrArg (·[354]?) e).trans w2
  simp only [List.getElem?_map, Option.map_eq_some_iff] at e1 e2
  exact ⟨e1, e2⟩

/-- So a block of the first chain stands at `placeL`, at every letter for the earlier hash. -/
theorem any_placeL_at_head' (h : P5J.AtMg o Z D r₀ Zp Np cF) :
    cF.blocksInOrder.any (·.place == placeL) = true := by
  obtain ⟨-, b, hb, hp⟩ := places_at_L h
  refine List.any_eq_true.2 ⟨b, List.mem_of_getElem? hb, ?_⟩
  rw [hp]
  exact beq_self_eq_true _

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.lens_at_head
#print axioms ProofFile.Honest.K12.AtProof.written_353
#print axioms ProofFile.Honest.K12.AtProof.written_354
#print axioms ProofFile.Honest.K12.AtProof.written_front
#print axioms ProofFile.Honest.K12.AtProof.written_places
#print axioms ProofFile.Honest.K12.AtProof.finish_two_rounds
#print axioms ProofFile.Honest.K12.AtProof.test_rounds_L
#print axioms ProofFile.Honest.K12.AtProof.front_rounds_L
#print axioms ProofFile.Honest.K12.AtProof.places_at_L
#print axioms ProofFile.Honest.K12.AtProof.any_placeL_at_head'
