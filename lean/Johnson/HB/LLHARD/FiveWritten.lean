-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/FiveWritten.lean: the test "five" of the shared chain's law (the third of
`Sh.testsO`): the one numbering of the oracle messages over all three chains gives five different
numbers to W, the index masks, o_u, o_omega and o_sp. Here at closed terms, in the thin spelling
`P5T.harrB arr (fiveTen N) fiveAll` (Johnson/Desc/K14/Law/LedgerFiveApartOwed.lean), which by its
owners' word is the law's own test by definition.

Row or tool. Definitions and closed facts on written values. They are an example for a premise of
another law. No law on a sub-protocol is named.

The test's arguments, their closed terms and their ties.
  arr: `P5T.arrOf P5T.seatsAllFull`: the numbering off the seats of all three chains
    (Johnson/P5T/PlanSeatsFull.lean). Tie: `seatsAllFull_is` with `planSeatsAll_at` there: through
    Lean.
  the seats of W and of the index masks: `P5T.N0Full.w` and `.index`. Tie: the same file's.
  the seats of o_u, o_omega and o_sp: `Fence.tenantSh lo layU layO`
    (Johnson/Desc/Sound/SharedMembers.lean) at the layouts of the two sendings at the written codes
    and the written linear shape. Tie for the codes and the shape: `first_in_scope`,
    `sized_in_scope`: through Lean.
  lo, the number of the shared chain's first tree: 83. In the law it is the number of oracles that
    the first chain's sub-protocols tell. It is tied by nothing yet.

What is here.
  `shFull`, `sentUFull`, `layUFull`, `layOFull`, `numsFull`: the closed terms, in the text of the
    law's own definitions. `lays_written`: what goes out with o_u can be said and both layouts are
    made, so none of the three is a fall-back.
  `seats_written`: the five seats are (82, 0), (1, 0), (83, 0), (84, 0) and (85, 0), and each is a
    seat of the list: so no number is the one that the numbering gives to a seat that it does not
    know.
  `numbers_written`: their five numbers.
  `five_written`: the test accepts.
  `five_rejects`: the negative test: at the numbering off the first chain's seats alone it rejects:
    the shared chain's three seats are unknown to it and get one number.
By evaluations in Lean's kernel (`decide +kernel`): all five.

Limits. No form in scope is stated: lo is tied by nothing yet. Nothing on soundness.


-/
import Johnson.P5T.PlanSeatsFull
import Johnson.Desc.K14.Law.LedgerFiveApartOwed
import Johnson.Desc.Sound.SharedMembers
import Johnson.Desc.Sound.TieEnd
import Johnson.Desc.K14.Text
import Johnson.Desc.Ok.PlanWritten.SizedLit
import Johnson.G.PackLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Johnson.G
open VerifiableInference.Desc.Shared (NumbersS)
open VerifiableInference.Desc.Sound (tiedNumbers)
open VerifiableInference.PlanWritten (proofSizedFull)

/-- The written linear shape. -/
def shFull : LinShape := proofSizedFull.batch.shape

/-- The oracle messages of "send o_u". -/
def sentUFull : Array OracleNotice := (_root_.Desc.K14.withU shFull).getD #[]

/-- The two sendings' layouts of trees. -/
def layUFull : TreeLay := (layTrees codesFull2 sentUFull).getD default
def layOFull : TreeLay := (layTrees codesFull2 (_root_.Desc.K14.withOmega shFull)).getD default

/-- **The shared chain's numbers, closed.** -/
def numsFull : NumbersS :=
  tiedNumbers P5T.N0Full (Fence.numbersSh 83 layUFull layOFull (0, 0) (0, 0))

set_option maxRecDepth 1000000 in
/-- None of the three is a fall-back. -/
theorem lays_written :
    (_root_.Desc.K14.withU shFull).isSome = true ∧ (layTrees codesFull2 sentUFull).isSome = true ∧
      (layTrees codesFull2 (_root_.Desc.K14.withOmega shFull)).isSome = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **The five seats**, each a seat of the list. -/
theorem seats_written :
    fiveAll.map (fiveTen numsFull) = [(82, 0), (1, 0), (83, 0), (84, 0), (85, 0)] ∧
      ((fiveAll.map (fiveTen numsFull)).all fun q =>
        P5T.seatsAllFull.any fun p => p.j == q.1 && p.t == q.2) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **Their five numbers.** -/
theorem numbers_written :
    (fiveAll.map fun m =>
      P5T.arrOf P5T.seatsAllFull (fiveTen numsFull m).1 (fiveTen numsFull m).2) =
      [161, 4, 163, 165, 166] := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **The test accepts.** -/
theorem five_written :
    P5T.harrB (P5T.arrOf P5T.seatsAllFull) (fiveTen numsFull) fiveAll = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **The negative test**: at the numbering off the first chain's seats alone. -/
theorem five_rejects :
    P5T.harrB (P5T.arrOf P5T.psFull) (fiveTen numsFull) fiveAll = false := by decide +kernel

end Desc.K14.Law

#print axioms Desc.K14.Law.lays_written
#print axioms Desc.K14.Law.seats_written
#print axioms Desc.K14.Law.numbers_written
#print axioms Desc.K14.Law.five_written
#print axioms Desc.K14.Law.five_rejects
