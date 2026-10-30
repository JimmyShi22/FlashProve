-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5T/CoreAtMg.lean: IN THE GOALS' SCOPE, WHERE THE VERIFIER's OWN VALUE IS LAID (`LaidAt`,
Johnson/P5J/LaidOpens.lean), THE CORE OF THE TABLE's NUMBERS IS THE WRITTEN ONE: the joint by
which a closed fact on the written seats (`psFull`, `N0Full`, Johnson/P5T/PlanSeatsFull.lean)
reaches the numbers in which a kind's law ends (`At.N Zp cF`, Johnson/P5J/LettersAt.lean). Ten
theorems. A joining: nothing is evaluated here.
Why. A test on the seats, on `sent`, `keptOf`, `index`, `w` or what is made of them can be had by
Lean's kernel at the written values. A law wants it at `At.N Zp cF`. The step between is the same
for every such test: so it stands here once, by name. It is typed from two premises alone, hW: the
scope, and L: the value is laid; a spender that holds the whole head `AtMg`
(Johnson/P5J/AtMg.lean) has both as fields, and calls the forms `AtMg.…`.
  `LaidAt.seats`: `planSeats Zp Zp.D.1 = psFull`.
  `LaidAt.core`: **`numbersOf (planSeats Zp Zp.D.1) = N0Full`**. Both by `seats_in_scope`
  (Johnson/P5T/PlanSeatsTie.lean); of its four premises the entry test on the written values is
  paid by `pins_of_laid` (Johnson/Goal/Skeleton/PinsOfLaid.lean), "the value is laid" as an
  equation by `LaidAt.laidPOf` (Johnson/P5T/FenceAtMg.lean).
  `LaidAt.N_is`: `At.N Zp cF` is `N0Full` with `rowsAt` laid (`withRows`) and filled off what the
  sub-protocols tell (`withTold`).
  `LaidAt.N_core`: the six fields that neither of these two turns: `sent`, `keptOf`, `index`, `w`,
  `inside`, `groupAt` of `At.N Zp cF` are `N0Full`'s.
  `LaidAt.fence`: the table's test on the fence at these numbers: `fenceFit (At.N Zp cF) fullLinks
  At.ps = true`.
  `AtMg.seats`, `AtMg.core`, `AtMg.N_is`, `AtMg.N_core`: the first four at the head; `AtMg.N_core`
  gives the first four fields. `AtMg.N_six`: all six.
Limits. IT STANDS OVER THE VERIFIER's LIST OF THIRTEEN ENTRY TESTS (ProofAsksFirstThirteenTests.lean) ALONE
(`pins_of_laid`). Whether `LaidAt` can be met at the release's own files is not shown here. The
full size alone. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.


-/
import Johnson.P5T.FenceAtMg
import Johnson.Goal.Skeleton.PinsOfLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (fenceFit possAt)
open OnBytes.Maker (WholeD)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- In scope, where the value is laid, the first chain's seats are the written ones. -/
theorem LaidAt.seats (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF)
    (hW : VerifierAndGoals.InScope Z = true) : P5T.planSeats Zp Zp.D.1 = P5T.psFull :=
  (P5T.seats_in_scope hW L.pub (pins_of_laid hW L).1 L.laidPOf).1

/-- **In scope, where the value is laid, the core of the table's numbers is the written one.** -/
theorem LaidAt.core (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF)
    (hW : VerifierAndGoals.InScope Z = true) : P5T.numbersOf (P5T.planSeats Zp Zp.D.1) = P5T.N0Full :=
  (P5T.seats_in_scope hW L.pub (pins_of_laid hW L).1 L.laidPOf).2.2

/-- The numbers in which a kind's law ends, over the written core. -/
theorem LaidAt.N_is (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF)
    (hW : VerifierAndGoals.InScope Z = true) :
    At.N Zp cF = (P5T.N0Full.withRows (At.shape Zp) (possAt cF.blocksInOrder At.links.length)
      At.links.length).withTold At.ps (At.told cF) := by
  unfold At.N At.pseats
  rw [L.core hW]

/-- The six fields that neither `withRows` nor `withTold` turns. -/
theorem LaidAt.N_core (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF)
    (hW : VerifierAndGoals.InScope Z = true) :
    (At.N Zp cF).sent = P5T.N0Full.sent ∧ (At.N Zp cF).keptOf = P5T.N0Full.keptOf ∧
      (At.N Zp cF).index = P5T.N0Full.index ∧ (At.N Zp cF).w = P5T.N0Full.w ∧
      (At.N Zp cF).inside = P5T.N0Full.inside ∧ (At.N Zp cF).groupAt = P5T.N0Full.groupAt := by
  rw [L.N_is hW]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The table's test on the fence, from the scope and "the value is laid" alone. -/
theorem LaidAt.fence (L : LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF)
    (hW : VerifierAndGoals.InScope Z = true) : fenceFit (At.N Zp cF) fullLinks At.ps = true := by
  have e := P5T.fence_in_scope hW L.pub (pins_of_laid hW L).1 L.laidPOf (pins_of_laid hW L).2
    (At.shape Zp) (possAt cF.blocksInOrder At.links.length) At.links.length
  unfold At.N At.ps At.pseats
  rw [At.told_is]
  exact e

/-- At the head. -/
theorem AtMg.seats (h : AtMg o Z D r Zp Np cF) : P5T.planSeats Zp Zp.D.1 = P5T.psFull :=
  h.laid.seats h.scope

/-- At the head. -/
theorem AtMg.core (h : AtMg o Z D r Zp Np cF) :
    P5T.numbersOf (P5T.planSeats Zp Zp.D.1) = P5T.N0Full := h.laid.core h.scope

/-- At the head. -/
theorem AtMg.N_is (h : AtMg o Z D r Zp Np cF) :
    At.N Zp cF = (P5T.N0Full.withRows (At.shape Zp) (possAt cF.blocksInOrder At.links.length)
      At.links.length).withTold At.ps (At.told cF) := h.laid.N_is h.scope

/-- At the head: all six fields. -/
theorem AtMg.N_six (h : AtMg o Z D r Zp Np cF) :
    (At.N Zp cF).sent = P5T.N0Full.sent ∧ (At.N Zp cF).keptOf = P5T.N0Full.keptOf ∧
      (At.N Zp cF).index = P5T.N0Full.index ∧ (At.N Zp cF).w = P5T.N0Full.w ∧
      (At.N Zp cF).inside = P5T.N0Full.inside ∧ (At.N Zp cF).groupAt = P5T.N0Full.groupAt :=
  h.laid.N_core h.scope

/-- At the head: the first four fields. -/
theorem AtMg.N_core (h : AtMg o Z D r Zp Np cF) :
    (At.N Zp cF).sent = P5T.N0Full.sent ∧ (At.N Zp cF).keptOf = P5T.N0Full.keptOf ∧
      (At.N Zp cF).index = P5T.N0Full.index ∧ (At.N Zp cF).w = P5T.N0Full.w :=
  let ⟨a, b, c, d, _⟩ := h.N_six
  ⟨a, b, c, d⟩

end P5J

#print axioms P5J.LaidAt.seats
#print axioms P5J.LaidAt.core
#print axioms P5J.LaidAt.N_is
#print axioms P5J.LaidAt.N_core
#print axioms P5J.LaidAt.fence
#print axioms P5J.AtMg.seats
#print axioms P5J.AtMg.core
#print axioms P5J.AtMg.N_is
#print axioms P5J.AtMg.N_six
#print axioms P5J.AtMg.N_core
