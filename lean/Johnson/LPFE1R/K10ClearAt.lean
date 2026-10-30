-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/K10ClearAt.lean: THE FIELD "clear" OF AtMgA.K10Left
(Johnson/P5J/K10Left.lean): RidersClearQ (At.arr Zp) (At.N Zp cF) fullLinks At.ps: FROM THE ONE HEAD
AtMg ALONE. No kind's: every kind's condition asks it. A joining: nothing is evaluated here.

  P5J.AtMg.arr_is  the numbers of the witness's messages are the written seats' (seats_in_scope,
                   Johnson/P5T/PlanSeatsTie.lean, its second clause)
  P5J.AtMg.laysClear   the table's test accepts at At.arr Zp and At.N Zp cF: by AtMg.N_is
                   (Johnson/P5T/CoreAtMg.lean), laysClear_told and clear_full
                   (Link/Law/ClearAtCore.lean: the kernel)
  P5J.AtMg.clear   **the field clear**: by ridersClearQ
                   (Johnson/Desc/Sound/BordersSides.lean) and readsOpen9 |
                   rowsApart9 (Link/Law/FifthTieRiders.lean: the kernel, at the written list)

Limits. IT STANDS OVER THE VERIFIER's LIST OF ENTRY TESTS OF THIRTEEN ROWS (through the pins;
GLOSSARY.md, "entry tests"). The full size alone. No soundness statement.

-/
import Johnson.P5T.CoreAtMg
import Johnson.Desc.First.Link.Law.ClearAtCore
import Johnson.Desc.First.Link.Law.FifthTieRiders
import Johnson.Desc.Sound.BordersSides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (start laysClear)
open VerifiableInference.Desc.Sound (RidersClearQ ridersClearQ)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc.LinkJoin (laysClear_told clear_full readsOpen9 rowsApart9)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- The numbers of the witness's messages are the written seats'. -/
theorem AtMg.arr_is (h : AtMg o Z D r Zp Np cF) : At.arr Zp = P5T.arrOf P5T.seatsAllFull := by
  unfold At.arr At.pseatsAll
  rw [(P5T.seats_in_scope h.scope h.laid.pub (pins_of_laid h.scope h.laid).1
    h.laid.laidPOf).2.1]

/-- The table's test accepts at the numbers in which a kind's law ends. -/
theorem AtMg.laysClear (h : AtMg o Z D r Zp Np cF) :
    laysClear (At.arr Zp) (At.N Zp cF) fullLinks At.ps (start fullLinks) = true := by
  rw [h.arr_is, h.N_is]
  exact (laysClear_told _ _ _ _ _ _ _ _ _ _).trans clear_full

/-- **K10Left's FIELD clear.** -/
theorem AtMg.clear (h : AtMg o Z D r Zp Np cF) :
    RidersClearQ (At.arr Zp) (At.N Zp cF) fullLinks At.ps :=
  ridersClearQ _ _ _ _ h.laysClear readsOpen9 rowsApart9

end P5J

#print axioms P5J.AtMg.arr_is
#print axioms P5J.AtMg.laysClear
#print axioms P5J.AtMg.clear
