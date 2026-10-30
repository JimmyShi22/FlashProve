-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFE1R/SeedPublicFull.lean: PUBLIC PREMISES: what `seed_field`
(SeedAtSeat.lean beside this file) takes on public data: "no place stands twice in the plan's list
of places" (hnd) and, of hB, "the plan's list of places has the member's seat at the member's
number": at the written values of the full size BY LEAN's KERNEL, at all 25 links; and carried to
the composed meaning's own letters IN THE GOALS' SCOPE, where the verifier's own value is laid. hB's
third clause (the shapes) is ShapeAtNoFull.lean's. Theorems. A law file; no running text imports it.
  `places_apart_W`    BY THE KERNEL: the written list of places LFull.places
                    (Johnson/HB/LLHARD/LaidWritten.lean) has no place twice.
  `seats_are_places_W`   BY THE KERNEL: the written plan's seats are that list.
  `booked_written`    BY THE KERNEL: at every l < 25 and every place i of the l-th written list
                    lo: LFull.places[noK10 seatsFullW lo P5T.psFull l i]? = some (seatK10 lo
                    P5T.psFull l i).
  `booked_written_next`   A NEGATIVE LINE, BY THE KERNEL: against the seats of link l + 1 no link
                    passes.
  `ld_at_laid`        in scope, where the value is laid: what laidAtCodes returns at the public
                    part's own codes and sendings is LFull.
  `seed_public_laid`  so there, for every Ld that laidAtCodes returns: Ld.places.Nodup ∧ ∀ l <
                    25, ∀ i, Ld.places[noK10 (At.seats Zp) lo (At.pseats Zp) l i]? = some (seatK10
                    lo (At.pseats Zp) l i).

  `sentAtK10W`, `below_written`, `below_written_tight`, `below_laid`   THE CLOSED HALF OF hB's FIRST
                    CLAUSE: a written list of 25 numbers (what a run at the stored full-size files
                    printed as the messages sent at the places of the kind K10); BY THE KERNEL:
                    every member's number lies below its link's; at one fewer no link passes; and
                    the first at the composed meaning's letters.

Limits. OF hB's FIRST CLAUSE ONLY THE CLOSED HALF: that the table's number of messages sent at K10's
place IS the written number is other files' to show (the counts at a cut): not joined here. The full
size alone. Nothing on the verifier's state. Nothing on soundness or on hiding.

-/
import Johnson.LPFE1R.ShapeAtNoFull
import Johnson.HB.LLHARD.LaidWritten
import Johnson.Desc.Ok.PlanWritten.SizedTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.LinkJoin
open OnBytes
open OnBytes.Maker (WholeD)
open Johnson.G (linksFullLit codesFull2)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Close (noK10 seatK10)
open VerifiableInference.Desc.K12.Door (Laid laidAtCodes)
open VerifiableInference.Desc.K13.Law (LFull laid_at)
open VerifiableInference.PlanWritten.Joined (sends_in_scope first_written_in_scope)

set_option maxRecDepth 1000000 in
/-- The written list of places has no place twice. -/
theorem places_apart_W : LFull.places.Nodup := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The written plan's seats are the written list of places. -/
theorem seats_are_places_W : seatsFullW = LFull.places := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **At the written values, at all 25 links.** -/
theorem booked_written : ((List.range 25).all fun l =>
    (List.finRange (linksFullLit.getD l []).length).all fun i =>
      LFull.places[noK10 seatsFullW (linksFullLit.getD l []) P5T.psFull l i]? ==
        some (seatK10 (linksFullLit.getD l []) P5T.psFull l i)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative line: against the next link's seats. -/
theorem booked_written_next : ((List.range 25).any fun l =>
    (List.finRange (linksFullLit.getD l []).length).all fun i =>
      LFull.places[noK10 seatsFullW (linksFullLit.getD l []) P5T.psFull l i]? ==
        some (seatK10 (linksFullLit.getD l []) P5T.psFull (l + 1) i)) = false := by decide +kernel

/-- The numbers of messages sent at the 25 places of the kind K10, as a run at the stored full-size
files printed them. A WRITTEN LIST: that the table's numbers have these values is not said here. -/
def sentAtK10W : List ℕ :=
  [7, 14, 22, 29, 37, 44, 52, 59, 67, 74, 82, 89, 97, 104, 112, 119, 127, 134, 142, 149, 157, 164,
    172, 179, 185]

set_option maxRecDepth 1000000 in
/-- BY THE KERNEL: every member's number lies below the written count of its link. -/
theorem below_written : ((List.range 25).all fun l =>
    (List.finRange (linksFullLit.getD l []).length).all fun i =>
      decide (noK10 seatsFullW (linksFullLit.getD l []) P5T.psFull l i < sentAtK10W.getD l 0)) =
    true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative line: TIGHT: at one fewer no link passes. -/
theorem below_written_tight : ((List.range 25).any fun l =>
    (List.finRange (linksFullLit.getD l []).length).all fun i =>
      decide (noK10 seatsFullW (linksFullLit.getD l []) P5T.psFull l i < sentAtK10W.getD l 0 - 1)) =
    false := by decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- In scope, where the value is laid: the plan's list of places is the written one. -/
theorem ld_at_laid (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) :
    laidAtCodes Zp.first.codes Zp.made.proof.1 = some LFull :=
  laid_at
    ((first_written_in_scope hW L.pub (P5J.pins_of_laid hW L).1).1.trans
      VerifiableInference.PlanWritten.codes_written)
    (by rw [sends_in_scope hW L.pub (P5J.pins_of_laid hW L).1])

/-- **The two public premises at the composed meaning's own letters.** -/
theorem seed_public_laid (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {Ld : Laid}
    (hLd : laidAtCodes Zp.first.codes Zp.made.proof.1 = some Ld) :
    Ld.places.Nodup ∧ ∀ l, l < 25 → ∀ i : Fin (linksFullLit.getD l []).length,
      Ld.places[noK10 (P5J.At.seats Zp) (linksFullLit.getD l []) (P5J.At.pseats Zp) l i]? =
        some (seatK10 (linksFullLit.getD l []) (P5J.At.pseats Zp) l i) := by
  obtain rfl : LFull = Ld := Option.some.inj ((ld_at_laid hW L).symm.trans hLd)
  have e1 : P5J.At.pseats Zp = P5T.psFull := L.seats hW
  have e2 : P5J.At.seats Zp = seatsFullW := by
    unfold P5J.At.seats seatsFullW
    rw [e1]
  refine ⟨places_apart_W, fun l hl i => ?_⟩
  rw [e1, e2]
  exact eq_of_beq (List.all_eq_true.1 (List.all_eq_true.1 booked_written l (List.mem_range.2 hl)) i
    (List.mem_finRange i))

/-- The closed half of "the number lies below", at the same letters. -/
theorem below_laid (hW : VerifierAndGoals.InScope Z = true)
    (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {l : ℕ} (hl : l < 25)
    (i : Fin (linksFullLit.getD l []).length) :
    noK10 (P5J.At.seats Zp) (linksFullLit.getD l []) (P5J.At.pseats Zp) l i <
      sentAtK10W.getD l 0 := by
  have e1 : P5J.At.pseats Zp = P5T.psFull := L.seats hW
  have e2 : P5J.At.seats Zp = seatsFullW := by
    unfold P5J.At.seats seatsFullW
    rw [e1]
  rw [e1, e2]
  exact of_decide_eq_true (List.all_eq_true.1
    (List.all_eq_true.1 below_written l (List.mem_range.2 hl)) i (List.mem_finRange i))

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.below_written
#print axioms VerifiableInference.Desc.LinkJoin.below_written_tight
#print axioms VerifiableInference.Desc.LinkJoin.ld_at_laid
#print axioms VerifiableInference.Desc.LinkJoin.seed_public_laid
#print axioms VerifiableInference.Desc.LinkJoin.below_laid
#print axioms VerifiableInference.Desc.LinkJoin.places_apart_W
#print axioms VerifiableInference.Desc.LinkJoin.seats_are_places_W
#print axioms VerifiableInference.Desc.LinkJoin.booked_written
#print axioms VerifiableInference.Desc.LinkJoin.booked_written_next
