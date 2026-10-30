-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/WrittenMeets.lean: the code switch at its WRITTEN rounds: the block's rounds
have the shape of the plan's two entries, and each of the block's two counts, times the sampler's
weight, is a share of at most 2⁻¹ ^ target of the written round's verifier messages, test bits
among them.

Level.lean bounds the two counts as shares of the TYPED values, work aside. LevelWritten.lean lays
the bits of work among the challenges, still over typed values. Here the written rounds are the
format's own (`wRound d`, OnBytes/Slice/Draws.lean): a verifier message is a string of hash blocks
and test bits, of which the format's sampler makes the typed value. Both things that stood between
Level.lean and the written rounds are paid, by the planner's own yes (`roundHolds`), through the
library's `held_round` (MeetsOfCovered.lean).

WHERE THE BITS COME FROM. The planner's test says of a round: its error, with a term for the
distance from uniform of the field elements that it draws, is at most 2 ^ (work - target). At the 5
and the 25 written records the target is 128 and the two rounds' bits of work are 0 and 20
(Level.lean: `small_works`, `full_works`). So there SEND seed, which draws field elements, is at
most 2 ^ -128 without work, the planner's term for the bias counted in; and LOC, which draws
positions alone and has no such term, is at most 2 ^ -108 as a share of its typed values, and the
other 20 bits are work, counted as the written round counts it (OnBytes/Slice/HeldRound.lean says
how).

Main names:
  `SwRow.writtenOK`: the planner's test and the two side conditions at the record's two rounds
    (`fineB`), and: the sending has a tree.
  `Letters.shape`: the block's shape has the rounds of the plan's two entries (`ShapeIsAll`,
    OnBytes/G4/RoundIsAll.lean; `sendLoc_shape`).
  `Letters.writtenBelow`: `Err.Below` of the two written counts (the library's `Held.cnts`) at
    2⁻¹ ^ target, for all letters and all written rounds with the plan's two entries and a kind
    other than a sealing (`WrittenAs`).
  `SwRow.wrAt`, `wrAt_fits`: written rounds with the plan's two entries exist: a poor member (the
    kind elems, no item, no tree).
  `K02Written`, `k02Written`: shape and bound as one closed proposition, at every record at which
    both tests say yes; its proof.

Limits: those of MeetsOfCovered.lean and of Row.lean. The written rounds are letters with the plan's
entries: that a file's chain has such rounds at a switch's place is not shown. That the written
counts bear the typed ones wants maps from written to typed messages at which at most w written
messages are read as one typed value (`Held.fits_cnts`, OnBytes/Flat/CountsHeld.lean;
OnBytes/Tie/Pv/Switch/SendLocCarry.lean: `carry_fib`): not called here. That work is worth its bits
is not said. A bound on each round, not on a sum over rounds. Nothing on soundness of the protocol.
On hiding nothing.
That the test says yes at the 5 and the 25 written records: WrittenLit.lean.

-/
import Johnson.Top.H0.K2Caller.Level
import Johnson.Top.H0.K2Caller.MeetsOfCovered

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan OnBytes.G4 Cb Iop IOR Johnson.Top.H
open OnBytes.Tie.Pv.Switch
open _root_.Run (PQ.RD ckP)
open _root_.Run.PQ (uL)
open scoped ENNReal

/-- The planner's test and the side conditions at the record's two rounds; the sending has a tree.
-/
def SwRow.writtenOK (r : SwRow) : Bool :=
  (r.specs.all fun y => fineB r.set .request y) && decide (r.roots ≠ 0)

/-- **The block's shape has the rounds of the plan's two entries.** -/
theorem Letters.shape (F : Type) {r : SwRow} {H : r.OK} (X : Letters r H) (hr : r.roots ≠ 0) :
    ShapeIsAll GE F (Cb.Pv.SendLocRide.R X.caller).shape
      (r.specs.map fun y => (y.round r.set .request).entry) :=
  sendLoc_shape X.caller F r.set .request r.o r.roots r.g hr
    (switchVec_fits _ _ _ _ _ _ _ _ _ _ _
      (callerOf_fits r H X.t₀ X.oM X.oZ X.kq X.Sb X.sl X.Z X.A₀ X.cutN X.w₀))

theorem p_is : Fmt.Fld.two.p = 2 ^ 64 - 2 ^ 32 + 1 := by decide +kernel

/-- **The two written counts are shares of at most 2⁻¹ ^ target.** -/
theorem Letters.writtenBelow (F : Type) {r : SwRow} (h : r.ok = true) (hW : r.writtenOK = true)
    (X : Letters r (r.ok_says h)) (ds : List PQ.RD) (hd : WrittenAs r.set .request ds r.specs) :
    Err.Below (OnBytes.Flat.Held.cnts (uL (ckP .two) ds) (OnBytes.Flat.Held.wsOf ds (allRead ds))
      (Cb.Pv.SendLocRide.R X.caller).shape (Cb.Pv.SendLocRide.eps X.caller))
      ((2 : ℝ≥0∞)⁻¹ ^ r.set.target) := by
  unfold SwRow.writtenOK at hW
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hW
  exact written_below r.set .request F ((r.ok_says h).p.trans p_is) (r.ok_says h).degree _ _ r.specs
    ds
    (X.shape F hW.2) (Letters.holds h X).2 hd fun y hy => fine_of (hW.1 y hy)

/-- Written rounds with the plan's two entries: a poor member. -/
def SwRow.wrAt (r : SwRow) : List PQ.RD :=
  r.specs.map fun y => ⟨(y.round r.set .request).entry, .elems, [], none, []⟩

theorem wrAt_fits (r : SwRow) : WrittenAs r.set .request r.wrAt r.specs :=
  List.forall₂_map_left_iff.2 (List.forall₂_same.2 fun _ _ =>
    ⟨rfl, (by decide : Fmt.Kind.elems ≠ Fmt.Kind.sealed)⟩)

/-- **The row on the rounds, as one closed proposition.** -/
def K02Written : Prop :=
  ∀ (F : Type) (r : SwRow) (h : r.ok = true), r.writtenOK = true →
    ∀ (X : Letters r (r.ok_says h)),
      ShapeIsAll GE F (Cb.Pv.SendLocRide.R X.caller).shape
        (r.specs.map fun y => (y.round r.set .request).entry) ∧
      ∀ ds : List PQ.RD, WrittenAs r.set .request ds r.specs →
        Err.Below (OnBytes.Flat.Held.cnts (uL (ckP .two) ds)
          (OnBytes.Flat.Held.wsOf ds (allRead ds)) (Cb.Pv.SendLocRide.R X.caller).shape
          (Cb.Pv.SendLocRide.eps X.caller)) ((2 : ℝ≥0∞)⁻¹ ^ r.set.target)

theorem k02Written : K02Written := fun F r h hW X =>
  ⟨X.shape F (by
      unfold SwRow.writtenOK at hW
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hW
      exact hW.2),
    fun ds hd => Letters.writtenBelow F h hW X ds hd⟩

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.Letters.shape
#print axioms VerifiableInference.Desc.First.K2Caller.Letters.writtenBelow
#print axioms VerifiableInference.Desc.First.K2Caller.wrAt_fits
#print axioms VerifiableInference.Desc.First.K2Caller.k02Written
