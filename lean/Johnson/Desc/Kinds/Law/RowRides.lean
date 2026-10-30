-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/RowRides.lean: THE OUTPUT HEAD's ROW OF THE TABLE OF JOINTS, WITH THE 17 ROW FORMS (idn · the two sums · keys and rider in our own words; planes on neither side; join not among the outs), FROM THE DECISION OF THE BLOCK AS IT RIDES: blockOf W l (Johnson/Stored/HeadSeatAt.lean):
the block that is made of the public record W which the program makes of the public files: its shape, its number of the reads'
array and its bits of work READ OFF W: no letter of ours is left free but the cells and the mask row: STATED AND PROVED; under the
rule cut at the tight ceiling (Law/RowPrice.lean), in the very form of a rule that the bridge from a kind's rule to a block's errors types
(Johnson/Desc/Sound/RuleForm.lean: Sound.NoBad).
WHAT IT DOES NOT SAY. c AND mask ARE LETTERS UNDER "FOR ALL", TIED HERE TO NOTHING THAT IS FIXED IN FRONT OF THE DRAWS: the law is meant to be spent at the
witness's components that are pinned in front of the block's first draw (the table of joints: pin 4 0, pinW): THAT INSTANCE IS THE CALLER's, AND IS NOWHERE YET; whoever
may pick mask behind the draws makes every hidden scalar what they like. At parOf, before := []: the block's own test that the messages with the cells precede its first draw is idle at this seat. rs IS WHAT decide IS SHOWN (no sealed digest): that these are the rounds of the written reading is another file's equation (Johnson/Desc/Sound/ShownRounds.lean).
All that Law/RowAtSeat.lean and Law/RowPrice.lean do not say: Opened is a premise; WellLaid, the tests on the plan
and the request, 0 < d, y < V, Canonical are premises; no written challenge is counted; that the ceiling's numbers are the plan's
prices is not shown here; no honest run is shown to meet the premises.
  RowPriceAtSeatStatement · rowPriceAtSeat   Law/RowPrice.lean's law at seatAt h iU3 and parOf h work: no premise on the seat.
  readsOf W, workOf W      the two numbers that blockOf reads off W (0 where the plan names no array of reads: there blockOf
                           returns nothing, and the law is not asked).
  RowRidesStatement · rowRides   blockOf W l = some b: the row of b.decide.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RowPrice
import Johnson.Desc.Kinds.Law.RowAtSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open Sound (cutTo strikeLast)
open VerifiableInference.Desc.First (S)

/-- **K6's ROW AT THE REAL SEAT, UNDER THE RULE CUT AT THE TIGHT CEILING.** -/
def RowPriceAtSeatStatement : Prop :=
  ∀ (h : OnBytes.Model.Head.Shape) (iU3 work l : Nat) (s : S) (c : NCells)
    (mask : Nat → E) (s' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
    (blockAt h iU3 work l).decide s rs gs = .ok s' → WellLaid ((seatAt h iU3).ledger s) →
    (parOf h work).ok = true → hasFeatures (parOf h work) →
    (parOf h work).okStart ((seatAt h iU3).request s) = true →
    (∀ y, Reply.token (seatAt h iU3).toSeat s = some y → y < (parOf h work).sizes.V) →
    Canonical rs → Sound.NoBad (ruleK6T (parOf h work) (seatAt h iU3) s c mask) rs →
    Opened (parOf h work) (seatAt h iU3) s' c mask →
    ClosedWhole (parOf h work) (seatAt h iU3) s' c mask

/-- The number of the reads' array, and the bits of work, as blockOf reads them off the public record. -/
def readsOf (W : OnBytes.Model.Verify.Public) : Nat := (W.H.tl.ix.U.getD 2 none).getD 0
@[inherit_doc readsOf] def workOf (W : OnBytes.Model.Verify.Public) : Nat :=
  (OnBytes.Params.settingOf W.P.frame).workOf .field .request

/-- **K6's ROW OF THE BLOCK AS IT RIDES.** -/
def RowRidesStatement : Prop :=
  ∀ (W : OnBytes.Model.Verify.Public) (l : Nat) (b : Block S Unit), blockOf W l = some b →
    ∀ (s : S) (c : NCells) (mask : Nat → E) (s' : S) (rs : List Fmt.RoundView)
      (gs : List (List (Nat × List UInt64))),
    b.decide s rs gs = .ok s' → WellLaid ((seatAt W.hS (readsOf W)).ledger s) →
    (parOf W.hS (workOf W)).ok = true → hasFeatures (parOf W.hS (workOf W)) →
    (parOf W.hS (workOf W)).okStart ((seatAt W.hS (readsOf W)).request s) = true →
    (∀ y, Reply.token (seatAt W.hS (readsOf W)).toSeat s = some y →
      y < (parOf W.hS (workOf W)).sizes.V) →
    Canonical rs → Sound.NoBad (ruleK6T (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s c mask) rs →
    Opened (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s' c mask →
    ClosedWhole (parOf W.hS (workOf W)) (seatAt W.hS (readsOf W)) s' c mask

namespace Came

theorem rowPriceAtSeat : RowPriceAtSeatStatement := by
  intro h iU3 work l s c mask s' rs gs hd hWL hplan hd0 hreq hy hcan hnb hopen
  exact rowPrice S Unit (fun _ => ()) (seatAt h iU3) l 4 (parOf h work) s c mask s' rs gs hd
    ((seatBack_iff _ _ _).2 (seatBack_at h iU3 work s)) hWL hplan hd0 hreq hy hcan hnb hopen

theorem rowRides : RowRidesStatement := by
  intro W l b hb s c mask s' rs gs hd
  unfold blockOf at hb
  cases hU : W.H.tl.ix.U.getD 2 none with
  | none =>
    rw [hU] at hb
    simp at hb
  | some i =>
    rw [hU] at hb
    simp only [Option.map_some, Option.some.injEq] at hb
    subst hb
    have e : readsOf W = i := by
      unfold readsOf
      rw [hU]
      rfl
    rw [e]
    exact rowPriceAtSeat W.hS i (workOf W) l s c mask s' rs gs hd

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rowPriceAtSeat
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rowRides
