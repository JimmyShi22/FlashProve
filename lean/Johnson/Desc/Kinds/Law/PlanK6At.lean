-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PlanK6At.lean: THE LETTERS s, seat AND pl OF THE OUTPUT HEAD'S READING
(Law/K6Cut.lean: compCut, PlanK6) AS TERMS: a candidate filling off the plan.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law).
  plAt n rb j: THE PLACE OF ENTRY j OF THE HEAD'S LINK'S MASK ROW: message number n, among that
      member's pad's places, row j mod 2 ^ rb, place j div 2 ^ rb. MEANT: n: the number of the
      link's first own message with mask rows; rb: the bits of its number of mask rows. (So other
      files' reader of the forms seats that entry, by report and by their texts.)
  seatLay Wp layout num: the seats of the symbols: another file's Meaning.seatBy
      (Meaning.fLay layout num) at its sizes Meaning.sizesOf Wp
      (Johnson/Goal/Meaning/HidSeatsOf.lean, HidPlan.lean).
  PlanK6At ...: PlanK6 at these three terms.
  follows_at: its clause "follows", from follows_sizesOf, where each plan's record has as
      its number of matrices the length of its list (nmFit).

Every letter under "there is": none.
What it does not say. THAT PlanK6At HOLDS ANYWHERE: "made" is by make at the maker's value;
"follows" is follows_at; the four others (named, seats, maskNamed, maskIn) HAVE BEEN EVALUATED TRUE
AT BOTH STORED PLANS ON SHEETS (files of evaluations, not named here), UNDER RIDERS: over plain pairs and by blocks, not as
these Props; at the sheets' own fillings of seat and pl (that the sheet's seat is seatLay: not yet
held by a run; its pl is plAt at n := the message's number, rb := 0); no theorem. cs, arr, msR, N,
layout, num, n, rb stay letters. Nothing on soundness.
-/
import Johnson.Goal.Meaning.HidSeatsOf
import Johnson.Desc.Kinds.Law.K6Cut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem)

/-- **The place of entry j of the head's link's mask row.** -/
def plAt (n rb j : Nat) : Nat × Bool × Nat × Nat := (n, true, j % 2 ^ rb, j / 2 ^ rb)

/-- **The seats of the symbols**, off the layout. -/
def seatLay (Wp : OnBytes.Model.Verify.Public) (layout : OnBytes.Params.ReqLayout)
    (num : Nat → Nat → Nat) :
    ∀ k, Fin (Meaning.sizesOf Wp k).NM → Nat → Nat → Nat × Nat × Nat :=
  Meaning.seatBy (Meaning.fLay layout num) Wp (Meaning.sizesOf Wp)

/-- **The conditions on the public letters, at the three terms.** -/
def PlanK6At (cs : OnBytes.Codes) (arr : Nat → Nat → Nat) (msR : List Mem) (N : Numbers)
    (Wp : OnBytes.Model.Verify.Public) (layout : OnBytes.Params.ReqLayout) (num : Nat → Nat → Nat)
    (n rb : Nat) : Prop :=
  PlanK6 cs arr msR N (Meaning.sizesOf Wp) (seatLay Wp layout num) Wp (plAt n rb)

/-- The clause "follows". -/
theorem follows_at {Wp : OnBytes.Model.Verify.Public} (h : Meaning.nmFit Wp = true) :
    Meaning.Follows Wp (Meaning.sizesOf Wp) := Meaning.follows_sizesOf h

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.follows_at
