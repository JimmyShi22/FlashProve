-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K6/Law/SpendsWritten.lean: THE OUTPUT HEAD's OWN SUB-PROTOCOL (K6):
WHAT ITS EIGHT PARTS STATE THAT THEY TAKE AND SPEND, WRITTEN OUT: NAMES, ORDER, COUNTS: general in
the place's public numbers, and in numerals under the hypothesis h (`P5J.AtMgA`,
Johnson/P5J/MgAtAll.lean). No definition; six theorems.

  `k6_takes_closed`     no part takes a coin of its own
  `k6_slots_replicate`  a helper: n variables of three coefficients add two a variable
  `k6_ownRun_point`     the first run of a call in n variables at points: lead + (2 n + 3) entries
  `k6_spends_closed`    the eight lists of stated runs, side by side
  `k6_spends_at_head`   under h: 9 · 49 and 2 · 7 · 24 and 4 · 24 and 2 · 50 and 2: 173 in all
  `k6_no_seed`          a closed fact: none of the 82 rounds at the full size is named "SEND seed"

Why. The frame lends a part its coins where three public lists of the part (takes, spends, carries)
are the book's at the part's address. The third is Honest/K6/Law/CarriesNone.lean. These are the
first two, ON THE PARTS' SIDE.

What it is not.
  * THE BOOK's SIDE IS NOT HERE: that a book's table has no row at one of K6's eight addresses, or
    that its entries there bear these names and counts in this order, is not said.
  * THAT ANY BOOK LENDS THE ROW IS NOT SAID.
  * `k6_no_seed` speaks of names at two written logarithms (10 and 13): that a book's table has a
    row only where a round of that name stands is a law on the book's maker, which is not here.
  * Counts and names: nothing on a value, a coin or a run.
  * h: the full size and the format's second hash function alone.
  * Modules under lean/Johnson/Goal/ lie in its import closure.
  * Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K6.Part
import Johnson.Desc.ProofFile.Honest.K6.GoodRounds
import Johnson.Desc.Kinds.Law.K6PubInScope
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K6

open OnBytes (zeroE)
open VerifiableInference.Desc (Chain Place)
open VerifiableInference.Desc.Part.MaskedSum (Var)
open VerifiableInference.Desc.Kinds (Head.Par Head.parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (numbers_in_scope)
open OnBytes.Maker (WholeD)

/-- GENERAL. No part of K6's row takes a coin of its own. -/
theorem k6_takes_closed (p : Head.Par) (at_ : Place) :
    (headParts p at_).map (·.takes) = List.replicate 8 ⟨0, 0⟩ := rfl

/-- n variables of three coefficients add two a variable. -/
theorem k6_slots_replicate (n a : Nat) :
    (List.replicate n (Var.point zeroE 3)).foldl (fun m v => m + (v.d - 1)) a = a + 2 * n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, List.foldl_cons, ih]
    show a + (3 - 1) + 2 * n = a + 2 * (n + 1)
    omega

/-- GENERAL. The first run of a call in n variables at points: the lead, two coefficients a
variable, three more. -/
theorem k6_ownRun_point (lead n ends : Nat) :
    ownRun (pointShape lead n ends) = lead + (2 * n + 3) := by
  show lead + (List.replicate n (Var.point zeroE 3) ++ [Var.point zeroE (2 + 1)]).foldl
    (fun m v => m + (v.d - 1)) 1 = lead + (2 * n + 3)
  rw [List.foldl_append, k6_slots_replicate]
  show lead + (1 + 2 * n + (2 + 1 - 1)) = lead + (2 * n + 3)
  omega

/-- GENERAL. **WHAT THE EIGHT PARTS STATE THAT THEY SPEND, SIDE BY SIDE: NAMES, ORDER, COUNTS.** -/
theorem k6_spends_closed (p : Head.Par) (at_ : Place) :
    (headParts p at_).map (·.spends) =
      [[], [(headRunName at_ 1 "scalars", ⟨0, 9⟩)],
       [(headRunName at_ 2 "sum", ⟨0, 0 + (2 * (headLPd p + headLt p) + 3)⟩),
        (headRunName at_ 2 "ends", ⟨0, 2⟩)],
       [], [(headRunName at_ 4 "scalars", ⟨0, 7⟩)],
       [(headRunName at_ 5 "sum", ⟨0, 1 + (2 * headLt p + 3)⟩),
        (headRunName at_ 5 "ends", ⟨0, 4⟩)],
       [(headRunName at_ 6 "sum", ⟨0, 1 + (2 * headLt p + 3)⟩),
        (headRunName at_ 6 "ends", ⟨0, 2⟩)],
       [(headRunName at_ 7 "sum", ⟨0, 1 + (2 * (headLt p + headLPd p) + 3)⟩),
        (headRunName at_ 7 "ends", ⟨0, 2⟩)]] := by
  rw [← k6_ownRun_point 0 (headLPd p + headLt p) 2, ← k6_ownRun_point 1 (headLt p) 4,
    ← k6_ownRun_point 1 (headLt p + headLPd p) 2]
  rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- CONDITIONAL: the hypothesis h. **THE SAME AT THE HEAD's PUBLIC NUMBERS, IN NUMERALS.** -/
theorem k6_spends_at_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (at_ : Place) :
    (headParts (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) at_).map (·.spends) =
      [[], [(headRunName at_ 1 "scalars", ⟨0, 9⟩)],
       [(headRunName at_ 2 "sum", ⟨0, 49⟩), (headRunName at_ 2 "ends", ⟨0, 2⟩)],
       [], [(headRunName at_ 4 "scalars", ⟨0, 7⟩)],
       [(headRunName at_ 5 "sum", ⟨0, 24⟩), (headRunName at_ 5 "ends", ⟨0, 4⟩)],
       [(headRunName at_ 6 "sum", ⟨0, 24⟩), (headRunName at_ 6 "ends", ⟨0, 2⟩)],
       [(headRunName at_ 7 "sum", ⟨0, 50⟩), (headRunName at_ 7 "ends", ⟨0, 2⟩)]] := by
  have N := numbers_in_scope h.scope h.reads h.pubOne
  have hlt : headLt (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) = 10 := N.lt
  have hlP : headLPd (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) = 13 := by
    show OnBytes.Model.clog2 (P5J.At.X Zp).hS.d = 13
    rw [N.d]
    decide
  have e := k6_spends_closed (Head.parOf (P5J.At.X Zp).hS (workOf (P5J.At.X Zp))) at_
  rw [hlt, hlP] at e
  exact e

set_option maxRecDepth 100000 in
/-- A CLOSED FACT, BY LEAN's KERNEL. None of K6's 82 rounds at the full size is named
"SEND seed". -/
theorem k6_no_seed : ((headRoundsOf 10 13).all fun r => r.name != "SEND seed") = true := by
  decide +kernel

end ProofFile.Honest.K6

#print axioms ProofFile.Honest.K6.k6_takes_closed
#print axioms ProofFile.Honest.K6.k6_slots_replicate
#print axioms ProofFile.Honest.K6.k6_ownRun_point
#print axioms ProofFile.Honest.K6.k6_spends_closed
#print axioms ProofFile.Honest.K6.k6_spends_at_head
#print axioms ProofFile.Honest.K6.k6_no_seed
