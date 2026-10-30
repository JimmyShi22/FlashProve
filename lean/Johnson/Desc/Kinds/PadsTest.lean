-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/PadsTest.lean: the cheap public test on the pads
(Johnson/Desc/Kinds/PadsDoor.lean: padsDoor) AS A FUNCTION OF A SMALL PLAIN STRUCTURE OF NUMBERS.
Definitions with code only. It imports Johnson/Desc/Kinds/PlanK6Test.lean (for ArrV), which imports
nothing.

Main names.
  PMemV     what the test reads of a sampled oracle message: the segments to which it belongs; its
          number; its main rows and mask rows; 1 or 3 (its main rows' field); its main code's
          message length.
  PadsView  all that the test reads: the pairs (reading segment, owning segment, the array if the
          layout holds it) and the oracle messages.
  thereV, missV   an oracle message of segment k has the number n; every such one has a shape at
          which the array misses the pad (the mask on an OOD answer).
  padsV v   THE TEST.

Not claimed here. No theorem. That it is padsDoor at the view of that test's arguments:
Law/PadsView.lean (padsDoor_eq). Nothing on soundness.

-/
import Johnson.Desc.Kinds.PlanK6Test

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

/-- What the test reads of a sampled oracle message. -/
structure PMemV where
  segs : List Nat
  num : Nat
  mainRows : Nat
  maskRows : Nat
  mainDeg : Nat
  ell : Nat
  deriving DecidableEq, Repr

/-- All that the test reads. -/
structure PadsView where
  pairs : List (Nat × Nat × Option ArrV)
  mems : List PMemV
  deriving DecidableEq, Repr

/-- An oracle message of segment k has the number n. -/
def thereV (v : PadsView) (k n : Nat) : Bool :=
  v.mems.any fun y => y.segs.contains k && Decidable.decide (y.num = n)

/-- The array misses the pad at this oracle message's shape. -/
def missAtV (A : ArrV) (y : PMemV) : Bool :=
  y.maskRows != 0 || A.ends.all fun e =>
    Decidable.decide (e.1 + 1 < y.mainRows) ||
      Decidable.decide (e.2 + (if y.mainDeg = 3 then 1 else 3) < y.ell)

/-- Every oracle message of segment k with the array's message's number: the array misses its pad.
-/
def missV (v : PadsView) (k : Nat) (A : ArrV) : Bool :=
  v.mems.all fun y => !(y.segs.contains k && Decidable.decide (y.num = A.num)) || missAtV A y

/-- The test at one pair. -/
def pairV (v : PadsView) (x : Nat × Nat × Option ArrV) : Bool :=
  match x.2.2 with
  | none => false
  | some A => thereV v x.1 A.num && thereV v x.2.1 A.num && missV v x.1 A && missV v x.2.1 A

/-- **The test.** -/
def padsV (v : PadsView) : Bool := v.pairs.all (pairV v)

end VerifiableInference.Desc.Kinds.Head.Law.OffPad
