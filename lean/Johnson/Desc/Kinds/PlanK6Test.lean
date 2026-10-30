-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/PlanK6Test.lean: a cheap public test for the output head's own rounds (kind K6),
as a function of a small plain structure of numbers. Definitions with code only. THIS FILE IMPORTS
NOTHING.

What the test checks, in words. Take each matrix of the output head's list that the head's own rule
reads. The request's layout must hold an array for it. Exactly one sampled oracle message of the
head's segment must carry the number of the message that holds the array. That oracle message must
be sent in the segment's first sending. Every rectangle of the array must end inside the oracle
message's main rows. The same is checked for those entries of the mask row that are in use.

Main names.
  MemV   what the test reads of a sampled oracle message: whether it belongs to segment 24 (the
         output head's); whether it is sent in that segment's first sending; its number; its main
         rows and mask rows; the message lengths of its two codes.
  ArrV   what it reads of an array: the number of the message that holds it; the last row and the
         last place of each of its rectangles.
  View   all that it reads: two numbers, the arrays, the numbers of the segment's oracle messages,
         and the oracle messages.
  planK6V v n rb   THE TEST. n: the number of the message that holds the mask row. rb: the logarithm
          of the number of mask rows over which the entries are spread.

Not claimed here. No theorem. What acceptance implies is proved in Law/PlanK6View.lean (planK6C_eq)
and Law/PlanK6ByBlocks.lean (planK6_of_C). Nothing on soundness.

-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

/-- What the test reads of a sampled oracle message: whether it belongs to segment 24; whether it is
sent in that segment's first sending; its number; its rows; its two codes' message lengths. -/
structure MemV where
  inGroup : Bool
  atZero : Bool
  num : Nat
  mainRows : Nat
  maskRows : Nat
  ellMain : Nat
  ellMask : Nat
  deriving DecidableEq, Repr

/-- What it reads of an array: its message's number; each rectangle's last row and last place. -/
structure ArrV where
  num : Nat
  ends : List (Nat × Nat)
  deriving DecidableEq, Repr

/-- All that the test reads. -/
structure View where
  NHf : Nat
  ns : Nat
  /-- for each matrix of the head's list: its number in the list, and its array if there is one -/
  arrs : List (Nat × Option ArrV)
  /-- the numbers of segment 24's sampled oracle messages -/
  groupNums : List Nat
  mems : List MemV
  deriving DecidableEq, Repr

/-- Exactly one of the segment's oracle messages has the number k. -/
def onceV (v : View) (k : Nat) : Bool := (v.groupNums.filter fun x => x == k).length == 1

/-- An oracle message of the segment has the number k; each one that does is sent in the segment's
first sending and passes ok. -/
def copyV (v : View) (k : Nat) (ok : MemV → Bool) : Bool :=
  (v.mems.any fun y => y.inGroup && Decidable.decide (y.num = k)) &&
    v.mems.all fun y => !(y.inGroup && Decidable.decide (y.num = k)) || (y.atZero && ok y)

/-- Every rectangle of the array ends inside the oracle message's main rows. -/
def insideV (A : ArrV) (y : MemV) : Bool :=
  A.ends.all fun e => Decidable.decide (e.1 < y.mainRows) && Decidable.decide (e.2 < y.ellMain)

/-- The oracle message's mask rows have room for ns entries, spread over 2 ^ rb rows. -/
def maskV (ns rb : Nat) (y : MemV) : Bool :=
  Decidable.decide (2 ^ rb ≤ y.maskRows) &&
    (ns == 0 || Decidable.decide ((ns - 1) / 2 ^ rb < y.ellMask))

/-- The test at one matrix. -/
def matV (v : View) : Option ArrV → Bool
  | none => false
  | some A => onceV v A.num && copyV v A.num (insideV A)

/-- **The test.** -/
def planK6V (v : View) (n rb : Nat) : Bool :=
  (v.arrs.all fun x =>
      x.1 == v.NHf + 2 || Decidable.decide (v.NHf + 3 < x.1) || matV v x.2) &&
    onceV v n && copyV v n (maskV v.ns rb)

end VerifiableInference.Desc.Kinds.Head.Law.OffPad
