-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/PadsDoor.lean: a cheap public test: NO ELEMENT OF A MATRIX THAT ONE SEGMENT READS
FROM AN EARLIER SEGMENT's ORACLE MESSAGE LIES AT A PLACE OF A PAD (the mask on an OOD answer),
whether in the oracle message as the owning segment sends it or as the reading segment sends it
again. At plain public arguments. Definitions with code only. No Mathlib. Meant for an entry of the
verifier's list of public tests (lawsAsk, Johnson/Desc/Laid/ProofAsks.lean).

The arguments.
  cs, layout, num, arr, mems   as in Johnson/Desc/Kinds/PlanK6Door.lean.
  labs k a   the label of matrix number a of segment k's list.
  group k    the sampled oracle messages of segment k, each as (tree, tenant).
  iXI        the number, in a layers' segment's list, of the matrix that it reads from the segment
          before.
  nas g      in the attention segment of group g that matrix has the number nas g + 3.
  NHf        in the output head's segment it has the number NHf + 3.

Main names.
  copyThereP    an oracle message of segment k has the number n.
  copiesMissP   every oracle message of segment k with the number n has a shape at which the array
          misses the pad (Law/LaidOffPad.lean: missB, rectangle by rectangle).
  padFreeP      at one pair of a reading segment k and an owning segment k': the layout holds the
          array that the label names; in both segments an oracle message has its message's number;
          and copiesMissP holds of it in both.
  padsDoor      THE TEST: at the 24 pairs of the full size's 25 segments.

Not claimed here. No theorem. What acceptance implies: Law/PadsDoorLaw.lean (padsFree_of_door).
Which terms are passed for the arguments is not said here. The full size only: the 24 pairs are
literals. Nothing on soundness.

-/
import Johnson.Desc.Kinds.PlanK6Door

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open OnBytes.Params (ReqArray ReqLayout)

section
variable (cs : OnBytes.Codes) (layout : ReqLayout) (labs : Nat → Nat → Nat)
  (num arr : Nat → Nat → Nat) (group : Nat → List (Nat × Nat))
  (mems : List (OnBytes.OracleShape × (Nat × Nat)))

/-- An oracle message of segment k has the number n. -/
def copyThereP (k n : Nat) : Bool :=
  mems.any fun y => (group k).contains y.2 && Decidable.decide (arr y.2.1 y.2.2 = n)

/-- Every oracle message of segment k with the number n has a shape at which A misses the pad. -/
def copiesMissP (k n : Nat) (A : ReqArray) : Bool :=
  mems.all fun y => !((group k).contains y.2 && Decidable.decide (arr y.2.1 y.2.2 = n)) ||
    missB cs y.1 A

/-- The test at one pair. -/
def padFreeP (k k' a : Nat) : Bool :=
  match VerifiableInference.Desc.arrayOf layout (ownerP (labs k a)).1 (ownerP (labs k a)).2 with
  | none => false
  | some A =>
    copyThereP arr group mems k (num (ownerP (labs k a)).1 A.message) &&
      copyThereP arr group mems k' (num (ownerP (labs k a)).1 A.message) &&
      copiesMissP cs arr group mems k (num (ownerP (labs k a)).1 A.message) A &&
      copiesMissP cs arr group mems k' (num (ownerP (labs k a)).1 A.message) A

/-- **The test.** -/
def padsDoor (iXI : Nat) (nas : Nat → Nat) (NHf : Nat) : Bool :=
  ((List.range 12).all fun g =>
      (g == 0 || padFreeP cs layout labs num arr group mems (2 * g) (2 * (g - 1)) iXI) &&
      padFreeP cs layout labs num arr group mems (2 * g + 1) (2 * g) (nas g + 3)) &&
    padFreeP cs layout labs num arr group mems 24 22 (NHf + 3)

end

end VerifiableInference.Desc.Kinds.Head.Law.OffPad
