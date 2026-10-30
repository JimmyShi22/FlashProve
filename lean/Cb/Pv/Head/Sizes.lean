-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/Sizes.lean: the sizes at which the output head's sub-proof runs its blocks, as written
lists.

The head's sub-proof is the last link of a request's first chain. Behind its lookup it draws a point
over the positions, and it runs five sumchecks that are written by hand. This file lists, for two
example configurations (prover/examples/target_small_f2: 64 positions; target_full_f2: 1,024
positions), the numbers from which the planner makes these rounds, each sumcheck with its place,
its slots and its sizes, and every other round of the sub-proof behind its two lookups.

The source. The lists were written by a program from a print of the rounds that the verifier's own
planner makes from the two examples' public files. The tests in
OnBytes/Tie/Pv/Plan/TestPlanSizesSmall.lean and
OnBytes/Tie/Pv/Plan/TestPlanSizesFull.lean compute them anew and compare.

The plan's bounds. E is the extension field. The round before a sumcheck's first challenge and the
round LINE have the bound 1 / |E|. The round of a variable that sends n scalars has n / |E|. The
round in the further variable, which sends inY scalars, has inY / (|E| - 1). The round of the end
values has no challenge. A round ZERO that draws n elements has n / |E|. A round BAT-sigma that
batches n rows has (n - 1) / |E|. The tests compare these with the planner's numbers. In both
examples no proof of work is asked in these rounds.

Main definitions: HeadSize, headSizes, PscAt, atSquares, atTV, atTN, atTH, atMerge, OtherAt, others.
What is not claimed: that a bound bounds anything. No theorem is stated. This file imports nothing.

-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head

/-- The numbers from which the planner makes the head's own rounds. -/
structure HeadSize where
  /-- the full-size example; false: the small one -/
  full : Bool
  /-- bits of a position -/
  lt : Nat
  /-- bits of a feature, padded -/
  lPd : Nat
  /-- bits of a column of the committed weights -/
  lkW : Nat
  /-- of the norm: sums of limb products -/
  sums : Nat
  /-- of the norm: row products -/
  products : Nat
  /-- of the norm: row values in the row products -/
  rowValues : Nat
  /-- what the last round batches -/
  rows : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The head's numbers. Length 2: one member for each example. -/
def headSizes : List HeadSize :=
  [{ full := false, lt := 6, lPd := 9, lkW := 11, sums := 9, products := 7,
     rowValues := 4, rows := 2712833 },
   { full := true, lt := 10, lPd := 13, lkW := 18, sums := 9, products := 7,
     rowValues := 4, rows := 24653737 }]

/-- A sumcheck at its place in the plan. -/
structure PscAt where
  /-- the full-size example; false: the small one -/
  full : Bool
  /-- the number of the head's link in the chain -/
  link : Nat
  /-- the moment of the link behind which the sumcheck stands -/
  moment : Nat
  /-- the place of the sumcheck's first round in the list of the sub-proof's rounds behind that
  moment, counted from 0, the lookup's rounds counted -/
  place : Nat
  /-- the place of that round in the plan of the proof's first chain, counted from 0 -/
  chain : Nat
  /-- the slot of the first scalar of the sumcheck's first message: how many scalars the sub-proof
  has sent before it -/
  slot : Nat
  /-- the scalars that this message holds beside the hiding sum, and before it -/
  riders : Nat
  /-- for each variable, in the order of the rounds: the scalars that its round sends -/
  sent : List Nat
  /-- the scalars of the round in the further variable -/
  inY : Nat
  /-- the end values -/
  values : Nat
  /-- a round that draws the point of a line follows the end values -/
  line : Bool
  deriving DecidableEq, Repr, Inhabited

/-- The slot of the hiding sum. -/
def PscAt.slotSum (x : PscAt) : Nat := x.slot + x.riders

/-- The slot of the first end value. -/
def PscAt.slotEnd (x : PscAt) : Nat := x.slotSum + 1 + x.sent.foldl (· + ·) 0 + x.inY

/-- The places of the sum of squares: a product layer, which is a sumcheck over the features and the
positions and then the point of a line.
Length 2: one place in each example. -/
def atSquares : List PscAt :=
  [{ full := false, link := 4, moment := 0, place := 838, chain := 7247,
     slot := 1540, riders := 0, sent := List.replicate 15 2, inY := 2,
     values := 2, line := true },
   { full := true, link := 24, moment := 0, place := 1082, chain := 47371,
     slot := 2004, riders := 0, sent := List.replicate 23 2, inY := 2,
     values := 2, line := true }]

/-- The places of the token sumcheck of the row products.
Length 2: one place in each example. -/
def atTV : List PscAt :=
  [{ full := false, link := 4, moment := 0, place := 858, chain := 7267,
     slot := 1582, riders := 1, sent := List.replicate 6 2, inY := 2,
     values := 4, line := false },
   { full := true, link := 24, moment := 0, place := 1110, chain := 47399,
     slot := 2062, riders := 1, sent := List.replicate 10 2, inY := 2,
     values := 4, line := false }]

/-- The places of the token sumcheck of the stream times the reciprocal.
Length 2: one place in each example. -/
def atTN : List PscAt :=
  [{ full := false, link := 4, moment := 0, place := 867, chain := 7276,
     slot := 1602, riders := 1, sent := List.replicate 6 2, inY := 2,
     values := 2, line := false },
   { full := true, link := 24, moment := 0, place := 1123, chain := 47412,
     slot := 2090, riders := 1, sent := List.replicate 10 2, inY := 2,
     values := 2, line := false }]

/-- The places of the token sumcheck of the activations times the head's weights; it goes on over
the features.
Length 2: one place in each example. -/
def atTH : List PscAt :=
  [{ full := false, link := 4, moment := 0, place := 876, chain := 7285,
     slot := 1620, riders := 1, sent := List.replicate 15 2, inY := 2,
     values := 2, line := false },
   { full := true, link := 24, moment := 0, place := 1136, chain := 47425,
     slot := 2116, riders := 1, sent := List.replicate 23 2, inY := 2,
     values := 2, line := false }]

/-- The places of the merge of the one claim on the committed weights.
Length 2: one place in each example. -/
def atMerge : List PscAt :=
  [{ full := false, link := 4, moment := 2, place := 660, chain := 7968,
     slot := 2854, riders := 0, sent := List.replicate 11 2, inY := 1,
     values := 1, line := false },
   { full := true, link := 24, moment := 2, place := 747, chain := 48203,
     slot := 3531, riders := 0, sent := List.replicate 18 2, inY := 1,
     values := 1, line := false }]

/-- A round that belongs to no sumcheck. -/
structure OtherAt where
  /-- the full-size example; false: the small one -/
  full : Bool
  /-- the moment of the link behind which the round stands -/
  moment : Nat
  /-- the round's place in the list of the sub-proof's rounds behind that moment -/
  place : Nat
  /-- its place in the plan of the proof's first chain -/
  chain : Nat
  /-- its name in the plan -/
  name : String
  /-- the scalars of its message -/
  scalars : Nat
  /-- the slot of the first of them -/
  slot : Nat
  /-- the elements that the verifier draws -/
  draws : Nat
  /-- the rows that it batches -/
  rows : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The head's rounds behind its two lookups that belong to no sumcheck and are no LINE, in the
order of the chain. Length 12. In each example: the point over the positions (ZERO); the batching of
the sums of limb products and that of the row products, each with its scalars; the matrix of the
smallness test (RNG); the batching of the one weight claim; the batching of all claims. -/
def others : List OtherAt :=
  [{ full := false, moment := 0, place := 836, chain := 7245, name := "ZERO",
     scalars := 0, slot := 1531, draws := 6, rows := 0 },
   { full := false, moment := 0, place := 837, chain := 7246, name := "BAT-sigma",
     scalars := 9, slot := 1531, draws := 1, rows := 9 },
   { full := false, moment := 0, place := 857, chain := 7266, name := "BAT-sigma",
     scalars := 7, slot := 1575, draws := 1, rows := 7 },
   { full := false, moment := 1, place := 0, chain := 7305, name := "RNG",
     scalars := 0, slot := 1656, draws := 0, rows := 0 },
   { full := false, moment := 2, place := 659, chain := 7967, name := "BAT-sigma",
     scalars := 0, slot := 2854, draws := 1, rows := 1 },
   { full := false, moment := 2, place := 674, chain := 7982, name := "BAT-sigma",
     scalars := 0, slot := 2879, draws := 1, rows := 2712833 },
   { full := true, moment := 0, place := 1080, chain := 47369, name := "ZERO",
     scalars := 0, slot := 1995, draws := 10, rows := 0 },
   { full := true, moment := 0, place := 1081, chain := 47370, name := "BAT-sigma",
     scalars := 9, slot := 1995, draws := 1, rows := 9 },
   { full := true, moment := 0, place := 1109, chain := 47398, name := "BAT-sigma",
     scalars := 7, slot := 2055, draws := 1, rows := 7 },
   { full := true, moment := 1, place := 0, chain := 47453, name := "RNG",
     scalars := 0, slot := 2168, draws := 0, rows := 0 },
   { full := true, moment := 2, place := 746, chain := 48202, name := "BAT-sigma",
     scalars := 0, slot := 3531, draws := 1, rows := 1 },
   { full := true, moment := 2, place := 768, chain := 48224, name := "BAT-sigma",
     scalars := 0, slot := 3570, draws := 1, rows := 24653737 }]

end Cb.Pv.Head
