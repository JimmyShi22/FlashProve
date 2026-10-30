-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB8/PinsOfEnds.lean: the premises of `decl_full` and `r8'_of_lin` (Row.lean in
this folder), cut in two: those on X, and those on N and P; and those on X from what other files'
theorems conclude of the planner's answer m. Statements and proofs by rewriting; nothing is
evaluated.

Why. X is what `Key.sourceOf m` returns. What is known of m in scope of the goals is proved in files
that this one does not import. Here their conclusions are premises, letter for letter, so that
PinsOfReturns.lean, which imports them, needs little but calls.

Main names.
  `PinsX X`: the six equations of `Pins` on X, and the one of `r8'_of_lin`.
  `PinsNP N P`: the seven of `Pins` on N and P.
  `pins_of_parts`: the two give `Pins X N P`. `Pins` itself is as it was.
  `pinsNP_of_eq`: `PinsNP` where N and P are the written values, whole.
  `pinsX_of_ends`: `PinsX X` from: X holds m's chains, m's key's chains as read and the sized key's
    setting; the sized key is `keyFull`; five items as read back are `keyFull`'s.
  `r8_of_parts`, `r8'_of_x`: the statements of r8 and r8' (see Row.lean's head) from the parts.

Limits. No premise is proved here. Nothing on any public file. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB8.Row

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB8

open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.G Johnson.G.OfPlan
open OnBytes OnBytes.Params
open Lk6.AtPlan (keyFull)

/-- **What r8 and r8' read of X, as equations.** -/
structure PinsX (X : Source) : Prop where
  /-- the setting -/
  set : X.set = keyFull.set
  /-- of the one-time chain's public values, as read: the item "ranges" -/
  ranges : X.Y.k.oneTime.ranges = keyFull.ranges.x
  /-- as read: the shape of the test on the table -/
  lin : X.Y.k.oneTime.lin = keyFull.once.shape
  /-- as read: the index-mask message -/
  idx : X.Y.k.oneTime.indexMasks = keyFull.once.input
  /-- as read: the codes -/
  codes : X.Y.k.oneTime.codes = keyFull.codes
  /-- the planner's sized key -/
  sized : X.chains.made.sized.key = keyFull
  /-- of the shared chain's public values, as read: the shape of the test on the table -/
  sharedLin : X.Y.k.shared.lin = keyFull.once.shape

/-- **What the declared rounds read of N and P, as equations.** -/
structure PinsNP (N : H2U.PlaceNums) (P : LaterPlaces) : Prop where
  /-- the ranges' test's place: its chain -/
  nC : N.chain = 1
  /-- the numbers that its rounds are made of -/
  nN : N.nums = rNums
  /-- the folded row's test's place: its chain -/
  uC : P.U.chain = 2
  /-- the numbers that its rounds are made of -/
  uN : P.U.nums = uNums
  /-- Omega's test has a place; its chain; the numbers that its rounds are made of -/
  o : ∃ O, P.O = some O ∧ O.chain = 2 ∧ O.nums = oNums
  /-- the own test's place: its chain -/
  wC : P.W.chain = 3
  /-- the numbers that its rounds are made of -/
  wN : P.W.nums = wNums

/-- The two parts give the whole. -/
theorem pins_of_parts {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (hx : PinsX X)
    (hn : PinsNP N P) : Pins X N P :=
  ⟨hx.set, hx.ranges, hx.lin, hx.idx, hx.codes, hx.sized, hn.nC, hn.nN, hn.uC, hn.uN, hn.o, hn.wC,
    hn.wN⟩

/-- The written values meet the part on N and P. -/
theorem pinsNP_full : PinsNP rangesNumsFull laterPlacesFull :=
  ⟨rfl, rfl, rfl, rfl, ⟨_, rfl, rfl, rfl⟩, rfl, rfl⟩

/-- So do N and P that are the written values. -/
theorem pinsNP_of_eq {N : H2U.PlaceNums} {P : LaterPlaces} (hN : N = rangesNumsFull)
    (hP : P = laterPlacesFull) : PinsNP N P := by
  rw [hN, hP]
  exact pinsNP_full

/-- **The part on X, from what is concluded of m elsewhere.** hc, hk, hs: what X holds of m. hz: the
sized key. i1, i2, i5, i6, i8: five of the items that are read back from the parameter bytes. -/
theorem pinsX_of_ends {m : Made} {X : Source} (hc : X.chains = m.p.chains)
    (hk : X.Y.k = m.p.chains.key) (hs : X.set = m.p.chains.made.sized.key.set)
    (hz : m.p.chains.made.sized.key = keyFull)
    (i1 : m.p.chains.key.oneTime.indexMasks = keyFull.once.input)
    (i2 : m.p.chains.key.oneTime.ranges = keyFull.ranges.x)
    (i5 : m.p.chains.key.oneTime.codes = keyFull.codes)
    (i6 : m.p.chains.key.oneTime.lin = keyFull.once.shape)
    (i8 : m.p.chains.key.shared.lin = keyFull.once.shape) : PinsX X :=
  ⟨by rw [hs, hz], by rw [hk, i2], by rw [hk, i6], by rw [hk, i1], by rw [hk, i5], by rw [hc, hz],
    by rw [hk, i8]⟩

/-- The statement of r8 from the parts. -/
theorem r8_of_parts {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (hx : PinsX X)
    (hn : PinsNP N P) : writtenOf "key file" (descriptionFromSource X N P).roundsDeclaredByBlocks = .ok dryKeyFull :=
  r8_of_pins (pins_of_parts hx hn)

/-- The statement of r8' from the part on X. -/
theorem r8'_of_x {X : Source} (hx : PinsX X) (N : H2U.PlaceNums) (P : LaterPlaces) :
    (descriptionFromSource X N P).tableDepth = 32 :=
  r8'_of_lin N P hx.sharedLin

end Johnson.KB8

#print axioms Johnson.KB8.pins_of_parts
#print axioms Johnson.KB8.pinsNP_full
#print axioms Johnson.KB8.pinsNP_of_eq
#print axioms Johnson.KB8.pinsX_of_ends
#print axioms Johnson.KB8.r8_of_parts
#print axioms Johnson.KB8.r8'_of_x
