-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Params/Fit/TurnForward.lean: a turn of the planner's iterations, forward and in parts: from
what the parts return to what Params.turn and Params.sizeOne return; and the search for the
integer m (Params.largestM), step by step.

A statement "this turn returns that", proved by one evaluation in Lean's kernel, takes about 2 GiB
of memory: the turn seeks m by some fifteen trials of Params.groupHolds, and the kernel keeps what
it has reduced until the statement is closed. With the laws of this file every trial is a statement
of its own (about 0.15 GiB), and the turn follows without a further evaluation.

Main names.
  firstGood_hit, growGood_step, growGood_stop, lastGood_up, lastGood_down, lastGood_end   one step
                 of the three routines of the search, for every test good.
  turn_more_of, turn_settled_of   Params.turn under the Johnson rule where the sized group serves.
  sizeOne_serves            Params.sizeOne under the Johnson rule where the sized group serves.

Limits. Only the branches that are named. Nothing on soundness.

-/
import OnBytes.Params.DeriveLin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

/-! ## The search for m -/

/-- The first routine stops at once where the test says yes. -/
theorem firstGood_hit (good : Nat → Bool) (fuel lo : Nat) (h : good lo = true) :
    firstGood good (fuel + 1) lo = lo := by
  rw [firstGood, h]
  simp

/-- The second routine doubles the upper end while the test says yes below the limit. -/
theorem growGood_step (good : Nat → Bool) (limit fuel lo hi : Nat) (hl : hi < limit)
    (h : good hi = true) :
    growGood good limit (fuel + 1) lo hi = growGood good limit fuel hi (2 * hi) := by
  rw [growGood, h]
  simp [hl]

/-- The second routine stops at the first no. -/
theorem growGood_stop (good : Nat → Bool) (limit fuel lo hi : Nat) (h : good hi = false) :
    growGood good limit (fuel + 1) lo hi = (lo, hi) := by
  rw [growGood, h]
  simp

/-- The third routine halves the stretch: a yes in the middle moves the lower end up. -/
theorem lastGood_up (good : Nat → Bool) (fuel lo hi : Nat) (hd : 1 < hi - lo)
    (h : good (lo + (hi - lo) / 2) = true) :
    lastGood good (fuel + 1) lo hi = lastGood good fuel (lo + (hi - lo) / 2) hi := by
  rw [lastGood]
  simp [hd, h]

/-- A no in the middle moves the upper end down. -/
theorem lastGood_down (good : Nat → Bool) (fuel lo hi : Nat) (hd : 1 < hi - lo)
    (h : good (lo + (hi - lo) / 2) = false) :
    lastGood good (fuel + 1) lo hi = lastGood good fuel lo (lo + (hi - lo) / 2) := by
  rw [lastGood]
  simp [hd, h]

/-- The third routine ends at the lower end when the two ends are neighbours. -/
theorem lastGood_end (good : Nat → Bool) (fuel lo hi : Nat) (hd : ¬ 1 < hi - lo) :
    lastGood good (fuel + 1) lo hi = lo := by
  rw [lastGood]
  simp [hd]

/-! ## A turn -/

/-- The group of a turn: the shape with the two numbers of random entries. -/
def turnGroup (shape : GroupSize) (mainR maskR : Nat) : GroupSize :=
  { shape with main := { shape.main with r := mainR }, mask := { shape.mask with r := maskR } }

/-- A turn where the sized group serves and more positions follow. -/
theorem turn_more_of {s : Setting} {scope : Scope} {load : GroupLoad} {shape sized : GroupSize}
    {mainR maskR t t2 : Nat}
    (hfit : ((turnGroup shape mainR maskR).main.n < (turnGroup shape mainR maskR).main.dim ||
      (turnGroup shape mainR maskR).mask.n < (turnGroup shape mainR maskR).mask.dim) = false)
    (hs : sizeGroup s scope (turnGroup shape mainR maskR) load = sized)
    (hh : groupHolds s scope sized load = true)
    (hp : scopePositions s scope (analysis s sized).mainAt.agree (margin s) = t2) (hl : t < t2) :
    turn s scope load shape mainR maskR t = .more sized t2 := by
  unfold turn
  have hs' : sizeGroup s scope (turnGroup shape mainR maskR) load = sized := hs
  unfold turnGroup at hfit hs'
  simp only [hfit, hs', hh, hp]
  simp [Nat.not_le.2 hl]

/-- A turn where the sized group serves and the positions have settled. -/
theorem turn_settled_of {s : Setting} {scope : Scope} {load : GroupLoad} {shape sized : GroupSize}
    {mainR maskR t t2 : Nat}
    (hfit : ((turnGroup shape mainR maskR).main.n < (turnGroup shape mainR maskR).main.dim ||
      (turnGroup shape mainR maskR).mask.n < (turnGroup shape mainR maskR).mask.dim) = false)
    (hs : sizeGroup s scope (turnGroup shape mainR maskR) load = sized)
    (hh : groupHolds s scope sized load = true)
    (hp : scopePositions s scope (analysis s sized).mainAt.agree (margin s) = t2) (hl : t2 ≤ t) :
    turn s scope load shape mainR maskR t = .settled sized t2 := by
  unfold turn
  have hs' : sizeGroup s scope (turnGroup shape mainR maskR) load = sized := hs
  unfold turnGroup at hfit hs'
  simp only [hfit, hs', hh, hp]
  simp [hl]

/-! ## The sizing of one group of the test on the table -/

/-- Params.sizeOne under the Johnson rule where the sized group serves. -/
theorem sizeOne_serves {s : Setting} {shape sized : GroupSize} {line : GroupLine} {scope : Scope}
    {mainDraws maskDraws rows more : Nat} {before : Sizing}
    (hfit : ((turnGroup shape (tailFor mainDraws) (tailFor maskDraws)).main.n <
        (turnGroup shape (tailFor mainDraws) (tailFor maskDraws)).main.dim ||
      (turnGroup shape (tailFor mainDraws) (tailFor maskDraws)).mask.n <
        (turnGroup shape (tailFor mainDraws) (tailFor maskDraws)).mask.dim) = false)
    (hs : sizeGroup s scope (turnGroup shape (tailFor mainDraws) (tailFor maskDraws))
      ⟨stageCubeBits (turnGroup shape (tailFor mainDraws) (tailFor maskDraws)), 2, rows⟩ = sized)
    (hh : groupHolds s scope sized
      ⟨stageCubeBits (turnGroup shape (tailFor mainDraws) (tailFor maskDraws)), 2, rows⟩ = true)
    (hp : scopePositions s scope (analysis s sized).mainAt.agree (margin s) = more)
    (h0 : more ≠ 0) :
    sizeOne s shape line scope mainDraws maskDraws rows before =
      some ⟨sized, max before.t more, true⟩ := by
  unfold sizeOne
  have hs' : sizeGroup s scope (turnGroup shape (tailFor mainDraws) (tailFor maskDraws))
      ⟨stageCubeBits (turnGroup shape (tailFor mainDraws) (tailFor maskDraws)), 2, rows⟩
      = sized := hs
  unfold turnGroup at hfit hs' hh
  simp only [hfit, hs', hh, hp]
  simp [h0]

end OnBytes.Params

#print axioms OnBytes.Params.sizeOne_serves
#print axioms OnBytes.Params.turn_more_of
#print axioms OnBytes.Params.turn_settled_of
#print axioms OnBytes.Params.lastGood_up
