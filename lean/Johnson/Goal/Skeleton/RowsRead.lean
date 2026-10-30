-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/RowsRead.lean: one named condition on three public files: the maker of the
rows of the sendings returns at them, and in the first proof chain's rows one shape has one radius.
Two definitions, five theorems with their proofs.


Why. Four of the tests in front of the head of the closed constant (`P5J.At.Nine`,
Johnson/P5J/AtNameA.lean) read the three public files a second time, beside the planner that the
verifier runs: `P5T.radIsB`, the first clause of `At.spotsB`, `At.callsSomeB` and `At.digSomeB`.
All four go through `Johnson.G.sendRowsOf` (Johnson/G/LinkSig.lean). The verifier never calls that
maker, and no entry test compares its value with a written one. So what the four want of it stands
as a condition under one name, once, and each of the four has its lemma from it.

Main names. Z: three public files.
  `rowsReadB Z`: the test with code: where `Johnson.G.sendRowsOf Z.pol Z.lay Z.KL` returns rows:
    `P5T.radOneB` (Johnson/P5J/Rad3Seat3At.lean) at what is sampled in the first proof chain's rows;
    where it returns none: false.
  `rowsRead Z`: it accepts.
  `rowsRead_iff`: that is: the maker returns some R, and `radOneB` accepts at R's.
  `rowsRead.rows`, `rowsRead.one`: the two halves. `rowsRead.some`: the first half in the form
    `(P5T.rowsAt? Z.pol Z.lay Z.KL).isSome = true`. `rowsRead.getD`: the default of
    `(P5T.rowsAt? …).getD []` is not taken.

Limits. It reads the public files alone: no proof, no key, no weights. It is not shown to hold at
any Z. Of what the rows hold it says the one thing named. Nothing on soundness.

-/
import Ladder.Stored
import Johnson.P5J.Rad3Seat3At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J

/-- The test: the maker of the rows of the sendings returns at the three public files, and in the
first proof chain's rows one shape has one radius. -/
def rowsReadB (Z : VerifierAndGoals.PublicFiles) : Bool :=
  match Johnson.G.sendRowsOf Z.pol Z.lay Z.KL with
  | .ok rows => P5T.radOneB ((P5T.firstRows rows).flatMap (·.sampled))
  | .error _ => false

/-- **The second reading of the three public files returns, with one radius a shape.** -/
def rowsRead (Z : VerifierAndGoals.PublicFiles) : Prop := rowsReadB Z = true

/-- The condition, as a sentence on the maker. -/
theorem rowsRead_iff {Z : VerifierAndGoals.PublicFiles} :
    rowsRead Z ↔ ∃ R, Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R ∧
      P5T.radOneB ((P5T.firstRows R).flatMap (·.sampled)) = true := by
  unfold rowsRead rowsReadB
  cases h : Johnson.G.sendRowsOf Z.pol Z.lay Z.KL with
  | error e => exact ⟨fun c => (by cases c), fun ⟨_, c, _⟩ => (by cases c)⟩
  | ok R => exact ⟨fun c => ⟨R, rfl, c⟩, fun ⟨_, e, c⟩ => (by cases e; exact c)⟩

/-- The rows. -/
theorem rowsRead.rows {Z : VerifierAndGoals.PublicFiles} (h : rowsRead Z) :
    ∃ R, Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R :=
  let ⟨R, e, _⟩ := rowsRead_iff.1 h
  ⟨R, e⟩

/-- The first half, as the tests' own reader of the rows says it. -/
theorem rowsRead.some {Z : VerifierAndGoals.PublicFiles} (h : rowsRead Z) :
    (P5T.rowsAt? Z.pol Z.lay Z.KL).isSome = true := by
  obtain ⟨R, hR⟩ := h.rows
  unfold P5T.rowsAt?
  rw [hR]
  rfl

/-- One shape, one radius, at whatever rows the maker returns. -/
theorem rowsRead.one {Z : VerifierAndGoals.PublicFiles} (h : rowsRead Z) {R : List Johnson.G.SendRow}
    (e : Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R) :
    P5T.radOneB ((P5T.firstRows R).flatMap (·.sampled)) = true := by
  obtain ⟨R', e', c⟩ := rowsRead_iff.1 h
  obtain rfl : R' = R := Except.ok.inj (e'.symm.trans e)
  exact c

/-- The default is not taken. -/
theorem rowsRead.getD {Z : VerifierAndGoals.PublicFiles} (h : rowsRead Z) :
    ∃ R, Johnson.G.sendRowsOf Z.pol Z.lay Z.KL = .ok R ∧
      (P5T.rowsAt? Z.pol Z.lay Z.KL).getD [] = R := by
  obtain ⟨R, hR⟩ := h.rows
  refine ⟨R, hR, ?_⟩
  unfold P5T.rowsAt?
  rw [hR]
  rfl

end P5J

#print axioms P5J.rowsRead_iff
#print axioms P5J.rowsRead.rows
#print axioms P5J.rowsRead.some
#print axioms P5J.rowsRead.one
#print axioms P5J.rowsRead.getD
