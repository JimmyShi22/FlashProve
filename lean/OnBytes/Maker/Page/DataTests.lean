-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/DataTests.lean: tests on a whole file's data that the page's laws on the leaves
ask for. Definitions alone: functions that compute.

  `treeFitB sb sh`    one tree that a round sends: it is not marked as stored; it is not deeper than
                      63; the first word of its leaves' label is below 2^64, at salts of sb bytes.
  `treesFitB sb ds`   all trees that the rounds ds send.
  `storedFitB a sb W` all stored tables in the three chains' rounds: marked as stored; tree number
                      0; depth a, not above 63; salts of sb bytes; fewer than 2^24 words a column;
                      the first word of the leaves' label below 2^64.
  `pageFitB a sb W`   the first at the three stretches of the data made of a and W, and the second.

What they give is in OnBytes/Maker/Page/DataTestsLaws.lean.


-/
import OnBytes.Maker.WholeOf

set_option autoImplicit false

namespace OnBytes.Maker.Page

open OnBytes.Maker

/-- One tree that a round sends. -/
def treeFitB (sb : ℕ) (sh : Fmt.Shape) : Bool :=
  !sh.stored && decide (sh.a ≤ 63) &&
    decide (164 + 65536 * Fmt.leafPlace sh.tree sh.W (sb / 8) < 2 ^ 64)

/-- All trees that the rounds send. -/
def treesFitB (sb : ℕ) (ds : List RDT) : Bool := ds.all fun d => d.trees.all (treeFitB sb)

/-- All stored tables in the three chains' rounds. -/
def storedFitB (a sb : ℕ) (W : Three.Whole) : Bool :=
  decide (a ≤ 63) && (W.ds₁ ++ (W.ds₂ ++ W.ds₃)).all fun d => d.stored.all fun t =>
    t.sh.stored && t.sh.tree == 0 && t.sh.a == a && t.salt == sb && decide (t.sh.W < 2 ^ 24) &&
      decide (174 + 65536 * Fmt.leafPlace 0 t.sh.W (sb / 8) < 2 ^ 64)

/-- The tests together. -/
def pageFitB (a sb : ℕ) (W : Three.Whole) : Bool :=
  treesFitB sb (WholeD.of a W).ds₁ && treesFitB sb (WholeD.of a W).ds₂ &&
    treesFitB sb (WholeD.of a W).ds₃ && storedFitB a sb W

end OnBytes.Maker.Page
