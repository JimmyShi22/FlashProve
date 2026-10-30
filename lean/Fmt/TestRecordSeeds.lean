-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/TestRecordSeeds.lean: the tests (#guard) on the drawing of a record's seeds with the hash as an
argument (Fmt/RecordSeeds.lean). No definition that another file uses, no theorem.

Expected values. PAGE: a line of docs/format/format-vectors.txt, named by its number. A test whose
comment names no line has an expected value of this file's own: the equality of two calls, a length,
a refusal.

What is held:
  1. At the format's own hash the drawing gives the page's record seed (lines 36, 37), in both ways
     to write it, and what the library's elder function at that hash gives
     (`Known56.recordSeeds`, Fmt/Rules56Known.lean), in both fields, at several numbers of seeds and
     coordinates.
  2. The flat list: its order at the page's seed; its length.
  3. No seed: the empty list.
  4. Another hash gives other seeds; so does another name.
Limits:
  The page has one record seed: one seed of two coordinates. The order of several seeds is held
  against the elder function alone.

-/
import Fmt.RecordSeeds
import Fmt.Rules56Known

namespace Fmt
namespace RecordSeedsTest

/-- lines 36, 37: "the name with root pattern(32) with 13 i + 4, the configuration of one file 'toy'
and a line feed, a = 10, 3 entries, tail 40, 2^9 rows, 1 answer, salt 40" -/
def nameP : ByteArray := tableName (pattern 32 13 4) Toy4.cfg 10 3 40 9 1 40

/-- the format's own hash, with values in Id -/
def hOwn : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray :=
  fun n t i s b => pure (formatHash n t i s b)

/-- the format's own hash with the number of the call raised by one -/
def hOther : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray :=
  fun n t i s b => pure (formatHash (n + 1) t i s b)

end RecordSeedsTest

open RecordSeedsTest

-- PAGE 36, 37: two coordinates: the point; the factor
#guard recordSeeds .two nameP 2 1 = some [([(9697749137137958355, 613613959841214928,
  8403959380172774020), (15526148976690303146, 2032215208828410348, 4053187377642565227)],
  (14917727018641805655, 3966560771581124203, 17230899846445233913))]
#guard Id.run (recordSeedsW hOwn .two nameP 2 1) = recordSeeds .two nameP 2 1
-- the elder function at the format's own hash: both fields; 0 to 3 seeds of 0 to 3 coordinates
#guard [Fld.one, .two].all fun f => (List.range 4).all fun v => (List.range 4).all fun a =>
  recordSeeds f nameP v a = Known56.recordSeeds f nameP v a
-- PAGE 36, 37: the flat list: the point's two coordinates, then the factor
#guard (recordSeeds .two nameP 2 1).map flatSeeds = some [(9697749137137958355, 613613959841214928,
  8403959380172774020), (15526148976690303146, 2032215208828410348, 4053187377642565227),
  (14917727018641805655, 3966560771581124203, 17230899846445233913)]
-- three seeds of two coordinates: nine elements; the first of the three is the page's one seed (the
-- seeds are cut one after the other from one row of words)
#guard ((recordSeeds .two nameP 2 3).map fun l => (l.length, (flatSeeds l).length)) = some (3, 9) &&
  ((recordSeeds .two nameP 2 3).map fun l => l.take 1) = recordSeeds .two nameP 2 1
-- no seed: the empty list
#guard recordSeeds .two nameP 2 0 = some [] && flatSeeds [] = []
-- another hash: other seeds; another name: other seeds
#guard Id.run (recordSeedsW hOther .two nameP 2 1) != recordSeeds .two nameP 2 1 &&
  recordSeeds .two (tableName (pattern 32 13 5) Toy4.cfg 10 3 40 9 1 40) 2 1 !=
    recordSeeds .two nameP 2 1

end Fmt
