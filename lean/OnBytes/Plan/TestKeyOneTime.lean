-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Plan/TestKeyOneTime.lean: tests of the derivation of a key's first chain from the public
files. They run when this file compiles.

The lines are those of prover/examples/target_small_f2_roomy/policy.txt. What is expected are the
parameter bytes that the C++ verifier forms for the first chain of that example's key, by their
length and digest (a print of cp_verify over examples/accepted-proof, whose policy is that file). The units of the
example's matrix of 59392 rows were read back from the item "ranges" of these same bytes. So the
test shows that cutting, sizing, planning and spelling give the C++ programs' bytes from these
units. That these are the units of the model's layout is the matter of
OnBytes/Plan/TestFromLayout.lean.

What is tested: small cases of the cutting into parts by hand; the lookups, the oracle message and
the stages of the example; the parameter bytes of the key's first chain, by their length and their
digest; and the same bytes for a toy key of the C++ tool blocks/frame/handover_files.cpp, derived
from that toy's two public files (toyFile says on what they hang) and the shape in its source.

No module of the program imports this file. It holds no theorem.
-/
import OnBytes.Plan.KeyOneTime
import OnBytes.Params.TestFile
import OnBytes.Hash.H

namespace OnBytes.Plan.TestKeyOneTime

open OnBytes.Params

-- parts of four entries; a run that crosses a border is cut there
#guard cutEntries [⟨0, 10, 3, 3⟩, ⟨0, 20, 6, 6⟩] 2 0 ==
  [⟨2, [⟨0, 10, 3, 3⟩, ⟨3, 20, 1, 6⟩]⟩, ⟨2, [⟨0, 21, 4, 6⟩]⟩, ⟨2, [⟨0, 25, 1, 6⟩]⟩]
-- both rows of an entry as keys of their own: the row's number in the top bit of the place
#guard cutEntries [⟨0, 10, 3, 3⟩] 2 1 ==
  [⟨2, [⟨0, 10, 2, 0⟩, ⟨2, 13, 2, 0⟩]⟩, ⟨2, [⟨0, 12, 1, 0⟩, ⟨2, 15, 1, 0⟩]⟩]
#guard partsOf [⟨0, 10, 3, 3⟩, ⟨0, 20, 6, 6⟩] 2 0 == 3 && partsOf [⟨0, 10, 3, 3⟩] 2 1 == 2

/-- Two runs of q and p entries are cut into parts of 2^logMost entries without a loss: the parts
hold q + p places, each part but the last is full, and there are as many parts as partsOf says. -/
def cutWhole (logMost q p : Nat) : Bool :=
  let entries : List WfRun := [⟨0, 0, q, 1⟩, ⟨0, 1000, p, 1⟩]
  let parts := cutEntries entries logMost 0
  let sizes := parts.map fun x => x.runs.foldl (fun n r => n + r.places) 0
  sizes.foldl (· + ·) 0 == q + p && sizes.dropLast.all (· == 2 ^ logMost) &&
    parts.length == partsOf entries logMost 0

-- at the borders: p = k most - 1, k most, k most + 1, after every filling q of the part before;
-- parts of 4 entries, of 2, and of 1
#guard (List.range 6).all fun q => (List.range 14).all fun p => cutWhole 2 q p
#guard (List.range 4).all fun q => (List.range 8).all fun p => cutWhole 1 q p
#guard (List.range 3).all fun q => (List.range 6).all fun p => cutWhole 0 q p
/-- The entries that cutRun places, for parts of four, under a bound on the pieces. -/
def placed (bound : Nat) (r : WfRun) (st : List (List WfRun) × Nat) : Nat :=
  (cutRun 4 bound r st).1.foldl (fun n one => one.foldl (fun k x => k + x.places) n) 0

-- the bound: nine entries after a full part are three pieces of at most four; two lose an entry
#guard placed 3 ⟨0, 0, 9, 1⟩ ([], 0) == 9 && placed 2 ⟨0, 0, 9, 1⟩ ([], 0) == 8
-- with one place of room left, ten entries are four pieces: 1, 4, 4, 1. cutEntries hands in
-- 10 / 4 + 2 = 4, which is just enough; three lose an entry
#guard placed 4 ⟨0, 0, 10, 1⟩ ([[]], 1) == 10 && placed 3 ⟨0, 0, 10, 1⟩ ([[]], 1) == 9
#guard planesOfParts [⟨5, []⟩, ⟨5, []⟩, ⟨5, []⟩, ⟨5, []⟩] 6 == 14
#guard planesOfParts [⟨4, []⟩] 6 == 11

/-- The rows of the example's first 64 units, which have two digits and follow one another. -/
def firstRows : List Nat := [
    4096, 128, 256, 512, 512, 512, 4096, 128, 256, 256, 256, 1024, 1024, 256, 1024, 2, 4096,
    128, 256, 512, 512, 512, 4096, 128, 256, 256, 256, 1024, 1024, 256, 1024, 2, 4096, 128, 256,
    512, 512, 512, 4096, 128, 256, 256, 256, 1024, 1024, 256, 1024, 2, 4096, 128, 256, 512, 512,
    512, 4096, 128, 256, 256, 256, 1024, 1024, 256, 1024, 2]

/-- Units of two digits with the listed numbers of rows, one after the other from a row on. -/
def unitsFrom : Nat → List Nat → List RowUnit
  | _, [] => []
  | at_, r :: rs => ⟨at_, r, 2⟩ :: unitsFrom (at_ + r) rs

/-- The example's units: the 64, one of four digits, and one more of two. -/
def units : List RowUnit := unitsFrom 0 firstRows ++ [⟨57352, 512, 4⟩, ⟨57864, 256, 2⟩]

/-- What the example's key looks up. -/
def shape : Option Shape := shapeOfUnits 11 59392 59392 units

/-- What follows for the example's key. -/
def sized : Option KeySized := TestFile.smallLines.bind fun l => shape.bind (keySized l)

#guard unitsOk 59392 59392 units
#guard !unitsOk 59392 59392 (units.drop 1) && !unitsOk 59392 59391 units
#guard shape.any fun s => s.lookups.map (·.entries.length) == [65 + 2 + 636, 65]
/-- All that is compared, computed once: the lookups (table, plane slots, real planes, the parts'
places in bits, the parts' numbers of runs); whether a key can be made; the number of rounds;
whether every round holds at the target; the length and the digest of the parameter bytes of the
key's first chain. The two
"whether" cannot be false where there is a value at all: oneTimeParams and oneTimePlan refuse
otherwise. -/
def facts : Option (List (Nat × Nat × Nat × List Nat × List Nat) × Bool × Nat × Bool × Nat ×
    String) := do
  let l ← TestFile.smallLines
  let z ← sized
  let p ← (oneTimePlan z).toOption
  let b ← shape.bind fun s => (oneTimeParams l TestFile.smallCfg s).toOption
  pure (z.ranges.x.lookups.map (fun l =>
      (l.d, l.mu, l.live, l.parts.map (·.logPlaces), l.parts.map (·.runs.length))),
    keyOk z, p.rounds.length, p.holds, b.size,
    Fmt.hex (Fmt.paramsDigestW (m := Id) formatHashFastForm b))

#guard facts == some (
  [(8, 5, 28, [14, 14, 14, 14], [34, 34, 46, 1298]),
   (13, 5, 27, [13, 13, 13, 13], [17, 17, 23, 11])],
  true, 3679, true, 434476,
  "859ef8873838b71646933101a10588f544016f7cfbfad3a784524407e01abc19")

/-! ## The toy key of the C++ tool that makes files for other verifiers -/

/-- The first of the toy's two public files: the lines of a parameter file, as toy_file() in
blocks/frame/tests/toy_file.h writes them. -/
def toyFile : List String :=
  ["version H821", "sec 128", "reading 1", "rowcost 1", "slots 2", "answers 1", "record 1",
   "work field 0 0 0", "work sample 0 0 0", "work closeness 0 0 0", "work positions 4 6 8",
   "work smallness 0 0 0", "salt 40", "listed 0", "group link 1 13 9 13 5",
   "stages link 2 1 13 13 0 0 15 15", "group folded 1 13 9 13 4",
   "stages folded 2 1 13 13 0 0 15 15", "group omega 1 13 7 13 4",
   "stages omega 2 1 13 13 0 0 15 15", "group own 1 13 7 12 3", "stages own 2 1 13 13 0 0 15 15",
   "group once-folded 1 13 9 13 4", "stages once-folded 2 1 13 13 0 0 15 15",
   "group once-omega 1 13 7 13 4", "stages once-omega 2 1 13 13 0 0 15 15",
   "group once-own 1 13 7 12 3", "stages once-own 2 1 13 13 0 0 15 15",
   "group once-ranges 1 14 9 14 8", "stages once-ranges 2 1 14 14 0 0 15 15", "ranges-part 5",
   "table 3 14 803 1001 0 6"]

/-- The second of the toy's two public files. -/
def toyShapes : String := "links 3\npending 2\nmatrix 100\nidentifiers 1 2 3\n"

/-- What the toy's key looks up in its matrix of 100 rows. Row i and row i + 50 are an entry; every
cell is a byte of three bits; the first fifth of the entries are weights of two digits. -/
def toyShape : Shape where
  kCol := 0
  matrixRows := 100
  lookups := [
    { lookup := { d := 3, mu := 0, live := 0, digitWeight := [1], offset := 4, paddingKey := 3,
                  parts := [], firstBound := [1, 0] }
      entries := [⟨0, 0, 50, 50⟩]
      logRowsApart := 1 },
    { lookup := { d := 5, mu := 0, live := 0, digitWeight := [1, 8], offset := 16,
                  paddingKey := 17, parts := [], firstBound := [] }
      entries := [⟨0, 0, 10, 50⟩] }]

/-- The length and the digest of the parameter bytes of the toy key's first chain, derived from the
two public files and the shape. -/
def toyFacts : Option (Nat × String) := do
  let file := TestFile.fileOf toyFile
  let l ← (readLines file).toOption
  let b ← (oneTimeParams l.1 (Fmt.configDigest [file, toyShapes.toUTF8]) toyShape).toOption
  pure (b.size, Fmt.hex (Fmt.paramsDigestW (m := Id) formatHashFastForm b))

#guard toyFacts ==
  some (76647, "37d50efc5a1d3a11ec7e86353f53e9fe8c644210ea14f275a080e39a59ef88ff")

end OnBytes.Plan.TestKeyOneTime
