-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Fmt/PlacesKnown.lean: tests of Fmt/Places.lean.

1. What the file contains. Tests (#guard) alone, of four kinds, and each block says which:
   "printed": the expected number stands on the format page or in a comment of this library;
   "printed in letters": the page prints the formula's value in letters, and the sizes are made up;
   "worked": the page's formula, worked by hand on a small made-up shape;
   "joined": one function of Fmt/Places.lean against another.
2. What is checked when the file compiles. Each #guard is an evaluation by Lean's evaluator: no
   theorem.
3. Theorems. None.
4. What is not claimed. No test shows that the programs compute a number.

Terms: lean/GLOSSARY.md.
-/
import Fmt.Places

namespace Fmt.Places

/-! Worked: the least b with n ≤ 2 ^ b. -/
#guard (List.range 10).map logUp == [0, 0, 1, 2, 2, 3, 3, 3, 3, 4]
#guard [16, 17, 18, 512, 1024, 1025, 2 ^ 20, 2 ^ 20 + 1].map logUp == [4, 5, 5, 9, 10, 11, 20, 21]

/-! Printed, 09-key-and-leaf-files.md, the head of section 9: "entry 0 of row 0, entry 0 of row 1,
and so on to row m - 1, then entry 1 of row 0". -/
#guard (List.range 4).map (freeAt 3) == [(0, 0), (1, 0), (2, 0), (0, 1)]

/-! Worked, the same place: the order goes on; a number whose low bits are m or more names no
entry. -/
#guard freeAt 3 4 == (1, 1)
#guard entryAt 3 3 == none
#guard entryAt 3 6 == some (2, 1)
#guard [5, 6, 7].map (entryAt 5) == [none, none, none]
#guard entryAt 5 12 == some (4, 1)

/-! Printed in letters, FORMAT.md 16.1, condition 3, part (d): "One row of 2^lz entries has 2^lz - S
free entries". -/
#guard freeCount 1 (2 ^ 13) 1 == 2 ^ 13 - 1
#guard freeCount 1 (2 ^ 8) 3 == 2 ^ 8 - 3

/-! Worked: the free entries' numbers rise; m (e - s) + (m - 1); none where a row is shorter than
the pad. -/
#guard (List.range 7).map (fun k => entryNo 3 (freeAt 3 k).1 (freeAt 3 k).2)
  == [0, 1, 2, 4, 5, 6, 8]
#guard freeCount 3 8 2 == 20
#guard freeCount 3 1 2 == 0
#guard freeCount 3 2 2 == 2
#guard freeCount 0 8 2 == 0

/-! Joined: the entry after the last free one is the pad's first. -/
#guard freeAt 3 (freeCount 3 8 2) == (padRow 0 3, padEntry 8 2 1 0 0)
#guard freeAt 1 (freeCount 1 64 1) == (padRow 5 1, padEntry 64 1 1 0 0)

/-! Printed, toys/1-product.md, Part 1, section 3 ("SEND in the toy run product"): three main rows,
m[r + 4 p]; at n = 12 a mask row of 32 entries and 15 coordinates, at n = 4 one of 16 and 7. -/
#guard entryNo 3 2 5 == 2 + 4 * 5
#guard cubeBits 3 12 1 5 == 15
#guard cubeBits 3 4 1 4 == 7

/-! Worked, FORMAT.md 13.9: with one table that table's bits; with both the larger number plus 1,
also where the mask table is the larger; the top bit is 1 for the mask table, and there is none
where there is one table; row bits low in the mask table too. -/
#guard cubeBits 3 12 0 0 == 14
#guard cubeBits 0 0 2 6 == 7
#guard cubeBits 1 2 4 6 == 9
#guard cubeBits 2 3 2 3 == 5
#guard tableBits 0 5 == 0
#guard cubeBits 3 12 0 5 == 14
#guard cubeBits 0 7 2 6 == 7
#guard cubeNo 3 12 1 5 false 2 5 == 22
#guard cubeNo 3 12 1 5 true 0 5 == 2 ^ 14 + 5
#guard cubeNo 1 2 4 6 false 0 3 == 3
#guard cubeNo 1 2 4 6 true 3 5 == 2 ^ 8 + 3 + 4 * 5
#guard cubeNo 0 0 2 6 true 1 3 == 1 + 2 * 3

/-! Printed in letters, toys/2-links.md, section 3, at s = 1: the pad's indices are l_zk - 1 in the
mask table of a message with one mask row; 2 l - 1 in the table of two main rows over E; l - 3,
l - 2, l - 1 in one main row over F. -/
#guard entryNo 1 (padRow 2 1) (padEntry 32 1 (padEach true false) 0 0) == 32 - 1
#guard entryNo 2 (padRow 2 0) (padEntry 16 1 (padEach false true) 0 0) == 2 * 16 - 1
#guard (List.range 3).map
    (fun t => entryNo 1 (padRow 1 0) (padEntry 16 1 (padEach false false) 0 t))
  == [16 - 3, 16 - 2, 16 - 1]

/-! Worked, FORMAT.md 13.9: the highest real row; answer i has entry l - s + i; over F the three
entries from l - 3 s + 3 i on; in the mask rows if there are any; one entry an answer there. -/
#guard padInMask 1 && padInMask 2 && !padInMask 0
#guard padEach true true == 1
#guard padRow 42 0 == 41
#guard padRow 42 2 == 1
#guard (List.range 2).map (fun i => padEntry 64 2 1 i 0) == [62, 63]
#guard (List.range 2).flatMap (fun i => (List.range 3).map (padEntry 64 2 3 i))
  == [58, 59, 60, 61, 62, 63]

/-! Worked, 09-key-and-leaf-files.md, "Where a vector is in an oracle message's main rows". -/
#guard vecAt true 8 4 19 == (2, 3)
#guard vecAt false 8 4 19 == (3, 4)
#guard vecAt true 16 4 19 == (1, 3)
#guard vecAt false 16 8 19 == (3, 2)

/-! Worked, FORMAT.md 13.4, step 7: x = c 2^a + i or i 2^e + c; row + (x >> bj); place + (x mod
2^bj). -/
#guard blockAt true 2 3 10 100 4 3 5 == (10 + 1, 100 + 7)
#guard blockAt false 2 3 10 100 4 3 5 == (10 + 1, 100 + 13)

/-! Printed, the head of Fmt/M1Psc.lean, row (U): K variables X and one further variable Y, two
scalars a round: gamma_l on entry 2 l, gamma_l^2 on 2 l + 1; 1, beta, beta^2 on 2 K, 2 K + 1,
2 K + 2; the rows (E_1), (E_2) at 2 K + 3, 2 K + 4; 2 K + 5 in all, 29 at K = 12. (In that toy the
mask row's entry with an end value's number masks that end value; elsewhere it need not.) -/
#guard (List.range 3).flatMap (fun l => [hidPos [2, 2, 2, 2] l 1, hidPos [2, 2, 2, 2] l 2])
  == [0, 1, 2, 3, 4, 5]
#guard (List.range 3).map (hidPos [2, 2, 2, 2] 3) == [6, 7, 8]
#guard [endNo [2, 2, 2, 2] 0, endNo [2, 2, 2, 2] 1] == [9, 10]
#guard endNo (List.replicate 13 2) 2 == 29

/-! Worked, 11-1-machinery.md: pos(l, deg) and the scalars' numbers where the rounds send unequal
numbers of scalars. -/
#guard [hidPos [2, 3, 2] 0 1, hidPos [2, 3, 2] 0 2, hidPos [2, 3, 2] 1 1, hidPos [2, 3, 2] 1 2,
  hidPos [2, 3, 2] 1 3, hidPos [2, 3, 2] 2 0, hidPos [2, 3, 2] 2 1, hidPos [2, 3, 2] 2 2]
  == List.range 8
#guard [sentNo [2, 3, 2] 0 0, sentNo [2, 3, 2] 1 0, sentNo [2, 3, 2] 2 0, sentNo [2, 3, 2] 2 1]
  == [1, 3, 6, 7]
#guard hidCount [2, 3, 2] == 8
#guard endNo [2, 3, 2] 0 == 8
#guard [hidPos [3, 1, 2, 2] 1 1, hidPos [3, 1, 2, 2] 2 1, hidPos [3, 1, 2, 2] 2 2,
  hidPos [3, 1, 2, 2] 3 0] == [3, 4, 5, 6]
#guard [sentNo [3, 1, 2, 2] 1 0, sentNo [3, 1, 2, 2] 2 0, sentNo [3, 1, 2, 2] 3 0] == [4, 5, 7]
#guard (List.range 3).map (hidPos [2] 0) == [0, 1, 2]
#guard hidCount [2] == 3
#guard hidCount (List.replicate 18 2) == 1 + 2 * 18

/-! Worked, 11-1-machinery.md, "The keys": the numbers u 2^lc + x with mz ≤ x < 2^lc, and all from
tau 2^lc on, are padding positions: tau mz key numbers are not; n_Z = max(10, clog2(tau) + lc). -/
#guard ((List.range 64).filter (isKey 3 3 5)).length == 3 * 5
#guard isKey 3 3 5 (keyNo 3 2 4)
#guard !isKey 3 3 5 (keyNo 3 2 5)
#guard !isKey 3 3 5 (keyNo 3 3 0)
#guard keyNo 3 2 4 == 20
#guard keyNo 2 3 1 == 13
#guard ((List.range 32).filter (isKey 4 2 3)) == [0, 1, 2, 4, 5, 6, 8, 9, 10, 12, 13, 14]
#guard keyBits 3 3 == 10
#guard keyBits 5 9 == 12
#guard keyBits 4 9 == 11

/-! Printed, the worked examples of 11-2-feed-forward-segment.md, 11-3-attention-segment.md and
11-4-output-head.md at tau = 128: mz = 499,712 gives 27 bits of a key's index, mz = 221,184 gives
26, mz = 385,024 gives 27; an index has n_Z + 1 bits. -/
#guard [499712, 221184, 385024].map (fun mz => keyBits 128 (logUp mz) + 1) == [27, 26, 27]

/-! Worked, 11-1-machinery.md, "Its numbers": key number x is in the call's tree floor(x / 2^dT) at
the index x mod 2^dT; call 1 has the trees from 2^(n_Z - dT) on; the tree's number is low. The
indices of both calls' key numbers fill 0 .. 2^(n_Z + 1) - 1. -/
#guard keyIndex 10 8 0 257 == 1 + 8 * 1
#guard keyIndex 10 8 1 257 == 4 + 1 + 8 * 1
#guard ((List.range 2).flatMap fun c => (List.range 16).map (keyIndex 4 2 c)).mergeSort
  == List.range 32

end Fmt.Places
