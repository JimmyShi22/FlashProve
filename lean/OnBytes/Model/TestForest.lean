-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestForest.lean: the public numbers of a lookup, tested on stored answers.

The C++ programs come with a file of known answers on the shape of a lookup,
verifier/tests/forest_values.txt. The C++ test that compares their verifier with it is not part of
the repository. This file compares the functions of
OnBytes/Model/Forest.lean with some of the same answers: the lines SHAPE, ORDER, PLANES and PUBRUN.
The file's other kinds of lines (FORM, COUNTS, ORDER.WRONG, ARRAY, PLACE) are not used here. The
program does not import this file.

What is tested when the file compiles. Each section below begins with its own account.
 1. Shapes.
 2. Numbers of scalars and claims.
 3. The order of the last key level.
 4. Refusals, by name and order.
 5. Padding keys by tree.
 6. The columns of the planes' matrix.
 7. The small configuration's numbers, and three pieces.

All guards under 1 and 3, the first 29 under 5 and the first 16 under 6 restate lines of known
answers, one guard for each line (two for a line PUBRUN). Five of the 29 restate lines PUBROWS of a
second file, verifier/tests/forest_weights.txt. The comment above a guard under 1, and above each of
these five, is the line's name in its file. The lines are typed here: no file is read. Not compared
or not tried: a line's field pre, and the numbers by tree of three groups with more than 40 trees
(1); which call a refusal names, and the names no-wrap-pin-forest and internal-forest-place (4). The
small configuration's expected numbers under 7 were recorded from a build of the C++ verifier that
is not part of the repository, and no file stores them.
-/
import OnBytes.Model.Forest

namespace OnBytes.Model.Forest.Test

/-- A group of calls with the given n and k, named c0, c1, .., each with the range table (row t has
the value t). -/
def group (n k : List Nat) : Array Call :=
  ((n.zip k).zipIdx.map fun x =>
    { name := "c" ++ toString x.2, n := x.1.1, k := x.1.2, kappa := 5 : Call }).toArray

/-- The name of a refusal; the empty string if there is none. -/
def nameOf {α : Type} : Except String α → String
  | .ok _ => ""
  | .error e => e

/-- Which of its call's trees tree y is (b(y) in the C++ record). -/
def treeOf (h : Shape) (y : Nat) : Nat := y - h.first.getD (h.callOf.getD y 0) 0

/-- A group's numbers: (dT, kT, NT, rK), then iota and first by call, then for each tree its call
and which of the call's trees it is. -/
def numbers (lid : Nat) (n k : List Nat) :
    Option (List Nat × List Nat × List Nat × List Nat × List Nat) :=
  (shape (group n k) lid).toOption.map fun h =>
    ([h.dT, h.kT, h.NT, h.rK], h.iota.toList, h.first.toList, h.callOf.toList,
      (List.range h.NT).map (treeOf h))

/-- The scalars and the claims of a lookup with v key bits and d table bits, as the C++ test writes
them out in closed form. -/
def closedForm (v d : Nat) : Nat × Nat :=
  (187 + v * (v - 1) + 5 * v + d * (d - 1) + 15 * d + (2 * d + 6) + (2 * d + 14), 32 + v + d)

/-- True if a group's numbers of scalars and claims are those of the closed form. -/
def countsHold (lid : Nat) (n k : List Nat) : Bool :=
  match shape (group n k) lid with
  | .ok h => (elems h, lins h) == closedForm h.v h.d
  | .error _ => false

/-- The name under which a group is refused after one of its calls was changed. -/
def bent (lid : Nat) (n k : List Nat) (c : Nat) (f : Call → Call) : String :=
  nameOf (shape ((group n k).modify c f) lid)

/-- The padding keys by tree of a single call of 2^n keys whose places from tot on are padding. -/
def tail (n dT tot : Nat) : Option (List Nat) :=
  ((shape (group [n] [8]) dT).bind fun h => pubRun h (noPub h) 0 tot (2 ^ n - tot)).toOption.map
    (·.toList)

/-- The same for the second of two calls, after a call of twice its size. -/
def tailBehind (n dT tot : Nat) : Option (List Nat) :=
  ((shape (group [n + 1, n] [8, 8]) dT).bind fun h =>
    pubRun h (noPub h) 1 tot (2 ^ n - tot)).toOption.map (·.toList)

/-- Counts as padding, for each entry (call, start, stride, length, number, tail): number runs of
length places each, run r from start + r stride on, and then all places of the call from tail on. -/
def rowsAndTail (lid : Nat) (n k : List Nat) (l : List (Nat × Nat × Nat × Nat × Nat × Nat)) :
    Option (List Nat) :=
  ((shape (group n k) lid).bind fun h =>
    l.foldlM
      (fun pub x => do
        let (c, start, stride, length, number, tail) := x
        let laid ← (List.range number).foldlM
          (fun p r => pubRun h p c (start + r * stride) length) pub
        pubRun h laid c tail (2 ^ n.getD c 0 - tail))
      (noPub h)).toOption.map (·.toList)

/-- Two calls of 4 and 2 trees of 2^10 keys. -/
def sixTrees : Shape := (shape (group [12, 11] [8, 8]) 10).toOption.getD {}

/-- Five runs of padding places, one after the other, in the six trees. -/
def fiveRuns : Except String (Array Nat) := do
  let a ← pubRun sixTrees (noPub sixTrees) 0 1000 100
  let b ← pubRun sixTrees a 0 2000 100
  let c ← pubRun sixTrees b 1 2047 1
  let d ← pubRun sixTrees c 1 5 0
  pubRun sixTrees d 1 2048 0

/-- The numbers of a placed call: (n, iota, k, kappa, fn, t0); of each piece (CP, off, a, b). -/
def placed (z : CallZ) : List Nat × List (List Nat) :=
  ([z.call.n, z.call.iota, z.call.k, z.call.kappa, z.call.fn, z.call.t0],
    z.pieces.toList.map fun p => [p.CP, p.off, p.a, p.b])

/-- The low digits' call of the small configuration's smallness test: one block of 128 rows by
30720 columns. -/
def lowDigits : CallZ := placeZ #[{ tree := 5, row := 0, Rp := 128, Cp := 30720 }] "R10z" 10 24

/-- The high digits' call of the same test. -/
def highDigits : CallZ :=
  placeZ #[{ tree := 5, row := 1, Rp := 128, c0 := 30720, Cp := 30720 }] "R8d" 8 24

/-- The padding keys of a lookup on placed calls: in each piece the columns from Cp on, row by row,
and all places after the last piece. -/
def fillers (h : Shape) (zs : List CallZ) : Except String (Array Nat) :=
  zs.zipIdx.foldlM
    (fun (pub : Array Nat) (x : CallZ × Nat) => do
      let inPieces ← x.1.pieces.toList.foldlM
        (fun (p : Array Nat) (e : Piece) =>
          (List.range e.Rp).foldlM
            (fun (q : Array Nat) r => pubRun h q x.2 (e.off + r * e.CP + e.Cp) (e.CP - e.Cp)) p)
        pub
      let stop := x.1.pieces.foldl (fun m e => max m (e.off + 2 ^ e.b)) 0
      pubRun h inPieces x.2 stop (2 ^ x.1.call.n - stop))
    (noPub h)

/-- The lookup of the small configuration's smallness test, with its numbers of padding keys. -/
def digits : Except String Shape := do
  let h ← shape #[lowDigits.call, highDigits.call] 24
  pure { h with pub := ← fillers h [lowDigits, highDigits] }

/-- The lookup of the small configuration's attention sub-proof: four calls of 2^20 keys, of which
the first 49152, 49152, 263168 and 131072 are not padding. -/
def attention : Except String Shape := do
  let h ← shape (group [20, 20, 20, 20] [16, 16, 16, 16]) 24
  let pub ← [49152, 49152, 263168, 131072].zipIdx.foldlM
    (fun (p : Array Nat) (x : Nat × Nat) => pubRun h p x.2 x.1 (2 ^ 20 - x.1)) (noPub h)
  pure { h with pub := pub }

/-- The numbers of a shape, in the order in which part 7 compares them. -/
def printed (h : Shape) : List (List Nat) :=
  [[h.dT, h.kT, h.NT, h.rK, h.NC, h.cK], h.iota.toList, h.first.toList, h.callOf.toList,
    h.pub.toList, [h.v, h.d, h.emptyKeys, h.padding], [elems h, lins h]]

/-! ## 1. Shapes

The shapes of the 37 lines SHAPE (32 different groups). A line's field pre is not compared. Of
three groups with more than 40 trees the numbers by tree are not compared either. Three groups
are refused; the name is the one that the C++ test expects: too many calls, or else too many
trees.
-/

-- toy.feed-forward
#guard numbers 22 [13, 14, 14, 15, 13, 13, 13, 13] [16, 16, 16, 8, 16, 16, 16, 16] == some ([13, 16,
  13, 4], [0, 1, 1, 2, 0, 0, 0, 0], [8, 4, 6, 0, 9, 10, 11, 12], [3, 3, 3, 3, 1, 1, 2, 2, 0, 4, 5,
  6, 7], [0, 1, 2, 3, 0, 1, 0, 1, 0, 0, 0, 0, 0])
-- toy.section-9
#guard numbers 22 [21, 21] [10, 8] == some ([21, 10, 2, 1], [0, 0], [0, 1], [0, 1], [0, 0])
-- toy.head
#guard numbers 22 [13, 13, 13, 13, 13, 13] [16, 16, 8, 16, 16, 16] == some ([13, 16, 6, 3], [0, 0,
  0, 0, 0, 0], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 0, 0, 0, 0, 0])
-- profile4.feed-forward
#guard numbers 22 [13, 14, 14, 15, 13, 13, 13, 13] [16, 16, 16, 8, 16, 16, 16, 16] == some ([13, 16,
  13, 4], [0, 1, 1, 2, 0, 0, 0, 0], [8, 4, 6, 0, 9, 10, 11, 12], [3, 3, 3, 3, 1, 1, 2, 2, 0, 4, 5,
  6, 7], [0, 1, 2, 3, 0, 1, 0, 1, 0, 0, 0, 0, 0])
-- profile4.section-9
#guard numbers 22 [21, 21] [10, 8] == some ([21, 10, 2, 1], [0, 0], [0, 1], [0, 1], [0, 0])
-- profile4.head
#guard numbers 22 [13, 13, 13, 13, 13, 13] [16, 16, 8, 16, 16, 16] == some ([13, 16, 6, 3], [0, 0,
  0, 0, 0, 0], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 0, 0, 0, 0, 0])
-- profile4.attention
#guard numbers 22 [13, 13, 13, 13] [16, 13, 16, 16] == some ([13, 16, 4, 2], [0, 0, 0, 0], [0, 1, 2,
  3], [0, 1, 2, 3], [0, 0, 0, 0])
-- profile4.section-9-attention
#guard numbers 22 [20, 20] [10, 8] == some ([20, 10, 2, 1], [0, 0], [0, 1], [0, 1], [0, 0])
-- profile4-12.feed-forward
#guard numbers 22 [13, 14, 14, 15, 13, 12, 12, 12] [16, 16, 16, 8, 16, 16, 16, 16] == some ([12, 16,
  23, 5], [1, 2, 2, 3, 1, 0, 0, 0], [16, 8, 12, 0, 18, 20, 21, 22], [3, 3, 3, 3, 3, 3, 3, 3, 1, 1,
  1, 1, 2, 2, 2, 2, 0, 0, 4, 4, 5, 6, 7], [0, 1, 2, 3, 4, 5, 6, 7, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 0,
  1, 0, 0, 0])
-- profile4-12.section-9-feed-forward
#guard numbers 22 [22, 22] [10, 8] == some ([22, 10, 2, 1], [0, 0], [0, 1], [0, 1], [0, 0])
-- profile4-12.section-9-head
#guard numbers 22 [21, 21] [10, 8] == some ([21, 10, 2, 1], [0, 0], [0, 1], [0, 1], [0, 0])
-- profile4-12.head
#guard numbers 22 [13, 12, 13, 12, 12, 12] [16, 16, 8, 16, 16, 16] == some ([12, 16, 8, 3], [1, 0,
  1, 0, 0, 0], [0, 4, 2, 5, 6, 7], [0, 0, 2, 2, 1, 3, 4, 5], [0, 1, 0, 1, 0, 0, 0, 0])
-- profile4-12.attention
#guard numbers 22 [12, 12, 13, 12] [16, 13, 16, 16] == some ([12, 16, 5, 3], [0, 0, 1, 0], [2, 3, 0,
  4], [2, 2, 0, 1, 3], [0, 1, 0, 0, 0])
-- profile4-12.section-9-attention
#guard numbers 22 [20, 20] [10, 8] == some ([20, 10, 2, 1], [0, 0], [0, 1], [0, 1], [0, 0])
-- small_both.feed-forward
#guard numbers 24 [20, 20, 20, 21, 20, 20, 20, 20] [16, 16, 16, 8, 16, 16, 16, 16] == some ([20, 16,
  9, 4], [0, 0, 0, 1, 0, 0, 0, 0], [2, 3, 4, 0, 5, 6, 7, 8], [3, 3, 0, 1, 2, 4, 5, 6, 7], [0, 1, 0,
  0, 0, 0, 0, 0, 0])
-- small_both.section-9
#guard numbers 24 [24, 24] [10, 8] == some ([24, 10, 2, 1], [0, 0], [0, 1], [0, 1], [0, 0])
-- small_both.head
#guard numbers 24 [20, 20, 20, 20, 20, 20] [16, 16, 8, 16, 16, 16] == some ([20, 16, 6, 3], [0, 0,
  0, 0, 0, 0], [0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 4, 5], [0, 0, 0, 0, 0, 0])
-- small_both.attention
#guard numbers 24 [20, 20, 20, 20] [16, 16, 16, 16] == some ([20, 16, 4, 2], [0, 0, 0, 0], [0, 1, 2,
  3], [0, 1, 2, 3], [0, 0, 0, 0])
-- small_both.section-9-attention
#guard numbers 24 [23, 23] [10, 8] == some ([23, 10, 2, 1], [0, 0], [0, 1], [0, 1], [0, 0])
-- full_prompt.feed-forward
#guard numbers 28 [27, 27, 27, 28, 27, 27, 26, 26] [16, 16, 16, 8, 16, 16, 16, 16] == some ([26, 16,
  16, 4], [1, 1, 1, 2, 1, 1, 0, 0], [4, 6, 8, 0, 10, 12, 14, 15], [3, 3, 3, 3, 0, 0, 1, 1, 2, 2, 4,
  4, 5, 5, 6, 7], [0, 1, 2, 3, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0])
-- full_prompt.section-9
#guard numbers 28 [27, 27] [10, 8] == some ([27, 10, 2, 1], [0, 0], [0, 1], [0, 1], [0, 0])
-- full_prompt.head
#guard numbers 28 [28, 28, 28, 27, 27, 27] [16, 16, 8, 16, 16, 16] == some ([27, 16, 9, 4], [1, 1,
  1, 0, 0, 0], [0, 2, 4, 6, 7, 8], [0, 0, 1, 1, 2, 2, 3, 4, 5], [0, 1, 0, 1, 0, 1, 0, 0, 0])
-- full_prompt.attention
#guard numbers 28 [27, 27, 26, 25] [16, 16, 16, 16] == some ([25, 16, 11, 4], [2, 2, 1, 0], [0, 4,
  8, 10], [0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 3], [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 0])
-- full_prompt.section-9-attention
#guard numbers 28 [26, 26] [10, 8] == some ([26, 10, 2, 1], [0, 0], [0, 1], [0, 1], [0, 0])
-- one-call
#guard numbers 22 [17] [8] == some ([17, 8, 1, 0], [0], [0], [0], [0])
-- one-call-of-eight-trees
#guard numbers 22 [25] [16] == some ([22, 16, 8, 3], [3], [0], [0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2,
  3, 4, 5, 6, 7])
-- all-alike
#guard numbers 22 [15, 15, 15, 15, 15] [5, 16, 9, 16, 7] == some ([15, 16, 5, 3], [0, 0, 0, 0, 0],
  [0, 1, 2, 3, 4], [0, 1, 2, 3, 4], [0, 0, 0, 0, 0])
-- rising
#guard numbers 30 [10, 11, 12, 13, 14] [8, 8, 8, 8, 8] == some ([10, 8, 31, 5], [0, 1, 2, 3, 4],
  [30, 28, 24, 16, 0], [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 3, 3, 3, 3, 3, 3, 3, 3, 2,
  2, 2, 2, 1, 1, 0], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7,
  0, 1, 2, 3, 0, 1, 0])
-- ties-among-the-large
#guard numbers 22 [14, 16, 15, 16, 14, 15, 16] [16, 8, 16, 8, 16, 8, 16] == some ([14, 16, 18, 5],
  [0, 2, 1, 2, 0, 1, 2], [16, 0, 12, 4, 17, 14, 8], [1, 1, 1, 1, 3, 3, 3, 3, 6, 6, 6, 6, 2, 2, 5, 5,
  0, 4], [0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 2, 3, 0, 1, 0, 1, 0, 0])
-- cap-below-all
#guard (numbers 23 [30, 28, 29] [16, 16, 16]).map (fun x => (x.1, x.2.1, x.2.2.1)) == some ([23, 16,
  224, 8], [7, 5, 6], [0, 192, 128])
-- cap-above-all
#guard numbers 30 [24, 26] [10, 8] == some ([24, 10, 5, 3], [0, 2], [4, 0], [1, 1, 1, 1, 0], [0, 1,
  2, 3, 0])
-- sixteen-calls
#guard numbers 22 [12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12] [16, 16, 16, 16,
  16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16] == some ([12, 16, 16, 4], [0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], [0, 1, 2, 3, 4,
  5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
-- seventeen-calls
#guard nameOf (shape (group [12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12, 12]
  [16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16]) 22) == "forest-calls"
-- trees-256
#guard (numbers 22 [29, 28, 27, 26, 25, 24, 23, 22, 22] [16, 16, 16, 16, 16, 16, 16, 16, 16]).map
  (fun x => (x.1, x.2.1, x.2.2.1)) == some ([22, 16, 256, 8], [7, 6, 5, 4, 3, 2, 1, 0, 0], [0, 128,
  192, 224, 240, 248, 252, 254, 255])
-- trees-257
#guard nameOf (shape (group [29, 28, 27, 26, 25, 24, 23, 22, 22, 22] [16, 16, 16, 16, 16, 16, 16,
  16, 16, 16]) 22) == "forest-trees"
-- trees-256-alike
#guard (numbers 22 [26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26, 26] [16, 16, 16, 16,
  16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16, 16]).map (fun x => (x.1, x.2.1, x.2.2.1)) == some
  ([22, 16, 256, 8], [4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4], [0, 16, 32, 48, 64, 80, 96,
  112, 128, 144, 160, 176, 192, 208, 224, 240])
-- widest
#guard nameOf (shape (group [62, 55] [16, 5]) 30) == "forest-trees"

/-! ## 2. Numbers of scalars and claims

The numbers of scalars and of claims. The closed form of the C++ test is compared at six groups
(the C++ test compares it at all 34 lines SHAPE that are not refused), with v and d as
Forest.shape gives them (the C++ test works them out from the line). Then the worked example of
the C++ test, and two numbers of a small configuration (see 7). Then the number of calls and of
the bits of a call's number at eight groups, and the keys in trees that hold only padding.
-/

#guard countsHold 22 [13, 14, 14, 15, 13, 13, 13, 13] [16, 16, 16, 8, 16, 16, 16, 16]
#guard countsHold 22 [21, 21] [10, 8]
#guard countsHold 24 [20, 20, 20, 20] [16, 16, 16, 16]
#guard countsHold 28 [27, 27, 26, 25] [16, 16, 16, 16]
#guard countsHold 22 [17] [8]
#guard countsHold 30 [10, 11, 12, 13, 14] [8, 8, 8, 8, 8]
-- the worked example of the C++ test
#guard elems { dT := 26, rK := 4, kT := 16, cK := 3 } == 1930
-- the small configuration's attention sub-proof: its own lookup, then that of its smallness test
#guard (shape (group [20, 20, 20, 20] [16, 16, 16, 16]) 24).toOption.map elems == some 1427
#guard elems { dT := 22, rK := 1, kT := 10, cK := 1 } == 1147
-- the number of calls, and the least cK with 2^cK at least that number
#guard [1, 2, 3, 4, 5, 8, 9, 16].map (fun c =>
    (shape (group (List.replicate c 10) (List.replicate c 5)) 10).toOption.map
      fun h => (h.NC, h.cK))
  == [some (1, 0), some (2, 1), some (3, 2), some (4, 2), some (5, 3), some (8, 3), some (9, 4),
    some (16, 4)]
-- six trees of eight numbers: two trees of 2^10 keys hold only padding
#guard sixTrees.emptyKeys == 2048

/-! ## 3. The order of the last key level

The order of the last key level (the lines ORDER).
-/

#guard orderForestRange 9 0 == [2, 1, 0, 5, 4, 3, 8, 7, 6]
#guard orderForestRange 10 1 == [3, 2, 1, 6, 5, 4, 9, 8, 7, 0]
#guard orderForestRange 12 3 == [5, 4, 3, 8, 7, 6, 11, 10, 9, 2, 1, 0]
#guard orderForestRange 12 2 == [4, 3, 2, 7, 6, 5, 10, 9, 8, 11, 1, 0]
#guard orderForestRange 16 4 == [6, 5, 4, 9, 8, 7, 12, 11, 10, 15, 14, 13, 3, 2, 1, 0]
#guard orderForestRange 16 5 == [7, 6, 5, 10, 9, 8, 13, 12, 11, 15, 14, 4, 3, 2, 1, 0]
#guard orderForestRange 21 1 == [3, 2, 1, 6, 5, 4, 9, 8, 7, 20, 19, 18, 17, 16, 15, 14, 13, 12, 11,
  10, 0]
#guard orderForestRange 29 4 == [6, 5, 4, 9, 8, 7, 12, 11, 10, 28, 27, 26, 25, 24, 23, 22, 21, 20,
  19, 18, 17, 16, 15, 14, 13, 3, 2, 1, 0]
#guard orderForestRange 30 4 == [6, 5, 4, 9, 8, 7, 12, 11, 10, 29, 28, 27, 26, 25, 24, 23, 22, 21,
  20, 19, 18, 17, 16, 15, 14, 13, 3, 2, 1, 0]
#guard orderForestRange 28 4 == [6, 5, 4, 9, 8, 7, 12, 11, 10, 27, 26, 25, 24, 23, 22, 21, 20, 19,
  18, 17, 16, 15, 14, 13, 3, 2, 1, 0]
#guard orderForestRange 37 8 == [10, 9, 8, 13, 12, 11, 16, 15, 14, 36, 35, 34, 33, 32, 31, 30, 29,
  28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 7, 6, 5, 4, 3, 2, 1, 0]
#guard orderForestRange 29 8 == [10, 9, 8, 13, 12, 11, 16, 15, 14, 28, 27, 26, 25, 24, 23, 22, 21,
  20, 19, 18, 17, 7, 6, 5, 4, 3, 2, 1, 0]

/-! ## 4. Refusals, by name and order

The refusals of a group, by name and order: the cases of the C++ test. Its two cases with a
negative number have no counterpart here, since all numbers are natural numbers. Where the C++
name ends in the call's name, the name here ends before it, so no guard shows which call was
named. Of the 14 names in Forest.names, no guard of this file expects no-wrap-pin-forest or
internal-forest-place.
-/

#guard bent 22 [12, 13, 12] [8, 16, 5] 0 id == ""
-- the tests on a call: its sizes, the floor on its keys, its planes
#guard bent 22 [12, 13, 12] [8, 16, 5] 1 (fun c => { c with k := 4 }) == "shape-pt-words"
#guard bent 22 [12, 13, 12] [8, 16, 5] 1 (fun c => { c with k := 17 }) == "shape-pt-words"
#guard bent 22 [12, 13, 12] [8, 16, 5] 1 (fun c => { c with k := 5 }) == ""
#guard bent 22 [12, 13, 12] [8, 16, 5] 0 (fun c => { c with fn := 3 }) == "shape-pt-words"
#guard bent 22 [12, 13, 12] [8, 16, 5] 0 (fun c => { c with fn := 2 }) == ""
#guard bent 22 [12, 13, 12] [8, 16, 5] 2 (fun c => { c with t0 := 32 }) == "shape-pt-words"
#guard bent 22 [12, 13, 12] [8, 16, 5] 2 (fun c => { c with t0 := 31 }) == ""
#guard bent 22 [12, 13, 12] [8, 16, 5] 2 (fun c => { c with tau := some (Array.replicate 31 7) })
  == "shape-pt-words"
#guard bent 22 [12, 13, 12] [8, 16, 5] 2 (fun c => { c with tau := some (Array.replicate 32 7) })
  == ""
#guard bent 22 [12, 13, 12] [8, 16, 5] 0 (fun c => { c with n := 63 }) == "shape-pt-words"
#guard bent 22 [12, 13, 12] [8, 16, 5] 0 (fun c => { c with n := 0 }) == "hid-call-floor"
#guard bent 22 [12, 13, 12] [8, 16, 5] 0 (fun c => { c with n := 9 }) == "hid-call-floor"
#guard bent 22 [12, 13, 12] [8, 16, 5] 0 (fun c => { c with n := 10 }) == ""
#guard bent 22 [12, 13, 12] [8, 16, 5] 1 (fun c => { c with kappa := 4 }) == "hid-planes"
#guard bent 22 [12, 13, 12] [8, 16, 5] 1 (fun c => { c with kappa := 6 }) == "hid-planes"
#guard bent 22 [12, 13, 12] [8, 16, 5] 2 (fun c => { c with heavy := [[]] }) == "hid-planes"
-- the number of calls, the depth, the number of trees
#guard bent 22 [] [] 0 id == "forest-calls"
#guard bent 22 (List.replicate 17 12) (List.replicate 17 8) 0 id == "forest-calls"
#guard bent 22 (List.replicate 16 12) (List.replicate 16 8) 0 id == ""
#guard bent 9 [12, 13, 12] [8, 16, 5] 0 id == "forest-depth"
#guard bent 10 [12, 13, 12] [8, 16, 5] 0 id == ""
#guard bent 10 [18, 10] [8, 8] 0 id == "forest-trees"
#guard bent 10 [17, 17] [8, 8] 0 id == ""
#guard bent 10 [62, 62] [8, 8] 0 id == "forest-trees"
-- the number of keys, counting the trees that hold only padding
#guard bent 30 [30, 30] [8, 8] 0 id == ""
#guard bent 30 [31, 30] [8, 8] 0 id == "forest-keys"
#guard bent 31 [31, 31] [8, 8] 0 id == "forest-keys"
#guard bent 31 [31] [8] 0 id == ""
#guard bent 24 [33, 24] [8, 8] 0 id == "forest-trees"
-- a row of a written table is a number below the prime
#guard bent 22 [12, 13, 12] [8, 16, 5] 2 (fun c => { c with tau := some (Array.replicate 32 pW) })
  == "forest-row-value"
-- with two faults, the name is that of the test that comes first
#guard bent 22 [12, 13, 12] [8, 16, 5] 0 (fun c => { c with k := 4, n := 9 })
  == "shape-pt-words"
#guard bent 22 [12, 13, 12] [8, 16, 5] 0 (fun c => { c with n := 9, kappa := 4 })
  == "hid-call-floor"
#guard nameOf (shape (((group [12, 13, 12] [8, 16, 5]).modify 0
  fun c => { c with kappa := 4 }).modify 1 fun c => { c with k := 4 }) 22) == "hid-planes"
#guard bent 22 (List.replicate 17 12) (List.replicate 17 8) 16 (fun c => { c with k := 4 })
  == "shape-pt-words"
#guard bent 9 (List.replicate 17 12) (List.replicate 17 8) 0 id == "forest-calls"
#guard bent 9 [18, 10] [8, 8] 0 id == "forest-depth"

/-! ## 5. Padding keys by tree

The padding keys of a call whose places from tot on are padding (the lines PUBRUN), for the
call by itself and, as in the C++ test, after a call of twice its size. Then many runs and a
tail, as in a smallness test (the lines PUBROWS of verifier/tests/forest_weights.txt), and the
C++ test's cases of runs that add up and of a caller's faults, except its case with a negative
number. Then cases of this file's own for pubAsk.
-/

#guard tail 27 25 94371840 == some ([0, 0] ++ [6291456] ++ [33554432])
#guard tailBehind 27 25 94371840 == some (List.replicate 8 0 ++ [0, 0] ++ [6291456] ++ [33554432])
#guard tail 13 12 5000 == some ([0] ++ [3192])
#guard tailBehind 13 12 5000 == some (List.replicate 4 0 ++ [0] ++ [3192])
#guard tail 13 12 4096 == some ([0] ++ [4096])
#guard tailBehind 13 12 4096 == some (List.replicate 4 0 ++ [0] ++ [4096])
#guard tail 13 12 4095 == some ([1] ++ [4096])
#guard tailBehind 13 12 4095 == some (List.replicate 4 0 ++ [1] ++ [4096])
#guard tail 13 12 8192 == some ([0, 0])
#guard tailBehind 13 12 8192 == some (List.replicate 4 0 ++ [0, 0])
#guard tail 13 12 1 == some ([4095] ++ [4096])
#guard tailBehind 13 12 1 == some (List.replicate 4 0 ++ [4095] ++ [4096])
#guard tail 12 12 4000 == some ([96])
#guard tailBehind 12 12 4000 == some (List.replicate 2 0 ++ [96])
#guard tail 12 12 4096 == some ([0])
#guard tailBehind 12 12 4096 == some (List.replicate 2 0 ++ [0])
#guard tail 15 12 12288 == some ([0, 0, 0] ++ List.replicate 5 4096)
#guard tailBehind 15 12 12288 == some (List.replicate 16 0 ++ [0, 0, 0] ++ List.replicate 5 4096)
#guard tail 15 12 12289 == some ([0, 0, 0] ++ [4095] ++ List.replicate 4 4096)
#guard tailBehind 15 12 12289 == some (List.replicate 16 0 ++ [0, 0, 0] ++ [4095] ++ List.replicate
  4 4096)
#guard tail 15 12 20000 == some (List.replicate 4 0 ++ [480] ++ [4096, 4096, 4096])
#guard tailBehind 15 12 20000 == some (List.replicate 16 0 ++ List.replicate 4 0 ++ [480] ++ [4096,
  4096, 4096])
#guard tail 16 10 1025 == some ([0] ++ [1023] ++ List.replicate 62 1024)
#guard tailBehind 16 10 1025 == some (List.replicate 128 0 ++ [0] ++ [1023] ++ List.replicate 62
  1024)
-- list-order-is-not-the-trees
#guard rowsAndTail 10 [12, 14, 13] [8, 8, 8] [(0, 37, 51, 30, 65, 3400), (2, 5, 100, 60, 30, 8000)]
  == some [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 619, 624, 557, 0, 0, 0, 0, 192, 588, 604,
  604, 850]
-- two-calls-alike
#guard rowsAndTail 10 [13, 13] [10, 8] [(0, 50, 64, 14, 96, 6144), (1, 50, 64, 14, 96, 6144)] ==
  some [224, 224, 224, 224, 224, 224, 1024, 1024, 224, 224, 224, 224, 224, 224, 1024, 1024]
-- a-run-over-three-trees
#guard rowsAndTail 10 [11, 12] [8, 8] [(0, 1000, 512, 100, 2, 2048), (1, 500, 4096, 2000, 1, 4000)]
  == some [524, 1024, 452, 96, 24, 176]
-- no-tail-and-no-run
#guard rowsAndTail 10 [11, 11] [8, 8] [(0, 0, 1, 0, 0, 2048), (1, 1023, 1, 2, 1, 2048)] == some [0,
  0, 1, 1]
-- every-place
#guard rowsAndTail 10 [10, 11] [8, 8] [(0, 0, 1, 0, 0, 0)] == some [0, 0, 1024]
-- runs add up; a run of no place changes nothing; a run may end at the call's last place
#guard fiveRuns.toOption == some #[24, 124, 52, 0, 0, 1]
-- a caller's faults
#guard nameOf (pubRun sixTrees (Array.replicate 5 0) 0 0 1) == "internal-forest-pub"
#guard nameOf (pubRun sixTrees (noPub sixTrees) 2 0 1) == "internal-forest-pub"
#guard nameOf (pubRun sixTrees (noPub sixTrees) 1 2048 1) == "internal-forest-pub"
#guard nameOf (pubRun sixTrees (noPub sixTrees) 1 2049 0) == "internal-forest-pub"
#guard nameOf (pubRun sixTrees (noPub sixTrees) 1 1 (2 ^ 64 - 1)) == "internal-forest-pub"
-- what must hold of the numbers of padding keys (cases of this file's own)
#guard nameOf (pubAsk sixTrees #[24, 124, 52, 0, 0, 1]) == ""
#guard nameOf (pubAsk sixTrees #[1024, 1024, 1024, 1023, 1024, 0]) == ""
#guard nameOf (pubAsk sixTrees #[0, 0, 0, 0, 1025, 0]) == "pt-pub-forest"
#guard nameOf (pubAsk sixTrees #[0, 0, 0, 0, 1024, 1024]) == "forest-only-padding"
#guard nameOf (pubAsk sixTrees #[1024, 1024, 1024, 1024, 0, 0]) == "forest-only-padding"
#guard nameOf (pubAsk sixTrees #[0, 0, 0, 0, 0]) == "internal-forest-pub"
-- a shape whose list of calls has another length than its number of calls
#guard nameOf (pubAsk { sixTrees with calls := #[] } #[0, 0, 0, 0, 0, 0]) == "internal-forest-pub"

/-! ## 6. The columns of the planes' matrix

The columns of the planes' matrix (the lines PLANES; their field NT is read as the number of
calls, as the C++ test reads it), and the two ends of the range of lm, the logarithm of the
number of that matrix's rows.
-/

#guard (planeCols { kT := 16, NC := 13 } 12).toOption == some 6656
#guard (planeCols { kT := 16, NC := 4 } 11).toOption == some 4096
#guard (planeCols { kT := 16, NC := 6 } 12).toOption == some 3072
#guard (planeCols { kT := 16, NC := 23 } 13).toOption == some 5888
#guard (planeCols { kT := 16, NC := 5 } 11).toOption == some 5120
#guard (planeCols { kT := 16, NC := 8 } 12).toOption == some 4096
#guard (planeCols { kT := 16, NC := 9 } 13).toOption == some 2304
#guard (planeCols { kT := 16, NC := 4 } 13).toOption == some 1024
#guard (planeCols { kT := 16, NC := 6 } 13).toOption == some 1536
#guard (planeCols { kT := 16, NC := 16 } 16).toOption == some 512
#guard (planeCols { kT := 16, NC := 11 } 14).toOption == some 1408
#guard (planeCols { kT := 16, NC := 9 } 15).toOption == some 576
#guard (planeCols { kT := 10, NC := 2 } 5).toOption == some 2048
#guard (planeCols { kT := 10, NC := 2 } 15).toOption == some 2
#guard (planeCols { kT := 5, NC := 1 } 10).toOption == some 1
#guard (planeCols { kT := 16, NC := 256 } 21).toOption == some 256
#guard nameOf (planeCols { kT := 10, NC := 3 } 4) == "forest-planes"
#guard nameOf (planeCols { kT := 10, NC := 3 } 5) == ""
#guard nameOf (planeCols { kT := 10, NC := 3 } 15) == ""
#guard nameOf (planeCols { kT := 10, NC := 3 } 16) == "forest-planes"

/-! ## 7. The small configuration's numbers, and three pieces

A small configuration (64 tokens, eight layers in two groups of four, four query heads, two
heads of keys and values): the lookup of the attention sub-proof, the two calls and the lookup
of that sub-proof's smallness test, and the numbers of scalars and claims of the smallness test
in a sub-proof of layers. The sizes that go into the functions (the calls' n and k, the numbers
of keys that are not padding, the blocks' rows and columns) are typed in this file; no file is
read, and the examples under prover/examples may have other numbers. The expected numbers are
the C++ verifier's at this configuration. They were recorded from a run of the C++ verifier with
added lines that only print; that build is not part of the repository, and no file stores them.
A reader can check them by hand: n, k, dT, kT, NT, first and pub of the attention's lookup are
those of the line APUB small_both of verifier/tests/forest_weights.txt; the numbers of scalars
and claims are those of the closed form; a block of 128 rows by 30720 columns takes 128 rows of
32768 places, 2048 of them padding. Then two cases of this file's own, worked out by hand:
placeZ with three pieces to order, and padRun.
-/

#guard attention.toOption.map printed == some [[20, 16, 4, 2, 4, 2], [0, 0, 0, 0], [0, 1, 2, 3],
  [0, 1, 2, 3], [999424, 999424, 785408, 917504], [22, 18, 0, 3701760], [1427, 72]]
#guard nameOf (attention.bind fun h => pubAsk h h.pub) == ""
#guard placed lowDigits == ([22, 0, 10, 5, 0, 0], [[32768, 0, 7, 22]])
#guard placed highDigits == ([22, 0, 8, 5, 0, 0], [[32768, 0, 7, 22]])
#guard digits.toOption.map printed == some [[22, 10, 2, 1, 2, 1], [0, 0], [0, 1], [0, 1],
  [262144, 262144], [23, 11, 0, 524288], [1147, 66]]
#guard lowDigits.call.pub == #[262144]
-- the smallness test in a sub-proof of layers: two calls of 2^23 keys (128 rows by 65536 columns),
-- no padding; the two numbers are closedForm 24 11
#guard (shape (group [23, 23] [10, 8]) 24).toOption.map (fun h => (elems h, lins h))
  == some (1198, 67)
-- the three pairs of scalars and claims above are those of the closed form
#guard (closedForm 22 18, closedForm 23 11, closedForm 24 11) ==
  ((1427, 72), (1147, 66), (1198, 67))
-- Three pieces of 16, 16 and 64 key places. The largest comes first; the two of one size keep their
-- order. 2^10 keys in four parts: key i counts under i mod 4.
#guard placed (placeZ #[{ Rp := 4, Cp := 3 }, { Rp := 2, Cp := 8 }, { Rp := 8, Cp := 5 }] "z" 10 8)
  == ([10, 2, 10, 5, 0, 0], [[4, 64, 2, 4], [8, 80, 1, 4], [8, 0, 3, 6]])
#guard (placeZ #[{ Rp := 4, Cp := 3 }, { Rp := 2, Cp := 8 }, { Rp := 8, Cp := 5 }] "z" 10
  8).call.pub == #[232, 240, 240, 244]
#guard padRun 2 #[0, 0, 0, 0] 5 3 == #[0, 1, 1, 1]
#guard padRun 2 #[0, 0, 0, 0] 6 9 == #[2, 2, 3, 2]

end OnBytes.Model.Forest.Test
