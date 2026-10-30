-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Witness.lean: a synthetic input of the prover's, for trials of the honest
prover of the layers' own rounds (K4). Definitions with code, and ten tests of two helpers. No
theorem.

WHAT IT IS NOT. NO MODEL IS RUN HERE. The cells are small synthetic numbers, and so are the weights.
A proof made of this input would be rejected: no cell is tied to a product with a weight, to a
rounding or to a table: the lookup's keys, which are whole numbers made of cells and weights, do not
lie in their tables, so that the lookup's own claims fail. The cells of the lookup's planes are not
the bits of any keys' multiplicities. Nothing here is laid for the smallness test or for the
attention segment, and nothing tries them.

WHAT IT DEFINES. By our reading of the format's page (docs/format/11-2-feed-forward-segment.md, "The
claims, group by group") these of K4's groups of claims bind cells to each other or to the weights;
each is met here as far as is said:
  groups 5 and 6   each norm's row of digits is reckoned from its stream (`normCells`)
  group 10         each selector is 1 at one expert and 0 at the others
  group 11, third  the planes' cells, each under 2 to the power of its row's number modulo 32, add
                   up to the number of keys that are not padding: a few cells are 1 so that they do
                   (`madePlanes`); all others are 0
  group 12         in the first group of layers the stream that comes in is the embedding of the
                   request's tokens under the synthetic weights
  group 14, first  the lookup's join: the end of the lookup's key side is the keys' value at the
                   lookup's point. The keys are committed nowhere: they have a value at any cells.
                   So this claim asks nothing of the cells; it asks that value of whoever lays the
                   state in front.
The other claims speak of scalars that the prover sends and of the reads: they are met, at any
cells, if the prover makes its scalars of these cells as the format says: a trial tries that.
  `madeInt`, `limbsOf`   a small whole number of three numbers; a whole number in limbs
  `layCell`, `madePick`  one cell written into the arrays; the expert that a selector picks
  `madePlanes`          which cells of the lookup's planes are 1
  `Made`, `madeWith`, `made`, `everyThird`   THE INPUT: cells, weights, tokens; with some streams
                         small; with none; which streams a second input has small
  `Made.input`           the same as the small input that K4's parts read (`K4In`)
  `bentCell`, `bentWeight`, `bentToken`   the input with one cell, weight or token turned by one

How the cells are laid. Each matrix but the lookup's planes is an array that is filled once; the
selectors, the small streams' high limbs and the stream that comes in are written over the synthetic
ones at the places that `featAt` (Johnson/Desc/K4/Honest/Cells.lean) gives. The norms' rows are
written into no array: `cellWithRows` (Johnson/Desc/K4/Honest/NormCells.lean) reads them from
`normCells`' array, by a rule of placement that is typed there. The embedding's entries are read off
the synthetic matrix of weights by `fbTable` (Johnson/Desc/K4/Honest/Units.lean) with both index
groups left open. The planes' matrix is no array: a cell of it is 1 if `madePlanes` lists it.

WHAT THE TEN TESTS TRY, AND WHAT THEY DO NOT. They are evaluations by Lean's evaluator at the build:
no proof. Five try `limbsOf`: four written answers, and at ten whole numbers that five limbs add up
to the number again. Five try `madeInt`: at 200 arguments it stays from -9 to 9; its values move
with the seed and with each of its three numbers. NO TEST OF THIS FILE TRIES THE INPUT ITSELF:
`madeWith`, `made`, `madePlanes`, `madePick`, `layCell` and the three bent inputs are tried, if at
all, where a trial calls them; that the groups of claims named above are met is said of the text by
reading.

Limits. The arrays are made where `made` is called: call it once and pass the structure on. At the
scales of the small plan no stream has both high pieces other than 0: so the product of the two is 0
at every input.
Nothing on any property.
No property is claimed.
-/
import Johnson.Desc.K4.Honest.NormCells
import Johnson.Desc.K4.Honest.Units

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest
open OnBytes
open OnBytes.Model (fOfInt tenCell Forest.Heard)
open OnBytes.Model.Layer (matIx)

/-- A whole number from -r to r, of a seed and three numbers. -/
def madeInt (r seed a b c : Nat) : Int :=
  let x := (((seed * 1000003 + a) * 1000003 + b) * 1000003 + c + 12345) % 2305843009213693951
  Int.ofNat (x * 2654435761 / 8192 % (2 * r + 1)) - Int.ofNat r

/-- The n limbs of a whole number to the base 256, the lowest first, each but the last from -128 to
127; the last takes what is left. -/
def limbsOf : Nat → Int → List Int
  | 0, _ => []
  | 1, x => [x]
  | n + 2, x =>
    let d := (x + 128) % 256 - 128
    d :: limbsOf (n + 1) ((x - d) / 256)

#guard limbsOf 3 0 == [0, 0, 0]
#guard limbsOf 3 (-1) == [-1, 0, 0]
#guard limbsOf 3 200 == [-56, 1, 0]
#guard limbsOf 3 (-70000) == [-112, -17, -1]
#guard [0, 5, -5, 127, 128, -128, -129, 70000, -70000, 8388607].all fun x =>
  ((limbsOf 5 x).zipIdx.foldl (fun s l => s + l.1 * 256 ^ l.2) 0) == x
#guard (List.range 200).all fun i => -9 ≤ madeInt 9 1 2 3 i && madeInt 9 1 2 3 i ≤ 9
-- the synthetic numbers move with each of their four arguments
#guard (List.range 40).map (madeInt 9 1 2 3) != (List.range 40).map (madeInt 9 2 2 3)
#guard (List.range 40).map (madeInt 9 1 2 3) != (List.range 40).map (madeInt 9 1 3 3)
#guard (List.range 40).map (madeInt 9 1 2 3) != (List.range 40).map (madeInt 9 1 2 4)
#guard ((List.range 40).map (madeInt 9 1 2 3)).eraseDups.length > 10

/-- **A synthetic input.** -/
structure Made where
  /-- a cell: the matrix's number in the segment's list, the row, the column -/
  cell : Nat → Nat → Nat → F
  /-- an entry of the matrix of the weights' digits: row, column -/
  w : Nat → Nat → F
  /-- the request's tokens -/
  tokv : Array Nat

/-- One cell written into the matrices' arrays; a matrix of m rows holds the cell of row r and
column c at c m + r. -/
def layCell (mats : Array (Nat × Nat)) (A : Array (Array F)) (at_ : Nat × Nat × Nat) (x : F) :
    Array (Array F) :=
  A.modify at_.1 fun a => a.setIfInBounds (at_.2.2 * (mats.getD at_.1 (0, 0)).1 + at_.2.1) x

/-- The expert that the synthetic selector of the layer number lm with routed experts picks at token
t. -/
def madePick (NE seed lm t : Nat) : Nat := (seed + 3 * lm + 5 * t + t / 3) % NE

/-- **Which cells of the lookup's planes are 1**: (row, column). By the format's page the planes'
cells, each under 2 to the power of its row's number modulo 32, add up to the number of keys that
are not padding. For each 1 bit i of that number one cell, in a row whose number is i modulo 32.
Nothing asks that the matrix has that row: 32 (7 i + 3) + i, at most 7071; the small plan's has
8192. -/
def madePlanes (y : Model.Layer.Lay) : List (Nat × Nat) :=
  let n := 2 ^ y.fo.v - y.fo.padding
  (List.range 32).filterMap fun i =>
    if n.testBit i then some (32 * (7 * i + 3) + i, (97 * i + 5) % y.kbm) else none

/-- **The synthetic input at a place.** seed: any number. tokv: the request's tokens. small: the
residual streams inside the group (number 1 to 2 Lam - 1) whose limbs from the third on are laid 0.
Why, at the small plan's scales (M = 44): a stream with synthetic cells in all its limbs is so large
that its norm's reciprocal is below 2^24, so that the reciprocal's high piece is 0; a stream of two
limbs has a root below 2^24, so that the root's high piece is 0 and the reciprocal's is not. -/
def madeWith (Q : K4Pub) (seed : Nat) (tokv : Array Nat) (small : Nat → Bool) : Made :=
  let y := Q.P.y
  let lay := Q.P.wsLay
  let mats := matsOf Q
  let iB := (matIx y).iB
  let cols := 2 ^ lay.lk
  -- the weights' digits
  let W : Array F := (Array.range (lay.m0 * cols)).map fun x =>
    fOfInt (madeInt 5 (seed + 1) 0 (x / cols) (x % cols))
  let w : Nat → Nat → F := fun r c => if c < cols then W.getD (r * cols + c) 0 else 0
  -- synthetic cells everywhere but in the lookup's planes
  let A0 : Array (Array F) := mats.mapIdx fun mu mk =>
    if mu == iB then #[]
    else (Array.range (mk.1 * mk.2)).map fun x => fOfInt (madeInt 9 seed mu (x % mk.1) (x / mk.1))
  -- group 10: the selectors
  let sel := tensorOf y "sel"
  let A1 := (List.range (y.LamM * y.h.NE * y.T)).foldl
    (fun A x =>
      let t := x % y.T
      let e := x / y.T % y.h.NE
      let lm := x / y.T / y.h.NE
      layCell mats A (featAt y sel.mat (tenCell sel.place 0 lm e) t)
        (if e == madePick y.h.NE seed lm t then 1 else 0))
    A0
  -- the small streams
  let xs := tensorOf y "xs"
  let A1 := (List.range (xs.cnt * (y.h.xl - 2) * y.h.d * y.T)).foldl
    (fun A x =>
      let t := x % y.T
      let j := x / y.T % y.h.d
      let lb := 2 + x / y.T / y.h.d % (y.h.xl - 2)
      let ix := x / y.T / y.h.d / (y.h.xl - 2)
      if small (ix + 1) then layCell mats A (featAt y xs.mat (tenCell xs.place lb ix j) t) 0 else A)
    A1
  -- group 12: the stream that comes in
  let A2 :=
    if Q.g != 0 then A1
    else
      match lay.unitOf 12 y.h.L with
      | none => A1
      | some ui =>
        let blank := (lay.U.getD ui {}).g.map fun _ => {}
        let emb := fbTable lay w { ui := ui, f := blank } ["v", "x"]
        (List.range (y.h.d * y.T)).foldl
          (fun A x =>
            let t := x % y.T
            let j := x / y.T
            let v := intOfF (emb.getD (tokv.getD t 0 * y.h.d + j) zeroE).c0
            (limbsOf y.h.xl v).zipIdx.foldl
              (fun A l => layCell mats A (featAt y 5 (tenCell y.xb l.2 0 j) t) (fOfInt l.1)) A)
          A1
  let planes := madePlanes y
  let read : Nat → Nat → Nat → F := fun mu r c =>
    if mu == iB then (if planes.contains (r, c) then 1 else 0)
    else (A2.getD mu #[]).getD (c * (mats.getD mu (0, 0)).1 + r) 0
  -- groups 5 and 6: the norms' rows
  let rows := normCells Q read
  { cell := cellWithRows Q rows read, w := w, tokv := tokv }

/-- The synthetic input with no stream laid small. -/
def made (Q : K4Pub) (seed : Nat) (tokv : Array Nat) : Made := madeWith Q seed tokv fun _ => false

/-- Every third stream, from the first inside the group on. -/
def everyThird (sg : Nat) : Bool := sg % 3 == 1

/-- The input as the small input that K4's parts read. look: what the lookup in front has sampled.
-/
def Made.input (m : Made) (look : List Fmt.Drawn → Forest.Heard) : K4In :=
  { cell := m.cell, w := m.w, tokv := m.tokv, look := look }

/-- The input with one cell raised by one. -/
def bentCell (m : Made) (mu r c : Nat) : Made :=
  { m with cell := fun a b d => addF (m.cell a b d) (if a == mu && b == r && d == c then 1 else 0) }

/-- The input with one entry of the weights' matrix raised by one. -/
def bentWeight (m : Made) (r c : Nat) : Made :=
  { m with w := fun a b => addF (m.w a b) (if a == r && b == c then 1 else 0) }

/-- The input with the token at position t replaced by the next one, below V. -/
def bentToken (m : Made) (V t : Nat) : Made :=
  { m with tokv := m.tokv.modify t fun x => (x + 1) % V }

end OnBytes.Desc.First.K4.Honest
