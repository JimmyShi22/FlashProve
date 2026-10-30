-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2Types.lean: the second toy's verifier. This file defines:
  its sizes (`Par`);
  a group of several oracle messages and its layout (`Mem`, `starts`);
  a row with a form on a kept table (`KRow`);
  an opened column laid on a group's rows (`KCol`).

The second toy (a chain of three links: x_(m+1) = c_m = x_m b_m, entry by entry) is a test protocol
of the programs (the C++ implementation that comes with this Lean code). Definitions only, with
guards. A guard is a test (#guard), which Lean evaluates when the file compiles. Core Lean; every
function is total; generic in the sizes and in the number of links. Written from the programs'
description of that toy (sections 0 to 6; its part on the frame of a chain of links; each of the two
written by one writer). Rendered: that text. This file builds on the first toy's
files (Fmt/M1Types.lean: vector arithmetic, rounds, views, stages; Fmt/M1Codes.lean).
The head of Fmt/M2Dec.lean tells how the protocol runs (seeds, answers, lists of positions,
closings). The frame is that file's pass through the rounds of the chain of links (`decBy`,
`goLinks`). At a closing all open rows of a group are batched into one. The head of Fmt/M2Loc.lean
tells of the switch between two links and of the carrying message (here `memG`).

What differs from the first toy, as far as types go. One prover's message holds several oracle
messages in one tree. Those that are tested together form a group; its main rows are laid side by
side in one table of 2^k rows. A message that the next link reads again is kept: its main row is a
symbol of the leaf, but no row of the group's table; coefficients on it are gathered in a form of
their own.

Main names:
  `Mem`: an oracle message as a member of a group: its real main rows; whether these are over the
    extension field; its mask rows; whether it is sampled; whether it is kept.
  `clog n`: the least b with n ≤ 2^b.
  `starts ms`: the layout: a member with R real rows takes a block of 2^(clog R) rows; blocks are
    laid from row 0 by decreasing size, ties in the order of joining (the order of the list ms); a
    kept member, or one without rows, takes none.
  `hOf`, `kOf`: h: the least number such that 2^h rows hold the mask blocks; k: the least such that
    2^k rows hold the main blocks, at least max(h, 1).
  `maskStarts`: the same for mask rows.
  `lay k f b n v`: a form on a member's own table (2^b rows: entry (row r, place p) at r + 2^b p)
    carried to the group's table of n entries: entry (f + r) + 2^k p.
  `KRow`: a row on a group: c on the main table, kp on the kept member's own table (empty where the
    group has none), d on the mask table, the target t. It stands for this equation:
    <c, main> + <kp, kept> + <d, mask> = t.
    There is at most one kept member, kept for one link: this is the toy's case. A message kept for
    more than one link (a life above 1) and several kept messages at once, which the format page's
    rules on a chain of links allow, are not rendered.
  `KSRow`: what a fold hands on: the first toy's claim on three virtual rows (`SRow`,
    Fmt/M1Types.lean; the head of Fmt/M1Fold.lean says what they are), and kp on the kept table,
    which is not folded.
  `MRow`, `oneAt`, `axpyL`, `sumMFrom`, `sumM`, `layAll`, `toK`: a row member by member: each form
    on its member's own table. Laying is linear: so rows are batched in this shape (tables of l or
    2 l entries) and laid into the group's table (2^k l entries) once. `toK` gives the row on the
    group; the kept member's form becomes kp. That batching and laying commute: Fmt/M2CloseEq.lean
    (`toK_sumM`, for a list of rows that is not empty).
  `cubeOf`: the number of coordinates that a sampled message reads of the shared point (without
    mask rows: its table's own index bits, no coordinate on top).
  `seedLen`: the number of coordinates of that point: as many as the largest `cubeOf` asks.
  `cutParts degs nz w`: a leaf's column: main symbols in the order of the parts, each over the
    extension field (three words) or the base field (one word, embedded), then nz mask symbols over
    the extension field; nothing behind them.
  `KCol`, `groupCol`: an opened column laid on the group's rows. It has:
      2^k main symbols by the layout (0 at rows that nobody sent);
      the kept row's symbol apart, as it stands;
      2^h old mask symbols (0 where the group has no mask row);
      the fresh mask symbols.
  `Par`: the sizes: the field; the links' main code C and mask code Z; t positions at each list of
    the frame; the number of links; the stages of the last proximity test, whose first is the last
    group's (a clause of `sizesOK`, Fmt/M2Dec.lean); work, salt (Notation).
  `memsOf L m`: the toy's groups, m = 1 .. L + 1. Group 1: "b" (two rows x_1, b_1 over the base
    field; one mask row), "c" (one row; kept if a link follows). Group m: the carrying message (two
    rows over the extension field), the former "c" sent anew, "b" (one row; one mask row), "c".
    Group L + 1: the carrying message alone.

Guards: at three links the four groups of the text: k; h; the rows at which the members begin; the
widths of the four trees' columns; the number of the seeds' elements; the number of answers.

Notation:
  `Code`, written ⟨a, l, r⟩: a code: codewords of length 2^a, messages of l entries, a random tail
    of r entries (Fmt/M1Codes.lean);
  `Stage`, written ⟨C, Z, k, h, t⟩: a stage of the proximity test: main code C, mask code Z, 2^k
    main rows, 2^h mask rows, t positions drawn (Fmt/M1Types.lean);
  natural numbers:
    `work`: bits of work on each draw of positions;
    `salt`: bytes of a leaf's salt
    (both as in the first toy's `Par`, Fmt/M1Types.lean).

Limits: No theorem says that these are what the programs compute. Compared with the programs on
their own files of this toy, by tests (#guard): the parameter bytes, every round, 34 intermediate
values and the outcome on three honest proofs, 39 altered copies and 27 false proofs:
Fmt/M2Theirs.lean, Fmt/M2EngineLT.lean, Fmt/M2EngineLR.lean, Fmt/M2EngineLF.lean and the files
beside them (the verifier on bytes); Run/M2EngineT1.lean and the files beside it (the run functions
of the generic construction). The tests named here stand on the files that come with this code. This
file says nothing on soundness.
One place where the toy, as its text has it and as it is rendered here, is not the letter of a print
of our own paper (found in a second, independent reading, which compared it with that print's
part on kept rows; that finding is not checked and stands here as a question): a kept member's
main rows are not among the group's 2^k rows; the print has them at places among these, replaced
there by zero rows: another k, one round of a fold fewer here. (The toy's form is also a rule of the
format page: a kept message's rows count in the group in which its life ends, alone.) (In the text
the old sample row of a kept message
also stands as a row of its own at the next closing, right behind the carried claim, as the print
has it; it stands among its own link's batched rows as well.)

Terms: lean/GLOSSARY.md.
-/
import Fmt.M1Types

namespace Fmt.M2
open Fmt.M1

/-- An oracle message as a member of a group. -/
structure Mem where
  rows    : Nat
  overE   : Bool
  masks   : Nat := 0
  sampled : Bool := true
  kept    : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- the least b with n ≤ 2^b -/
def clog (n : Nat) : Nat := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- Blocks of 2^(size i) rows, laid from row 0 by decreasing size, ties in the given order; a member
without a block: none. The result: the starts, in the given order; the rows taken. -/
def layBlocks (sizes : List (Option Nat)) : List (Option Nat) × Nat :=
  let idx : List (Nat × Nat) := sizes.zipIdx.filterMap fun x => x.1.map fun e => (x.2, e)
  let top : Nat := idx.foldl (fun m x => max m x.2) 0
  let order : List (Nat × Nat) :=
    (List.range (top + 1)).reverse.flatMap fun e => idx.filter fun x => x.2 == e
  let put : List (Nat × Nat) × Nat :=
    order.foldl (fun s x => ((x.1, s.2) :: s.1, s.2 + 2 ^ x.2)) ([], 0)
  ((List.range sizes.length).map fun i => (put.1.find? fun y => y.1 == i).map (·.2), put.2)

/-- The layout of the main rows. -/
def starts (ms : List Mem) : List (Option Nat) × Nat :=
  layBlocks (ms.map fun m => if m.kept || m.rows == 0 then none else some (clog m.rows))

/-- the layout of the mask rows -/
def maskStarts (ms : List Mem) : List (Option Nat) × Nat :=
  layBlocks (ms.map fun m => if m.masks == 0 then none else some (clog m.masks))

def hOf (ms : List Mem) : Nat := clog (maskStarts ms).2
def kOf (ms : List Mem) : Nat := max (clog (starts ms).2) (max (hOf ms) 1)

/-- A form on a member's own table, carried to the group's table; n: the entries of the group's
table. By selection: entry i of the result is an entry of v, or 0: nothing is added. -/
def lay (k f b n : Nat) (v : Array E) : Array E :=
  Array.ofFn (n := n) fun i =>
    if f ≤ i.val % 2 ^ k && i.val % 2 ^ k < f + 2 ^ b then
      ent v ((i.val % 2 ^ k - f) + 2 ^ b * (i.val / 2 ^ k))
    else Fld.zeroE

/-- A row on a group. -/
structure KRow where
  c  : Array E
  kp : Array E := #[]
  d  : Array E
  t  : E
  deriving Inhabited

/-- What a fold hands on. -/
structure KSRow where
  s  : SRow
  kp : Array E := #[]
  deriving Inhabited

def KRow.ofG (G : GRow) : KRow := ⟨G.c, #[], G.d, G.t⟩
def KRow.toG (R : KRow) : GRow := ⟨R.c, R.d, R.t⟩

/-- The sum of the rows with the coefficients 1, x, x^2, .. -/
def sumK (f : Fld) (x : E) (rows : List KRow) : KRow :=
  (rows.foldl
    (fun (s : KRow × E) R =>
      (⟨axpy f s.1.c s.2 R.c, axpy f s.1.kp s.2 R.kp,
          axpy f s.1.d s.2 R.d, f.addE s.1.t (f.mulE s.2 R.t)⟩,
        f.mulE s.2 x))
    (⟨#[], #[], #[], Fld.zeroE⟩, Fld.oneE)).1

/-- the row holds of these tables -/
def KRow.holdsAt (f : Fld) (R : KRow) (main kept mask : Array E) : Bool :=
  f.addE (dot f R.c main) (f.addE (dot f R.kp kept) (dot f R.d mask)) == R.t

/-- A row, member by member: for each member of a group, in the order of joining, a form on that
member's own main table and one on its own mask table (empty: zero); the target. Laying a form into
the group's table is linear: so rows are batched in this shape and laid once. -/
structure MRow where
  main : List (Array E)
  mask : List (Array E)
  t    : E
  deriving Inhabited

/-- v at member i of n, nothing elsewhere -/
def oneAt (n i : Nat) (v : Array E) : List (Array E) :=
  (List.range n).map fun j => if j == i then v else #[]

/-- u + s v, member by member; the result has the longer list's length. A member that one of the two
lacks counts as the empty form, so member number j of the result is `axpy` of the two members number
j, for every j. -/
def axpyL (f : Fld) : List (Array E) → E → List (Array E) → List (Array E)
  | a :: u, s, b :: v => axpy f a s b :: axpyL f u s v
  | [], s, v => v.map (axpy f #[] s)
  | u, s, [] => u.map fun a => axpy f a s #[]

/-- The sum of the rows with the coefficients first, first x, first x^2, ..; and the next power. -/
def sumMFrom (f : Fld) (x first : E) (rows : List MRow) : MRow × E :=
  rows.foldl (fun (s : MRow × E) R =>
      (⟨axpyL f s.1.main s.2 R.main, axpyL f s.1.mask s.2 R.mask, f.addE s.1.t (f.mulE s.2 R.t)⟩,
        f.mulE s.2 x))
    (⟨[], [], Fld.zeroE⟩, first)

def sumM (f : Fld) (x : E) (rows : List MRow) : MRow := (sumMFrom f x Fld.oneE rows).1

/-- Which member's block holds row r: (the member's number, the row at which its block begins, the
bits of its rows); j: the number of the list's first member. -/
def pickRow : List (Option Nat × Nat) → Nat → Nat → Option (Nat × Nat × Nat)
  | [], _, _ => none
  | (some st, b) :: xs, r, j =>
    if st ≤ r && r < st + 2 ^ b then some (j, st, b) else pickRow xs r (j + 1)
  | (none, _) :: xs, r, j => pickRow xs r (j + 1)

/-- The members' forms laid side by side; w: the bits of the table's rows; n: its entries; L: for
each member where its block begins and the bits of its rows. By selection: entry i of the result is
an entry of one member's form, or 0: nothing is added. -/
def layAll (w n : Nat) (L : List (Option Nat × Nat)) (parts : List (Array E)) : Array E :=
  Array.ofFn (n := n) fun i =>
    match pickRow L (i.val % 2 ^ w) 0 with
    | some (j, st, b) => ent (parts.getD j #[]) ((i.val % 2 ^ w - st) + 2 ^ b * (i.val / 2 ^ w))
    | none => Fld.zeroE

/-- the number of the kept member -/
def keptFrom : List Mem → Nat → Option Nat
  | [], _ => none
  | m :: ms, j => if m.kept then some j else keptFrom ms (j + 1)
def keptIdx (ms : List Mem) : Option Nat := keptFrom ms 0

/-- The row on the group; l, lz: the entries of a main row, of a mask row. -/
def toK (ms : List Mem) (l lz : Nat) (R : MRow) : KRow where
  c := layAll (kOf ms) (2 ^ kOf ms * l) ((starts ms).1.zip (ms.map fun m => clog m.rows)) R.main
  kp := match keptIdx ms with
    | some j => R.main.getD j #[]
    | none => #[]
  d :=
    layAll (hOf ms) (2 ^ hOf ms * lz) ((maskStarts ms).1.zip (ms.map fun m => clog m.masks)) R.mask
  t := R.t

/-- A row that a switch between two links makes: g on the carrying message's own table (two rows:
entry (row r, place p) at r + 2 p), p on the table of the kept message sent anew (empty where there
is none), the target. -/
structure LRow where
  g : Array E
  p : Array E := #[]
  t : E
  deriving Inhabited

/-- The same as a row member by member of a group of n members, whose first is the carrying message
and whose second, if the row has a part there, is the kept message sent anew. -/
def LRow.toM (n : Nat) (R : LRow) : MRow :=
  ⟨(List.range n).map fun j => if j == 0 then R.g else if j == 1 then R.p else #[], [], R.t⟩

/-- The cube of a sampled message: with mask rows: the larger of the two tables' index bits, and one
coordinate on top; without: its main table's own index bits and no more. lgl, lgz: the logarithms of
a main row's and a mask row's length. -/
def cubeOf (lgl lgz : Nat) (m : Mem) : Nat :=
  if m.masks == 0 then clog m.rows + lgl else max (clog m.rows + lgl) (clog m.masks + lgz) + 1

/-- The coordinates of the one point that all sampled messages of a prover's message share: the
largest cube; each reads the first coordinates. -/
def seedLen (lgl lgz : Nat) (ms : List Mem) : Nat :=
  (ms.filter (·.sampled)).foldl (fun a m => max a (cubeOf lgl lgz m)) 0

/-- main symbols in the order of the parts -/
def takeParts : List Bool → List UInt64 → Option (List E × List UInt64)
  | [], w => some ([], w)
  | true :: ds, a :: b :: c :: w => (takeParts ds w).map fun x => ((a, b, c) :: x.1, x.2)
  | false :: ds, a :: w => (takeParts ds w).map fun x => (Fld.ofF a :: x.1, x.2)
  | _ :: _, _ => none

/-- A leaf's column: (the main symbols, the mask symbols). -/
def cutParts (degs : List Bool) (nz : Nat) (w : List UInt64) : Option (List E × List E) :=
  match takeParts degs w with
  | none => none
  | some (ms, w') =>
    match takeE nz w' with
    | some (zs, []) => some (ms, zs)
    | _ => none

/-- the main symbols' degrees (true: over the extension field), in the order of the parts -/
def degsOf (ms : List Mem) : List Bool := ms.flatMap fun m => List.replicate m.rows m.overE

/-- a column's width in words of the base field; fresh: the number of fresh mask rows in it -/
def widthOf (ms : List Mem) (fresh : Nat) : Nat :=
  ((degsOf ms).map fun e => if e then 3 else 1).sum + 3 * ((ms.map (·.masks)).sum + fresh)

/-- An opened column, laid on a group's rows. -/
structure KCol where
  col  : Col
  kept : Option E
  deriving Inhabited

/-- a list of symbols cut into pieces of the given lengths, member by member -/
def splitBy : List Nat → List E → List (List E)
  | [], _ => []
  | n :: ns, l => l.take n :: splitBy ns (l.drop n)

/-- symbols put at their rows -/
def putRows (n : Nat) (xs : List (Option Nat × List E)) : Array E :=
  Array.ofFn (n := n) fun i =>
    ((xs.findSome? fun x =>
      x.1.bind fun f =>
        if f ≤ i.val && i.val < f + x.2.length then x.2[i.val - f]? else none).getD Fld.zeroE)

/-- The column of a group's tree. -/
def groupCol (ms : List Mem) (fresh : Nat) (w : List UInt64) : Option KCol :=
  (cutParts (degsOf ms) ((ms.map (·.masks)).sum + fresh) w).map fun x =>
    let mains := splitBy (ms.map (·.rows)) x.1
    let nOld := (ms.map (·.masks)).sum
    let olds := splitBy (ms.map (·.masks)) (x.2.take nOld)
    ⟨⟨putRows (2 ^ kOf ms) ((starts ms).1.zip mains),
        putRows (2 ^ hOf ms) ((maskStarts ms).1.zip olds),
        (x.2.drop nOld).toArray⟩,
      ((ms.zip mains).find? fun y => y.1.kept).bind fun y => y.2.head?⟩

/-- The sizes. -/
structure Par where
  fld    : Fld
  C      : Code
  Z      : Code
  t      : Nat
  links  : Nat
  stages : List Stage
  work   : Nat := 20
  salt   : Nat := 40

/-- the variables of a link's sum-check: a vector fills the lower half of a row -/
def Par.V (P : Par) : Nat := Nat.log2 P.C.l - 1

def memG : Mem := { rows := 2, overE := true }
def memB (m : Nat) : Mem := { rows := if m == 1 then 2 else 1, overE := false, masks := 1 }
def memP (kept : Bool) : Mem := { rows := 1, overE := false, kept := kept }

/-- The toy's groups, m = 1 .. L + 1. -/
def memsOf (L m : Nat) : List Mem :=
  if m == 1 then [memB 1, memP (decide (1 < L))]
  else if m ≤ L then [memG, memP false, memB m, memP (decide (m < L))]
  else [memG]

/-- the number of answers after the seed of group m's prover's message -/
def nAns (P : Par) (m : Nat) : Nat := ((memsOf P.links m).filter (·.sampled)).length

/-- The number of rows that are batched at the closing of group m. Counted are:
  the carried claim (m > 1);
  the old sample row of the former group's kept message, if it has one;
  a link's three rows;
  the sample rows (one for each answer: `nAns`);
  for each draw (each of the `Par.t` drawn positions), four rows if the former group has a kept row,
  else three. -/
def nRowsAt (P : Par) (m : Nat) : Nat :=
  (if m == 1 then 0 else 1) + (if 1 < m && m - 1 < P.links then 1 else 0) +
    (if m ≤ P.links then 3 else 0) + nAns P m +
    (if m == 1 then 0 else (if m - 1 < P.links then 4 else 3) * P.t)

/-- The programs' parameters: the full ones; the tiny ones, which reach no security level. -/
def toyPar : Par :=
  ⟨.two, ⟨15, 4096, 73⟩, ⟨15, 32, 73⟩, 73, 3,
    [⟨⟨15, 4096, 73⟩, ⟨15, 32, 73⟩, 1, 0, 73⟩, ⟨⟨14, 2048, 74⟩, ⟨14, 256, 74⟩, 1, 1, 74⟩,
      ⟨⟨14, 2048, 74⟩, ⟨14, 1024, 74⟩, 0, 0, 74⟩],
    20, 40⟩
def tinyPar : Par :=
  ⟨.two, ⟨9, 64, 3⟩, ⟨9, 16, 3⟩, 3, 3,
    [⟨⟨9, 64, 3⟩, ⟨9, 16, 3⟩, 1, 0, 3⟩, ⟨⟨9, 32, 3⟩, ⟨9, 32, 3⟩, 1, 1, 3⟩,
      ⟨⟨10, 32, 3⟩, ⟨10, 128, 3⟩, 0, 0, 3⟩],
    6, 40⟩

/-! ## Tests -/

#guard [1, 2, 3, 4].map (nRowsAt toyPar) == [5, 301, 301, 221] && [1, 2, 3, 4].map (nRowsAt tinyPar) == [5, 21, 21, 11]
#guard (toyPar.V, tinyPar.V) == (11, 5)

#guard (List.range 9).map clog == [0, 0, 1, 2, 2, 3, 3, 3, 3]
-- elements drawn in the four seeds, full and tiny parameters: the point's coordinates, the factor
#guard [1, 2, 3, 4].map (fun m => seedLen 12 5 (memsOf 3 m) + 1) == [15, 14, 14, 14]
#guard [1, 2, 3, 4].map (fun m => seedLen 6 4 (memsOf 3 m) + 1) == [9, 8, 8, 8]
-- the answers after them
#guard [1, 2, 3, 4].map (fun m => ((memsOf 3 m).filter (·.sampled)).length) == [2, 4, 4, 1]
-- the four groups of the toy of three links
#guard [1, 2, 3, 4].map (fun m => (kOf (memsOf 3 m), hOf (memsOf 3 m))) == [(1, 0), (2, 0), (3, 0), (1, 0)]
#guard (starts (memsOf 3 1)).1 == [some 0, none]
#guard (starts (memsOf 3 2)).1 == [some 0, some 2, some 3, none]
#guard (starts (memsOf 3 3)).1 == [some 0, some 2, some 3, some 4]
#guard (starts (memsOf 3 4)).1 == [some 0]
#guard [1, 2, 3, 4].map (fun m => (maskStarts (memsOf 3 m)).1) == [[some 0, none], [none, none, some 0, none], [none, none, some 0, none], [none]]
#guard [1, 2, 3, 4].map (fun m => widthOf (memsOf 3 m) 1) == [9, 15, 15, 9]
-- a larger block goes first, whatever the order of joining; ties in the order of joining
#guard (starts [{ rows := 1, overE := false }, { rows := 3, overE := true }, { rows := 1, overE := false }, { rows := 2, overE := true }]).1 == [some 6, some 0, some 7, some 4]
-- a form on a member's table of two rows, laid at row 2 of a table of eight rows with two places
#guard lay 3 2 1 16 #[(1, 0, 0), (2, 0, 0), (3, 0, 0), (4, 0, 0)] == #[(0, 0, 0), (0, 0, 0), (1, 0, 0), (2, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (3, 0, 0), (4, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)]
#guard lay 1 0 1 4 #[(1, 0, 0), (2, 0, 0), (3, 0, 0), (4, 0, 0)] == #[(1, 0, 0), (2, 0, 0), (3, 0, 0), (4, 0, 0)]
#guard (lay 3 4 0 32768 (zerosE 4096)).size == 32768
-- a column of the second tree: G's two symbols, c anew, b, c; then b's mask symbol, the fresh one
#guard ((groupCol (memsOf 3 2) 1 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]).map fun c => (c.col.main, c.kept, c.col.mask, c.col.fresh)) ==
  some (#[(1, 2, 3), (4, 5, 6), (7, 0, 0), (8, 0, 0)], some (9, 0, 0), #[(10, 11, 12)], #[(13, 14, 15)])
-- of the third: c is a row of the group
#guard ((groupCol (memsOf 3 3) 1 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]).map fun c => (c.col.main, c.kept)) ==
  some (#[(1, 2, 3), (4, 5, 6), (7, 0, 0), (8, 0, 0), (9, 0, 0), (0, 0, 0), (0, 0, 0), (0, 0, 0)], none)
-- of the first; of the last group's: no old mask row was sent: its symbol counts as 0
#guard ((groupCol (memsOf 3 1) 1 [1, 2, 3, 4, 5, 6, 7, 8, 9]).map fun c => (c.col.main, c.kept, c.col.mask, c.col.fresh)) == some (#[(1, 0, 0), (2, 0, 0)], some (3, 0, 0), #[(4, 5, 6)], #[(7, 8, 9)])
#guard ((groupCol (memsOf 3 4) 1 [1, 2, 3, 4, 5, 6, 7, 8, 9]).map fun c => (c.col.main, c.kept, c.col.mask, c.col.fresh)) == some (#[(1, 2, 3), (4, 5, 6)], none, #[(0, 0, 0)], #[(7, 8, 9)])
#guard (groupCol (memsOf 3 4) 1 [1, 2, 3, 4, 5, 6, 7, 8]).isNone && (groupCol (memsOf 3 4) 1 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]).isNone
-- a row member by member, laid: group 2 at rows of two places: G's table (stride 2), c anew, b, the
-- kept c
#guard (let R : MRow := ⟨[#[(1, 0, 0), (2, 0, 0), (3, 0, 0), (4, 0, 0)], #[(5, 0, 0), (6, 0, 0)], #[(7, 0, 0), (8, 0, 0)], #[(9, 0, 0), (10, 0, 0)]], [#[], #[], #[(11, 0, 0)], #[]], (1, 0, 0)⟩
  let K := toK (memsOf 3 2) 2 1 R
  (K.c, K.kp, K.d)) == (#[(1, 0, 0), (2, 0, 0), (5, 0, 0), (7, 0, 0), (3, 0, 0), (4, 0, 0), (6, 0, 0), (8, 0, 0)], #[(9, 0, 0), (10, 0, 0)], #[(11, 0, 0)])
-- batching and laying commute (at an example)
#guard (let R1 : MRow := ⟨[#[(1, 0, 0), (2, 0, 0), (3, 0, 0), (4, 0, 0)], #[], #[(7, 0, 0), (8, 0, 0)], #[(9, 0, 0)]], [#[], #[], #[(11, 0, 0)], #[]], (1, 0, 0)⟩
  let R2 : MRow := ⟨[#[], #[(5, 0, 0), (6, 0, 0)], #[(1, 0, 0)], #[(0, 0, 0), (2, 0, 0)]], [#[], #[], #[(3, 0, 0)], #[]], (4, 0, 0)⟩
  let a := toK (memsOf 3 2) 2 1 (sumM .two (3, 1, 0) [R1, R2])
  let b := sumK .two (3, 1, 0) [toK (memsOf 3 2) 2 1 R1, toK (memsOf 3 2) 2 1 R2]
  (a.c, a.kp, a.d, a.t) == (b.c, b.kp, b.d, b.t))
#guard (sumK .two (2, 0, 0) [⟨#[(1, 0, 0)], #[(1, 0, 0)], #[], (1, 0, 0)⟩, ⟨#[(1, 0, 0), (1, 0, 0)], #[(5, 0, 0)], #[(3, 0, 0)], (1, 0, 0)⟩]).kp == #[(11, 0, 0)]

end Fmt.M2
