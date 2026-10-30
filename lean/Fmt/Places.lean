-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Fmt/Places.lean: where an entry stands, and which number a thing has: the byte format's own rules
for numberings and places, as functions on natural numbers.

The programs (the C++ implementation that comes with this Lean code) number the entries of an oracle
message, the free entries of its mask rows, the coefficients of a hiding polynomial and the keys of
a lookup by fixed rules, which the format page writes down. A description of the protocol that only
proves that such numberings exist can take these functions as the values of its arguments. Nothing
is invented here: every function restates a sentence of the format page, and its comment names the
place.

Sources. The format page that ships: docs/format/FORMAT.md (13.4, step 7; 13.9), docs/format/
09-key-and-leaf-files.md (the head of section 9; 9.1), docs/format/11-1-machinery.md ("The numbers
of its scalars"; "The hiding polynomial"; 11.1's lookup; "The lookup on the digits"); one sentence
of FORMAT.md 18. The file imports nothing: no
Mathlib is below it.

The line "Place" at the end of a comment is the function's place on the format page.

1. What the file contains.
    `logUp`: the least b with n ≤ 2 ^ b.
    `entryNo`, `entryAt`: the number of an entry of a table of rows, the row's bits low; back.
    `tableBits`, `cubeBits`, `cubeNo`: the cube of an oracle message with main and mask rows.
    `padInMask`, `padRow`, `padEach`, `padEntry`: the pad of an out-of-domain sample.
    `freeCount`, `freeAt`: the free entries of an oracle message's mask rows, in their order.
    `vecAt`: where entry j of a vector stands in an oracle message's main rows.
    `blockAt`: where an element of a block of the layout file stands.
    `sk`, `hidPos`, `hidCount`, `sentNo`, `endNo`: a sumcheck with a hiding sum: which entry holds
      which coefficient of the hiding polynomial; the numbers of its scalars.
    `keyNo`, `isKey`, `keyBits`, `keyIndex`: the key numbers of the lookup on the digits, and a
      key's index among the keys of both calls.

2. What is checked when the file compiles. Only the types. Tests: Fmt/PlacesKnown.lean.

3. Theorems. None here: Fmt/PlacesLaws.lean.

4. What is not claimed, and what is not here.
   That these functions are what the programs compute: they follow the format page, which says of
   each of these passages that it is from the programs' source. No file of the programs was read
   for this file.
   A function on natural numbers has a value outside the page's range too (a row that is not there,
   a pad longer than its row, degree 0 of a variable that is not the last). Such a value means
   nothing. Where a function has a law (Fmt/PlacesLaws.lean), the law's hypotheses say which
   arguments are meant; for `vecAt`, `blockAt`, `sentNo`, `endNo` only their comments do.
   Not here: where each member's rows are among a group's rows (`layBlocks`, `starts`,
   `maskStarts`, Fmt/M2Types.lean); how many coordinates a point has that several oracle messages
   share (`seedLen`, there); which blocks a layout file has; a stored table's pads (R13.8); where
   the second part of a folded row's vector begins (`t0Of`, Fmt/M3Types.lean); the order of the rows
   in a batching (10-proof-file.md 10.6), which is an order of lists; that a vector ends before the
   pad's first entry (`vectorRoom`, OnBytes/Iop/Foldeq.lean); a key's index in a lookup other than
   that on the digits.
   Like rules stand in other texts of this library, each for its own use. None is imported here.
   Proved equal to a function of this file, under the conditions that each theorem states: in
   Fmt/PlacesTies.lean `Fmt.M2.clog`, `Fmt.M2.cubeOf`, `Fmt.M1.nCoord`, `Fmt.M2.padAt`, `hiAt`,
   `Fmt.M1.ledger`, `pscTakes`; in OnBytes/Iop/SendPlaces.lean `ceilLog2`, the five numbers of
   `Send.cube`, `Send.pad`, `Send.freeMaskEntries`; in OnBytes/Iop/LedgerPlaces.lean `nextRealRow`
   and `VectorLay.index`. `cubeNo`, `blockAt`, `hidPos`, `sentNo`, `endNo` and the four functions on
   keys are tied to no other text. The list:
    `logUp`: `Fmt.M2.clog`, `ceilLog2` (OnBytes/Iop/Ground.lean), `clog2`
      (OnBytes/Params/Group.lean).
    The cube: `Send.cube` (OnBytes/Iop/Send.lean), `Statement.tableBits` (OnBytes/Iop/Ground.lean),
      `cubeBitsOf` (OnBytes/Params/DeriveLin.lean), `Fmt.M2.cubeOf`, `Fmt.M1.nCoord`
      (Fmt/M1Send.lean).
    The free entries: `Send.freeMaskEntries` (OnBytes/Iop/Send.lean), `Ledger`, `nextRealRow`,
      `Blk.takeMask` (OnBytes/Iop/Ground.lean), `freshLedger` (OnBytes/Slice/BlkCalls.lean),
      `Fmt.M1.ledger`.
    The pad: `Send.pad`, `Fmt.M2.padAt` (Fmt/M2Send.lean).

    A vector: `VectorLay.index` (OnBytes/Iop/Tensor.lean), `vectorLay` (OnBytes/Iop/Foldeq.lean),
      `hiAt`, `loAt` (Fmt/M3Types.lean).
    A sumcheck: `hidingEntries`, `hidingWalk`, `masksOf` (OnBytes/Iop/Psc.lean), `pscTakes` and the
      rows (U), (E_1), (E_2) (Fmt/M1Psc.lean).

Terms: lean/GLOSSARY.md.
-/

namespace Fmt.Places

/-- The least b with n ≤ 2 ^ b.
Place: 09-key-and-leaf-files.md, the head of section 9 ("let 2^q be the least power of two that is
at least m"). -/
def logUp (n : Nat) : Nat := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-! ## The entries of a table of rows -/

/-- The number of entry c of row r in a table of m rows: the row's bits are low.
Place: 09-key-and-leaf-files.md, the head of section 9 ("Entry c of row r has the number
r + 2^q c"); FORMAT.md 13.9, "after a root, round SEND seed" ("row bits low"). -/
def entryNo (m r c : Nat) : Nat := r + 2 ^ logUp m * c

/-- The entry with the number n, as (row, entry of the row); none where the low bits are m or more.
The function does not know how long a row is: a number beyond the rows' end names no entry either.
Place: 09-key-and-leaf-files.md, the head of section 9 ("a number whose low q bits are m or more
names no entry and is passed over"). -/
def entryAt (m n : Nat) : Option (Nat × Nat) :=
  if n % 2 ^ logUp m < m then some (n % 2 ^ logUp m, n / 2 ^ logUp m) else none

/-! ## The cube of an oracle message -/

/-- The bits of a table of rows whose messages have 2 ^ logLen entries; 0 for no row.
Place: FORMAT.md 13.9, "after a root, round SEND seed". -/
def tableBits (rows logLen : Nat) : Nat := if rows = 0 then 0 else logUp rows + logLen

/-- The bits of an oracle message's cube: with one table that table's bits; with both the larger
number plus 1. It is how many coordinates of the point of an out-of-domain sample this message
reads, the first ones; a point that several messages share has as many as the largest cube.
Place: FORMAT.md 13.9, "after a root, round SEND seed". -/
def cubeBits (mainRows mainLog maskRows maskLog : Nat) : Nat :=
  if mainRows ≠ 0 ∧ maskRows ≠ 0 then
    max (tableBits mainRows mainLog) (tableBits maskRows maskLog) + 1
  else tableBits mainRows mainLog + tableBits maskRows maskLog

/-- The index in the cube of entry c of row r, a number whose bit t belongs to coordinate t of the
point: the entry's number in its table; with both tables the top bit is 0 for the main table and 1
for the mask table. An entry of the pad has an index like every other entry; the sample's row does
not weigh it by the point.
Place: FORMAT.md 13.9, "after a root, round SEND seed" and "round SEND answer". -/
def cubeNo (mainRows mainLog maskRows maskLog : Nat) (mask : Bool) (r c : Nat) : Nat :=
  entryNo (if mask then maskRows else mainRows) r c +
    (if mask ∧ mainRows ≠ 0 ∧ maskRows ≠ 0 then
      2 ^ (cubeBits mainRows mainLog maskRows maskLog - 1) else 0)

/-! ## The pad -/

/-- Whether the pad is in the mask rows: it is, if the message has a mask row.
Place: FORMAT.md 13.9, the table's row after "after a root, round SEND seed";
09-key-and-leaf-files.md, the head of section 9 ("The pad"). -/
def padInMask (maskRows : Nat) : Bool := maskRows != 0

/-- The pad's row: the last mask row, or the last main row if there is no mask row.
Place: as `padInMask`. -/
def padRow (mainRows maskRows : Nat) : Nat := if maskRows != 0 then maskRows - 1 else mainRows - 1

/-- How many entries the pad has for each answer: one in a mask row and in a main row over E, three
in a main row over F, read through the basis 1, X, X^2. overE: whether the main rows are over E; it
is read only where the pad is in no mask row.
Place: as `padInMask`. -/
def padEach (inMask overE : Bool) : Nat := if inMask || overE then 1 else 3

/-- The pad's entry number t, below each, of answer i, from 0, in a row whose message has len
entries, for s answers. It is meant only where the pad fits the row, each * s ≤ len: a verifier
rejects any other shape.
Place: as `padInMask` ("Answer i, from 0, has entry l - s + i of that row …; for main rows over F
the three entries from l - 3 s + 3 i on"). -/
def padEntry (len s each i t : Nat) : Nat := len - each * s + each * i + t

/-! ## The free entries of the mask rows -/

/-- How many free entries m mask rows of e entries have, for s answers: those with a number below
that of the pad's first entry, which is entry e - s of row m - 1; none where a row is shorter than
the pad. The page speaks of free entries only where a sample has been answered, so s is at least 1.
Place: 09-key-and-leaf-files.md, the head of section 9 ("they are m (e - s) + (m - 1)"); FORMAT.md
18, the row of a pad ("which is 0 where a mask row is shorter than the pad"). -/
def freeCount (m e s : Nat) : Nat := if m = 0 ∨ e < s then 0 else m * (e - s) + (m - 1)

/-- The k-th free entry, from 0, of m mask rows, as (row, entry of the row): by increasing number.
Place: 09-key-and-leaf-files.md, the head of section 9 ("entry 0 of row 0, entry 0 of row 1, and so
on to row m - 1, then entry 1 of row 0"). -/
def freeAt (m k : Nat) : Nat × Nat := (k % m, k / m)

/-! ## A vector in main rows; an element of a block -/

/-- Where entry j of a vector stands in R main rows whose messages have l entries, as (row, entry of
the row). high: the item's word that says that the rows' index is in the high bits. Where the word
is 0 the page has R a power of two, and no value for another R.
Place: 09-key-and-leaf-files.md, the head of section 9 ("Where a vector is in an oracle message's
main rows"). -/
def vecAt (high : Bool) (l R j : Nat) : Nat × Nat := if high then (j / l, j % l) else (j % R, j / R)

/-- Where the element (R + i, K + c) of an array, i below 2 ^ a and c below 2 ^ e, stands by a
block's line with the words a, e, low, row, place, bj, as (row, position) in the line's group, which
in the layout file is one oracle message: lowR says that the letter low is r.
Place: FORMAT.md 13.4, step 7 ("A block's line"). -/
def blockAt (lowR : Bool) (a e row place bj i c : Nat) : Nat × Nat :=
  let x := if lowR then c * 2 ^ a + i else i * 2 ^ e + c
  (row + x / 2 ^ bj, place + x % 2 ^ bj)

/-! ## A sumcheck with a hiding sum

ks: for each variable, in the order of the rounds (a further variable Y, if there is one, last), the
number of scalars that its round sends. It is the round polynomial's degree, because one coefficient
is not sent. -/

/-- The number of scalars that the rounds before variable l send.
Place: 11-1-machinery.md, "The numbers of its scalars". -/
def sk (ks : List Nat) (l : Nat) : Nat := (ks.take l).sum

/-- Which of the sumcheck's entries, from 0, holds the hiding polynomial's coefficient of degree deg
in variable l: by variable, in the order of the rounds, and within a variable by increasing degree;
from degree 1 for every variable but the last, from degree 0 for the last.
Place: 11-1-machinery.md, "The hiding polynomial" (pos(l, deg)); 09-key-and-leaf-files.md 9.1,
item 3; FORMAT.md 13.9, "a sumcheck with a hiding sum". -/
def hidPos (ks : List Nat) (l deg : Nat) : Nat :=
  if l + 1 < ks.length then sk ks l + deg - 1 else sk ks l + deg

/-- How many coefficients the hiding polynomial has.
Place: 11-1-machinery.md, "The hiding polynomial" ("That makes 1 + sk(NV) coefficients"). -/
def hidCount (ks : List Nat) : Nat := 1 + ks.sum

/-- The number, counted from the sumcheck's first scalar, of the i-th scalar that the round of
variable l sends. The hiding polynomial's sum has the number 0.
Place: 11-1-machinery.md, "The numbers of its scalars". -/
def sentNo (ks : List Nat) (l i : Nat) : Nat := 1 + sk ks l + i

/-- The number, counted from the sumcheck's first scalar, of end value i. It is a scalar's number.
From which oracle message the entry comes that masks an end value differs from use to use.
Place: 11-1-machinery.md, "The numbers of its scalars" (jE + i). -/
def endNo (ks : List Nat) (i : Nat) : Nat := 1 + ks.sum + i

/-! ## The lookup on the digits -/

/-- The key number, in either of the lookup's two calls, that belongs to row u of ZZ and the cell
row crow: call 0 has the low digit there, call 1 the high digit. lc is logUp mz.
Place: 11-1-machinery.md, "The lookup on the digits", "The keys". -/
def keyNo (lc u crow : Nat) : Nat := u * 2 ^ lc + crow

/-- Whether a key number is no padding position: u below tau and the cell row below mz.
Place: 11-1-machinery.md, "The lookup on the digits", "The keys". -/
def isKey (tau lc mz x : Nat) : Bool := x / 2 ^ lc < tau && x % 2 ^ lc < mz

/-- Each call has 2 ^ keyBits key numbers (the page's n_Z).
Place: 11-1-machinery.md, "The lookup on the digits", "The keys". -/
def keyBits (tau lc : Nat) : Nat := max 10 (logUp tau + lc)

/-- The index, among the keys of both calls, of key number x of a call (0 or 1): the number of its
tree in the low bits, its index inside the tree in the dT bits above. nZ: keyBits; dT: the lesser
of the line lidb and nZ. Call 0 has the first 2 ^ (nZ - dT) trees, call 1 the next as many, so a
tree's number has nZ - dT + 1 bits and an index nZ + 1 (the page's rK and v_Z).
Place: 11-1-machinery.md, 11.1 ("A key's index has the number of its tree in its low rK bits");
"The lookup on the digits", "Its numbers". -/
def keyIndex (nZ dT call x : Nat) : Nat :=
  call * 2 ^ (nZ - dT) + x / 2 ^ dT + 2 ^ (nZ - dT + 1) * (x % 2 ^ dT)

end Fmt.Places
