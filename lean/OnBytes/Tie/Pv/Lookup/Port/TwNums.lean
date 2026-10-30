-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Port/TwNums.lean.
The public numbers of a lookup with one part, no shift, no dead plane and the range table, read off
a value of `OnBytes.Lkp.Public` (OnBytes/Iop/Lkp.lean), and the numbering of its mask entries.

Definitions alone: numbers, lists and Bool tests; no proof; no Mathlib; all computable.
OnBytes/Tie/Pv/Lookup/Port/FoNums.lean takes the numbering of the mask entries from this file.
Main names:
  `Sizes`: the public numbers. `Sizes.ofPublic`: read off a value of `Lkp.Public`, field by field.
  `Sizes.served`, `Sizes.ofPublic?`, `Sizes.ok`: at which values of `Lkp.Public` the numbers are
    meant to be read; which numbers are lawful. Bool tests on public numbers.
  `ordK l`, `ordT l`, `ordE`, `ordB`: the orders as lists: round j binds variable (list)[j]:
    `Lkp.defaultOrder`, `Lkp.orderBeginning`.
  `Sc`: a sumcheck's public shape: the degrees by round (the round Y's last, where there is one),
    and how many values are shown. `scs`: the sumchecks in run order: tie, keys, table, leaves,
    bits. `firstOf`: the number of a sumcheck's first mask entry, by summing; no numeral.
  `slotCoef`, `slotConst`, `slotShown`: the place of a mask entry inside a sumcheck: by round,
    degrees upward from 1, the last round's constant first among its own; then one entry a shown
    value.
  `reIdx`: for each end claim of the typed lookup, its place in `Lkp.verify`: one list for all
    transcripts.
Limits: the file states nothing: that a number, an order or a place here is the one that
`Lkp.verify` or the typed lookup uses is said by no declaration of it. The functions are total in
S. The numbers are meant as those of a lookup of OnBytes/Iop/Lkp.lean only at a value with
`served`, and they are lawful only where `ok` holds.

-/
import OnBytes.Iop.Lkp

set_option autoImplicit false

namespace TwNums

/-- The public numbers. v: a key's number has v bits; d: a row's; w: a plane's (`Lkp.Public.mu`);
planes: how many planes count; first: the variables that the last key level binds first; pads: the
padding as (row, how many places) (`Lkp.paddingList` has (how many, row)); padAt: each padded place
with its row. -/
structure Sizes where
  v : Nat
  d : Nat
  w : Nat
  planes : Nat
  first : List Nat
  pads : List (Nat × Nat)
  padAt : List (Nat × Nat)
  deriving Repr, DecidableEq

namespace Sizes

/-- every padded place of the runs of padding, with its row -/
def padAtOf (S : OnBytes.Lkp.Public) : List (Nat × Nat) :=
  S.padding.flatMap fun p => (List.range p.length).map fun i => (p.first + i * 2 ^ p.logStep, p.row)

/-- Read off the public inputs, field by field. It reads: the head of parts, d, mu, live (through
planes), the runs' row, length, first, logStep, and lastKeyLevelOrder. It does not read h, g,
shifted, readFrom, keys, tables, the tail of parts, a run's part: what these must be is the Bool
`served` below: the numbers are meant as those of a lookup of OnBytes/Iop/Lkp.lean only where it
holds.
pads is derived from padAt (one place, one pair): one source. -/
def ofPublic (S : OnBytes.Lkp.Public) : Sizes where
  v := S.parts.headD 0
  d := S.d
  w := S.mu
  planes := S.planes
  first := S.lastKeyLevelOrder
  pads := (padAtOf S).map fun p => (p.2, 1)
  padAt := padAtOf S

/-- The lookups at which these numbers are meant to be read: `Lkp.Public.ok`; one part; no tree
numbers (g = 0); the table's pieces are blocks of rows (h = 0); no shift; all planes count; the
caller's first two messages are read; every block of trees
has function 0; one table, the range table (no row written), of function 0; every run lies in
part 0. -/
def served (S : OnBytes.Lkp.Public) : Bool :=
  S.ok && S.parts.length == 1 && S.g == 0 && S.h == 0 && !S.shifted && S.live == 0 && S.readFrom ==
      [0, 1] &&
  (S.keys.all fun b => b.function == some 0) &&
  S.tables.length == 1 && (S.tables.all fun t => t.rows.isEmpty && t.function == 0) &&
  S.padding.all fun p => p.part == 0

/-- none where `served` is false -/
def ofPublic? (S : OnBytes.Lkp.Public) : Option Sizes := if served S then some (ofPublic S) else
    none

variable (S : Sizes)

/-- The numbers are lawful: a key's number has a bit; at least two planes, and all 2^w count; the
padded places differ, lie among the keys and hold rows of the table; pads is padAt, one pair a
place; the last key level's own order names variables of that level, each once
(`Lkp.Public.orderOK`). -/
def ok : Bool :=
  decide (1 ≤ S.v) && decide (2 ≤ S.planes) && S.planes == 2 ^ S.w &&
  decide (S.padAt.map (·.1)).Nodup && (S.padAt.all fun p => decide (p.1 < 2 ^ S.v) && decide (p.2 <
      2 ^ S.d)) &&
  S.pads == S.padAt.map (fun p => (p.2, 1)) &&
  (S.first.all fun j => decide (j + 1 < S.v)) && decide S.first.Nodup

/-- the numbers of `LkAsmH`: v' + 1 = v; the tie has n + 1 steps, and n + 2 planes count -/
def v' : Nat := S.v - 1
def n : Nat := S.planes - 2

/-- how many entries the caller's three messages have: keys (the padded places are no entries),
planes, masks (below: nMasks) -/
def nPad : Nat := (S.pads.map (·.2)).sum
def nKeys : Nat := 2 ^ S.v - S.nPad
def nPlanes : Nat := 2 ^ (S.w + S.d)

/-- is key number b padded, and with which row -/
def padRow (b : Nat) : Option Nat := S.padAt.lookup b
/-- the entry of the keys' message that holds key number b: b less the padded places below it; none
at a padded place -/
def keyEntry (b : Nat) : Option Nat :=
  if (S.padRow b).isSome then none else some (b - (S.padAt.filter fun p => p.1 < b).length)
/-- the entry of the planes' message that holds bit j of row u's count -/
def planeEntry (u j : Nat) : Nat := j + 2 ^ S.w * u

/-! ### The orders, as lists: round j binds variable (list)[j] -/
def ordK (l : Nat) : List Nat :=
  if l + 1 = S.v then OnBytes.Lkp.orderBeginning S.first l else OnBytes.Lkp.defaultOrder l
def ordT (l : Nat) : List Nat := OnBytes.Lkp.defaultOrder (S.w + l)
def ordE : List Nat := OnBytes.Lkp.defaultOrder (S.w + S.d)
def ordB : List Nat := OnBytes.Lkp.defaultOrder (S.w + S.d)

end Sizes

/-! ### A sumcheck's public shape, and the places of its mask entries -/

/-- degs: by round, the largest degree of the round's polynomial, the equality factor not counted
(`PFmt.n`, Cb/Ld/LdPsc.lean); the round sends as many scalars. The round Y is the round of the dummy
last variable (`pDummy`, the same file); its degree stands last where there is one. withY: is the
last round the round Y; shown: how many values are shown at the end -/
structure Sc where
  degs : List Nat
  withY : Bool
  shown : Nat
  deriving Repr, DecidableEq

/-- the number of mask entries of a sumcheck: the hiding polynomial's (one a degree from 1 up in
each round, one constant), then one a shown value -/
def Sc.masks (c : Sc) : Nat := 1 + c.degs.sum + c.shown

/-- the place of the hiding polynomial's coefficient of degree t + 1 in round j; f: the sumcheck's
first entry -/
def slotCoef (degs : List Nat) (f j t : Nat) : Nat :=
  f + (degs.take j).sum + (if j + 1 = degs.length then 1 else 0) + t
/-- the place of its constant: first among the last round's own -/
def slotConst (degs : List Nat) (f : Nat) : Nat := f + degs.dropLast.sum
/-- the place of the mask of shown value number a -/
def slotShown (degs : List Nat) (f a : Nat) : Nat := f + 1 + degs.sum + a

/-- the number of a shown value, in the order of ends of OnBytes/Iop/Lkp.lean. Tie, step 0: root,
power, plane 0 (in the typed record: none, some false, some true); a later step: power, plane
(false, true); a level: the two halves (false, true); the bits: one. -/
def shownTie0 : Option Bool → Nat
  | none => 0
  | some false => 1
  | some true => 2
def shownBool : Bool → Nat
  | false => 0
  | true => 1

namespace Sizes
variable (S : Sizes)

def scTie (_ : Sizes) (j : Nat) : Sc := ⟨[3], true, if j = 0 then 3 else 2⟩
def scKey (_ : Sizes) (l : Nat) : Sc := ⟨List.replicate l 2 ++ [2], true, 2⟩
def scTab (l : Nat) : Sc := ⟨List.replicate (S.w + l) 2 ++ [2], true, 2⟩
/-- the leaves: degree 1 in a plane's variable, 2 in a row's, by round; no round Y; nothing shown -/
def scEnd : Sc := ⟨S.ordE.map fun t => if t < S.w then 1 else 2, false, 0⟩
def scBit : Sc := ⟨List.replicate (S.w + S.d) 2 ++ [2], true, 1⟩

/-- the sumchecks in run order -/
def scs : List Sc :=
  (List.range (S.n + 1)).map S.scTie ++ (List.range S.v).map S.scKey ++ (List.range S.d).map S.scTab
      ++ [S.scEnd, S.scBit]

/-- the number of sumcheck number i's first mask entry: the sum of all before it -/
def firstOf (i : Nat) : Nat := ((S.scs.take i).map Sc.masks).sum
def nMasks : Nat := (S.scs.map Sc.masks).sum

/-- the sumchecks' numbers in run order -/
def iTie (_ : Sizes) (j : Nat) : Nat := j
def iKey (l : Nat) : Nat := S.n + 1 + l
def iTab (l : Nat) : Nat := S.n + 1 + S.v + l
def iEnd : Nat := S.n + 1 + S.v + S.d
def iBit : Nat := S.n + 1 + S.v + S.d + 1

def fTie (j : Nat) : Nat := S.firstOf (S.iTie j)
def fKey (l : Nat) : Nat := S.firstOf (S.iKey l)
def fTab (l : Nat) : Nat := S.firstOf (S.iTab l)
def fEnd : Nat := S.firstOf S.iEnd
def fBit : Nat := S.firstOf S.iBit

/-- The places of the mask entries as one function: sumcheck number i; which entry of it. -/
inductive Ent where
  | coef (round power : Nat)   -- the hiding polynomial's coefficient of degree power + 1 there
  | const                      -- its constant
  | shown (a : Nat)            -- the mask of shown value number a
  deriving Repr, DecidableEq
def place (i : Nat) (e : Ent) : Nat :=
  let c := S.scs.getD i ⟨[], false, 0⟩
  match e with
  | .coef j t => slotCoef c.degs (S.firstOf i) j t
  | .const => slotConst c.degs (S.firstOf i)
  | .shown a => slotShown c.degs (S.firstOf i) a

/-- the same by block; a step or level that is not played goes to entry 0 (the typed record asks its
places at every number) -/
def pTie (j : Nat) (e : Ent) : Nat := if j < S.n + 1 then S.place (S.iTie j) e else 0
def pKey (l : Nat) (e : Ent) : Nat := if l < S.v then S.place (S.iKey l) e else 0
def pTab (l : Nat) (e : Ent) : Nat := if l < S.d then S.place (S.iTab l) e else 0
def pEnd (e : Ent) : Nat := S.place S.iEnd e
def pBit (e : Ent) : Nat := S.place S.iBit e

/-- The places made total: a (round, power) that the sumcheck has not goes to the constant; a shown
value's number beyond the last goes to the last (where nothing is shown: to the constant). An entry
that the sumcheck has stays as it is. -/
def Ent.clamp (c : Sc) : Ent → Ent
  | .coef j t => if t < c.degs.getD j 0 then .coef j t else .const
  | .const => .const
  | .shown a => if c.shown = 0 then .const else .shown (min a (c.shown - 1))
def pTieC (j : Nat) (e : Ent) : Nat := S.pTie j (Ent.clamp (S.scTie j) e)
def pKeyC (l : Nat) (e : Ent) : Nat := S.pKey l (Ent.clamp (S.scKey l) e)
def pTabC (l : Nat) (e : Ent) : Nat := S.pTab l (Ent.clamp (S.scTab l) e)
def pEndC (e : Ent) : Nat := S.pEnd (Ent.clamp S.scEnd e)
def pBitC (e : Ent) : Nat := S.pBit (Ent.clamp S.scBit e)

/-- all entries of sumcheck i, in the order of `PIdx` (by round, degrees upward, the constant last),
then the shown -/
def entsOf (c : Sc) : List Ent :=
  ((List.range c.degs.length).flatMap fun j => (List.range (c.degs.getD j 0)).map fun t => Ent.coef
      j t) ++ [Ent.const] ++
    (List.range c.shown).map Ent.shown

/-! ### The end claims -/

/-- how many end claims: a row a sumcheck, the bits' end row, the pin, the keys' claim -/
def nClaims : Nat := S.scs.length + 3

/-- Entry i: the place in `Lkp.verify` of the end claim in place i of the typed lookup's list.
Typed: within the tie and within a tree the row of a later step comes first; then closing, bits'
sumcheck, bits' end, pin, keys. `Lkp.verify`: every sumcheck's row in run order, the bits' end row,
the pin; the keys' claim beside them, here numbered last. -/
def reIdx : List Nat :=
  (List.range (S.n + 1)).reverse ++ (List.range S.v).reverse.map (· + (S.n + 1)) ++ (List.range
      S.d).reverse.map (· + (S.n + 1 + S.v)) ++
    (List.range 5).map (· + S.iEnd)

end Sizes

end TwNums
