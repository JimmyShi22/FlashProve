-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Means/Says.lean: what a row says of words, and what a group's row says of the group's
tables.

A row of the statement has a coefficient on each entry of each table of each oracle message
(Row.coefficient). Words give each such entry a value in a commutative ring K. The row says of the
words that the sum of coefficient times value, over the entries of the tables that the statement
has, is the row's target (Says). A group puts its members' tables into two tables of its own, a kept
member's main table apart (GroupLayout). A group's row says the like of these tables (GroupSays).

This file has definitions alone, and the laws as definitions of propositions.

Main definitions: Words, tableSize, onTable, value, Says, AllSay, Padded, Tables, KeptAt, tablesOf,
groupValue, GroupSays, InBlock, OffMain, OffMask, Laid, Clean, GroupOk, RowIn. Of
OnBytes/Iop/MaskLaws.lean: MaskReady.
The laws, as propositions: LaysRight and RowMeans (of a function that carries a row to a group's
row), LayoutRight, TablesRight.

The bounds matter. A structured vector does not look at the bits of an index above its variables
(Tensor.entry), so a row's coefficient goes on beyond the end of a table. A sum over more indices
than the table has would count an entry again. So the sums here end where the tables end.

What the tables hold beside the words. An index of a group's table whose row is in no member's block
holds 0, and so does the kept part at an oracle message that is no kept member: no message fills
these places (GroupLayout: the rows after the blocks are zero). So a coefficient there would mean
nothing; Clean says that a group's row has none. The rows of a member's block beyond its real rows
are entries of the words like the others: whoever ties words to messages has to show them 0
(Padded). Whoever reads a group's table off what a prover has sent has to show that it holds the
words on the members' blocks and on the kept members' main tables; elsewhere a clean group's row
does not read it.

Plain records and pure functions of the program are named here, none that takes a context or runs:
Row.coefficient, Statement.has, Statement.tableBits, Statement.rowBits, Statement.layout,
GroupLayout.find, groupIndex, Blk.placeOk, Form.entry, Form.fits.

What is not claimed. Nothing is proved in this file. Nothing on how words are tied to what a prover
has sent, on soundness or on hiding.

-/
import OnBytes.Iop.MaskLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)

/-! ## What a row says of words -/

/-- Words: a value for each oracle message, table and index. -/
abbrev Words (K : Type) : Type := Nat → Part → Nat → K

/-- The number of entries of a table; 0 for a table that is not there. -/
def tableSize (S : Statement) (o : Nat) (part : Part) : Nat :=
  if S.has o part then 2 ^ S.tableBits o part else 0

/-- A row applied to one table of the words. -/
def onTable (S : Statement) (r : Row) (m : Words K) (o : Nat) (part : Part) : K :=
  ∑ i ∈ Finset.range (tableSize S o part), ρ.val (r.coefficient o part i) * m o part i

/-- A row applied to the words: the sum over both tables of all oracle messages. -/
def value (S : Statement) (r : Row) (m : Words K) : K :=
  ∑ o ∈ Finset.range S.oracles.size, (onTable ρ S r m o .main + onTable ρ S r m o .mask)

/-- What a row says of words. The sums end where the statement's tables end, so this is the claim
that is meant only for a row that meets RowIn: a summand on a table that the statement does not
have, or beyond a table's end, counts for nothing, and a structured vector with fewer variables than
its table has index bits is counted again and again. Whoever states a law over Says shows RowIn of
the row, at the statement in force. -/
def Says (S : Statement) (r : Row) (m : Words K) : Prop := value ρ S r m = ρ.val r.target

/-- Every row of a list says its claim of the words. -/
def AllSay (S : Statement) (l : List Row) (m : Words K) : Prop := ∀ r ∈ l, Says ρ S r m

/-- The real rows of a table. -/
def realRows (S : Statement) (o : Nat) (part : Part) : Nat :=
  match S.oracles[o]? with
  | some x => x.shape.rows part
  | none => 0

/-- The words are 0 on the rows beyond the real ones. No law of this file asks it. -/
def Padded (S : Statement) (m : Words K) : Prop :=
  ∀ o part i, realRows S o part ≤ i % 2 ^ S.rowBits o part → m o part i = 0

/-! ## The tables of a group -/

/-- The tables that a group's row is on: the group's main table, its mask table, and the main table
of each kept member. -/
structure Tables (K : Type) where
  main : Nat → K
  mask : Nat → K
  kept : Nat → Nat → K

/-- The oracle message o is a member whose main rows are kept. -/
def KeptAt (L : GroupLayout) (o : Nat) : Prop :=
  ∃ i, L.find o = some i ∧ L.kept.getD i false = true

/-- The group's tables as the words fill them. At an index whose row is in the block of a member
stands that member's entry; at the other indices 0. The kept part has a kept member's main table,
and 0 at every other oracle message. -/
def tablesOf (S : Statement) (L : GroupLayout) (m : Words K) : Tables K where
  main := fun J => ∑ o ∈ Finset.range S.oracles.size,
    mainWeight (K := K) S L o J * m o .main (mainBack S L o J)
  mask := fun J => ∑ o ∈ Finset.range S.oracles.size,
    maskWeight (K := K) S L o J * m o .mask (maskBack S L o J)
  kept := fun o i => keptWeight (K := K) L o * m o .main i

/-- A group's row applied to tables. -/
def groupValue (S : Statement) (L : GroupLayout) (R : GroupRow) (T : Tables K) : K :=
  (∑ J ∈ Finset.range (2 ^ (L.k + L.logEll)), ρ.val (R.c.entry J) * T.main J) +
  (∑ J ∈ Finset.range (2 ^ (L.h + L.logEllZk)), ρ.val (R.d.getD J zeroE) * T.mask J) +
  ∑ o ∈ Finset.range S.oracles.size, ∑ i ∈ Finset.range (tableSize S o .main),
    keptSum ρ o i R.kept.toList * T.kept o i

/-- What a group's row says of tables. -/
def GroupSays (S : Statement) (L : GroupLayout) (R : GroupRow) (T : Tables K) : Prop :=
  groupValue ρ S L R T = ρ.val R.target

/-- The row of the index J of a table with 2^k rows is in the block of 2^a rows from first on. -/
def InBlock (J a first k : Nat) : Prop := first ≤ J % 2 ^ k ∧ J % 2 ^ k < first + 2 ^ a

/-- The row of the index J of the group's main table is in no member's block. -/
def OffMain (S : Statement) (L : GroupLayout) (J : Nat) : Prop :=
  ∀ o i first, L.find o = some i → L.kept.getD i false = false →
    L.mainFirst.getD i none = some first → ¬ InBlock J (S.rowBits o .main) first L.k

/-- The row of the index J of the group's mask table is in no member's block. -/
def OffMask (S : Statement) (L : GroupLayout) (J : Nat) : Prop :=
  ∀ o i first, L.find o = some i → L.maskFirst.getD i none = some first →
    ¬ InBlock J (S.rowBits o .mask) first L.h

/-- The tables hold the words as the layout lays them, said with the function that the program
carries an index with (groupIndex): each entry of a member stands where that function puts it, and
an index whose row is in no member's block holds 0. A kept member's main table is its own; the kept
part is 0 at what is no kept member. -/
structure Laid (S : Statement) (L : GroupLayout) (m : Words K) (T : Tables K) : Prop where
  main_at : ∀ o i first, L.find o = some i → L.kept.getD i false = false →
    L.mainFirst.getD i none = some first → ∀ idx < tableSize S o .main,
      T.main (groupIndex idx (S.rowBits o .main) first L.k) = m o .main idx
  main_else : ∀ J < 2 ^ (L.k + L.logEll), OffMain S L J → T.main J = 0
  mask_at : ∀ o i first, L.find o = some i → L.maskFirst.getD i none = some first →
    ∀ idx < tableSize S o .mask,
      T.mask (groupIndex idx (S.rowBits o .mask) first L.h) = m o .mask idx
  mask_else : ∀ J < 2 ^ (L.h + L.logEllZk), OffMask S L J → T.mask J = 0
  kept_at : ∀ o i, L.find o = some i → L.kept.getD i false = true →
    ∀ idx < tableSize S o .main, T.kept o idx = m o .main idx
  kept_else : ∀ o, ¬ KeptAt L o → ∀ idx, T.kept o idx = 0

/-- A group's row has no coefficient where the tables hold no word: it reads 0 at an index whose row
is in no member's block, and on what is no kept member. -/
structure Clean (S : Statement) (L : GroupLayout) (R : GroupRow) : Prop where
  main : ∀ J, OffMain S L J → ρ.val (R.c.entry J) = 0
  mask : ∀ J < 2 ^ (L.h + L.logEllZk), OffMask S L J → ρ.val (R.d.getD J zeroE) = 0
  kept : ∀ o, ¬ KeptAt L o → ∀ i, keptSum ρ o i R.kept.toList = 0

/-! ## What the calls have tested -/

/-- What the calls that make a group and let a message join it have tested: no member twice, every
member is there, a mark for each member, and each member's rows are under the group's codes. -/
structure GroupOk (S : Statement) (G : Group) : Prop where
  nodup : G.members.toList.Nodup
  there : ∀ o ∈ G.members.toList, o < S.oracles.size
  marks : G.kept.size = G.members.size
  mainCode : ∀ o ∈ G.members.toList, ∀ x, S.oracles[o]? = some x →
    x.shape.mainRows = 0 ∨ x.shape.code = G.code
  maskCode : ∀ o ∈ G.members.toList, ∀ x, S.oracles[o]? = some x →
    x.shape.maskRows = 0 ∨ x.shape.maskCode = G.maskCode

/-- What the call that adds an open row has tested of the row's summands: each is on a table that a
member of the group has, and within it. -/
structure RowIn (S : Statement) (G : Group) (row : Row) : Prop where
  terms : ∀ t ∈ row.terms.toList, Blk.placeOk S G t.oracle t.part t.v.vars 0 = true
  units : ∀ u ∈ row.units.toList,
    Blk.placeOk S G u.oracle u.part (S.tableBits u.oracle u.part) u.index = true
  runs : ∀ w ∈ row.runs.toList, 0 < w.coeffs.size ∧ 1 ≤ w.step ∧
    Blk.placeOk S G w.oracle w.part (S.tableBits w.oracle w.part)
      (w.first + w.step * (w.coeffs.size - 1)) = true
  forms : ∀ f ∈ row.forms.toList,
    Blk.placeOk S G f.oracle .main (S.tableBits f.oracle .main) 0 = true ∧
      f.c.fits (S.tableBits f.oracle .main) = true

/-! ## The laws, as propositions -/

/-- The type of the function that adds x times a row to a group's row (addToGroupRow). -/
abbrev Lay : Type := Statement → GroupLayout → Row → E → GroupRow → Option GroupRow

/-- **The law of the laying.** At the layout that the statement gives a group, for a row that has
passed the tests of the adding, and a group's row before whose mask table is not yet written out or
has its full length (MaskReady): the function returns a group's row; the same holds of its mask
table; it has no coefficient where the tables hold no word, if the group's row before had none; and
for all words what it is short of its target, on the group's tables as the words fill them, is what
the group's row before was short of plus x times what the row is short of on the words. -/
def LaysRight (lay : Lay) : Prop :=
  ∀ (S : Statement) (g : Nat) (G : Group) (L : GroupLayout) (row : Row) (x : E) (acc : GroupRow),
    S.groups[g]? = some G → S.layout g = some L → GroupOk S G → RowIn S G row → MaskReady L acc →
    ∃ acc', lay S L row x acc = some acc' ∧ MaskReady L acc' ∧
      (Clean ρ S L acc → Clean ρ S L acc') ∧ ∀ m : Words K,
      groupValue ρ S L acc' (tablesOf S L m) - ρ.val acc'.target =
        groupValue ρ S L acc (tablesOf S L m) - ρ.val acc.target +
          ρ.val x * (value ρ S row m - ρ.val row.target)

/-- **A row laid on a group's tables holds of them just if it holds of the words.** The tables are
those that the words fill (tablesOf). For tables that are read off something else, such as what a
proximity test has decoded, Laid is to be shown of them: see TablesRight. -/
def RowMeans (lay : Lay) : Prop :=
  ∀ (S : Statement) (g : Nat) (G : Group) (L : GroupLayout) (row : Row),
    S.groups[g]? = some G → S.layout g = some L → GroupOk S G → RowIn S G row →
    ∃ R, lay S L row oneE { group := g } = some R ∧ Clean ρ S L R ∧ ∀ m : Words K,
      (GroupSays ρ S L R (tablesOf S L m) ↔ Says ρ S row m)

/-- **The layout is in order**: the members' blocks are aligned and inside the tables, and no two
members' blocks have a row in common. -/
def LayoutRight : Prop :=
  ∀ (S : Statement) (g : Nat) (G : Group) (L : GroupLayout),
    S.groups[g]? = some G → S.layout g = some L →
    MainBlocksOk S L ∧ MaskBlocksOk S L ∧
    (∀ o o' i i' a a', o ≠ o' → L.find o = some i → L.find o' = some i' →
      L.mainFirst.getD i none = some a → L.mainFirst.getD i' none = some a' →
      a + 2 ^ S.rowBits o .main ≤ a' ∨ a' + 2 ^ S.rowBits o' .main ≤ a) ∧
    (∀ o o' i i' a a', o ≠ o' → L.find o = some i → L.find o' = some i' →
      L.maskFirst.getD i none = some a → L.maskFirst.getD i' none = some a' →
      a + 2 ^ S.rowBits o .mask ≤ a' ∨ a' + 2 ^ S.rowBits o' .mask ≤ a)

/-- **The tables are the laid words, and nothing else is**: tablesOf meets Laid, and tables that
meet Laid agree with it wherever a group's row reads them. -/
def TablesRight (K : Type) [CommRing K] : Prop :=
  ∀ (S : Statement) (g : Nat) (G : Group) (L : GroupLayout) (m : Words K),
    S.groups[g]? = some G → S.layout g = some L → GroupOk S G →
    Laid S L m (tablesOf S L m) ∧ ∀ T : Tables K, Laid S L m T →
      (∀ J < 2 ^ (L.k + L.logEll), T.main J = (tablesOf S L m).main J) ∧
      (∀ J < 2 ^ (L.h + L.logEllZk), T.mask J = (tablesOf S L m).mask J) ∧
      (∀ o, ∀ i < tableSize S o .main, T.kept o i = (tablesOf S L m).kept o i)

end OnBytes.Means
