-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M3Types.lean: the types and the small functions on which the verifier's decision on an entry
file is written: sizes, the two members of its one group, the layout of a folded row, and the view.

An entry file comes with a further stored copy of a committed table. It holds the messages of a
protocol, the link, whose purpose is to show that the copy holds the same table as the first one
(given that the first one is well formed, which is the key file's matter). This file has the types
and the small functions on which the verifier's decision (Fmt/M3Link.lean, Fmt/M3Dec.lean) is
written. Definitions that compute, and small tests. Core Lean, no Mathlib.

A table has 2^v rows, each a message of l entries with a tail of r entries, encoded under the code T
(`Code`, Fmt/M1Codes.lean). Its stored tree is a hash tree over its columns; a column has one symbol
of each row's codeword. The prover's two folded rows, one for each table, are two oracle messages in
one tree: a group of two members (`Mem`, Fmt/M2Types.lean). Fmt/M3Link.lean says what a folded row
holds.

Sources. Written from the programs' description of the entry file (its part on an entry and the
link); this file's sources include no file made by the programs (the C++ implementation that comes
with this Lean code) for this protocol. It builds on the types of the second toy (a chain of three
links):
Fmt/M2Types.lean has a member of a group, blocks of rows, and rows given member by member.

1. What the file contains.
   `Par`                The sizes, in the record's order:
                        - `fld`: the field.
                        - `T`, `v`, `s`: the one shape of the tables: the code T (its message length
                          l need not be a power of two), 2^v rows, s answers of a record.
                        - `nu0`, `nuj`: how many columns of the first table and of the copy are
                          drawn.
                        - `C`, `Z`: the group's code C and the group's mask code Z.
                        - `R`: the message that holds a folded row has R main rows over E under the
                          group's code C, no mask rows. E is the extension field (`E`,
                          Fmt/M1Types.lean).
                        - `high`: the layout word.
                        - `stages`: all stages of the proximity test, the first among them.
                        - `work`, `salt`: bits of work on each draw of positions; bytes of a leaf's
                          salt (the decision reads neither).
   `aR`, `aP`, `aPhi`, `cut`, `t0`
                        The number of bits of a member's rows and of a row's places; the number of
                        coordinates of the point of comparison; the entry below which the two tables
                        are compared; where the folded tail begins.
   `mem`, `mems`        The group: the first table's member, then the copy's.
   `hiAt`, `loAt`       The layout "rows high": entry e of a folded row's vector lies in row
                        e / 2^aP at place e % 2^aP, which is index e / 2^aP + 2^aR (e % 2^aP) of
                        the member's table; and the way back. Without the layout word, entry e is
                        index e.
   `layHiG`, `layHi`    A vector on entries as a linear form on the member's table. It is made by
                        selection: entry i of the result is an entry of the vector, or 0.
   `View`, `ofView`, `storedAt`
                        The view: the rounds; the opened columns of the chain's own trees; and the
                        opened columns of the two stored trees under (which, position), where which
                        = 0 is the first table and 1 the copy. Both stored tables have one tree
                        number (R7.4 of the format page, docs/format/FORMAT.md, which comes with the
                        programs: the tree of a stored table has the number 0; so in an edition of
                        that page that is not the one that ships), so a tree's number does not name
                        a stored column. In the reader's view they come among the opened columns
                        under the key 2^16 + which (Fmt/Rules8X.lean, `storedKey` and `viewX`).

2. What is checked when the file compiles. Ten small tests (#guard) at made-up sizes, on the numbers
above, on the layout and its way back, and on the split of a reader's view.

3. Theorems. None in this file.

4. What is not claimed.
   It is not claimed that the programs compute in this way. What has been compared with their files
   is said in the head of Fmt/M3Dec.lean.
   Not rendered: a record (s > 0), that is its rows and its seeds.

Terms: lean/GLOSSARY.md.
-/
import Fmt.M2Types
import Fmt.M1PscOps
import Fmt.Rules8X

set_option autoImplicit false

namespace Fmt.M3
open Fmt.M1 Fmt.M2

/-- The sizes; see the head, 1. -/
structure Par where
  fld    : Fld
  T      : Code
  v      : Nat
  s      : Nat := 0
  nu0    : Nat
  nuj    : Nat
  C      : Code
  Z      : Code
  R      : Nat
  high   : Bool := true
  stages : List Stage
  work   : Nat := 8
  salt   : Nat := 40

def Par.aR (P : Par) : Nat := clog P.R
def Par.aP (P : Par) : Nat := Nat.log2 P.C.l
def Par.aPhi (P : Par) : Nat := clog P.T.l
def Par.cut (P : Par) : Nat := P.T.l - 3 * P.s

/-- The least multiple of 2^(clog r) that is at least l. -/
def t0Of (l r : Nat) : Nat := (l + 2 ^ clog r - 1) / 2 ^ clog r * 2 ^ clog r
def Par.t0 (P : Par) : Nat := t0Of P.T.l P.T.r

/-- The number of entries of a member's table. -/
def Par.nTab (P : Par) : Nat := 2 ^ (P.aR + P.aP)

def Par.mem (P : Par) : Mem := { rows := P.R, overE := true }
def Par.mems (P : Par) : List Mem := [P.mem, P.mem]

/-- Sends entry e of a folded row's vector to its index in the member's table. -/
def hiAt (high : Bool) (aR aP e : Nat) : Nat :=
  if high then e / 2 ^ aP + 2 ^ aR * (e % 2 ^ aP) else e
/-- The way back: sends an index of the member's table to an entry of the vector. -/
def loAt (high : Bool) (aR aP i : Nat) : Nat := if high then i % 2 ^ aR * 2 ^ aP + i / 2 ^ aR else i

/-- A vector on entries as a form on the member's table. -/
def layHiG {α : Type} (A : FOps α) (high : Bool) (aR aP : Nat) (w : Array α) : Array α :=
  Array.ofFn (n := 2 ^ (aR + aP)) fun i => w.getD (loAt high aR aP i.val) A.zero
def layHi (P : Par) (w : Array E) : Array E := layHiG (opsOf P.fld) P.high P.aR P.aP w

/-- What the decision sees. -/
structure View where
  rounds : Rs
  opened : List (Nat × Nat × List UInt64)
  stored : List (Nat × Nat × List UInt64)

/-- Made from the first toy's kind of view (`M1.View`). -/
def ofView (V : M1.View) : View :=
  ⟨V.rounds,
    V.opened.filter (fun o => decide (o.1 < 2 ^ 16)),
    (V.opened.filter fun o => decide (2 ^ 16 ≤ o.1)).map fun o => (o.1 - 2 ^ 16, o.2)⟩

/-- The chain's own part, as a view of the first toy's kind. -/
def View.own (V : View) : M1.View := ⟨V.rounds, V.opened⟩

/-- The opened column of a stored tree (`which`) at the position x, if there is one. -/
def storedAt (V : View) (which x : Nat) : Option (List UInt64) :=
  (V.stored.find? fun o => o.1 == which && o.2.1 == x).map (·.2.2)

/-! ## Tests -/

-- where the tail begins
#guard t0Of 5 3 == 8 && t0Of 8 3 == 8 && t0Of 9 4 == 12 && t0Of 803 1001 == 1024 && t0Of 5 1 == 5
-- the layout and its way back, R = 3 rows of 4 places in a table of 4 rows
#guard (List.range 16).all fun e => loAt true 2 2 (hiAt true 2 2 e) == e
#guard (List.range 16).all fun i => hiAt true 2 2 (loAt true 2 2 i) == i
#guard (List.range 12).map (hiAt true 2 2) == [0, 4, 8, 12, 1, 5, 9, 13, 2, 6, 10, 14]
-- the last entry of the last real row is the place of the sample's pad: (R - 1) + 2^aR (l_u - 1)
#guard hiAt true 2 2 (3 * 4 - 1) == (3 - 1) + 2 ^ 2 * (4 - 1)
#guard layHiG OpsT.m101 true 1 1 #[10, 11, 12, 13] == #[10, 12, 11, 13] && layHiG OpsT.m101 false 1 1 #[10, 11, 12] == #[10, 11, 12, 0]
-- two members of three rows: blocks of four rows at 0 and 4; k = 1 + 2, h = 0
#guard (starts [{ rows := 3, overE := true }, { rows := 3, overE := true }]).1 == [some 0, some 4]
#guard kOf [{ rows := 3, overE := true }, { rows := 3, overE := true }] == 3 && hOf [{ rows := 3, overE := true }, { rows := 3, overE := true }] == 0
-- the reader's view is split at 2^16
#guard (ofView ⟨[], [(0, 5, [1]), (storedKey 1, 7, [2, 3]), (storedKey 0, 7, [4, 5]), (1, 7, [6])]⟩).opened == [(0, 5, [1]), (1, 7, [6])]
#guard storedAt (ofView ⟨[], [(0, 5, [1]), (storedKey 1, 7, [2, 3]), (storedKey 0, 7, [4, 5])]⟩) 1 7 == some [2, 3] && storedAt (ofView ⟨[], [(storedKey 1, 7, [2, 3])]⟩) 0 7 == none

end Fmt.M3
