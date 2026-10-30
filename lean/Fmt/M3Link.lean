-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M3Link.lean: the entry file's link: the linear claims ("rows") that its verifier forms on the
prover's two oracle messages, in the order in which they are combined.

An entry file holds the messages of a protocol, the link, whose purpose is to show that a further
stored copy of a committed table holds the same table as the first one (given that the first one is
well formed, which is the key file's matter). A table has 2^v rows, each a message of l entries with
a tail of r entries. The head of Fmt/M3Types.lean says more on both.
The link's prover sends two folded rows, one of the first table and one of the copy. The two are
oracle messages in one tree: a group of two members (`Mem`, Fmt/M2Types.lean). The honest prover of
the tests (`LinkT.vec`) writes two things into a folded row. One is the sum of its table's rows,
messages and tails, under the weights eq(gamma, b) of the link's point gamma. The other is the
sample's pad, at the last entry in use. The verifier forms linear claims ("rows") on the group:
   - one row for each drawn column of a stored table;
   - the equality row;
   - the two sample rows.
This file has these rows and their combination into one (`batchLit`). Definitions that compute, and
tests with an honest prover that is defined here. Core Lean, no Mathlib.

Sources. Written from the programs' description of the entry file; this file's sources include no
file made by the programs (the C++ implementation that comes with this Lean code) for this protocol.
What has been compared, and with what, is said in the head of Fmt/M3Dec.lean.

The G-functions. The arithmetic that this file adds (`foldColG`, `colVecG`, `eqVecG`, `negVG`) is
written over any operations (Fmt/M1PscOps.lean, `FOps`; the head of that file says for what); the
format's functions are its values at the format's field operations (`opsOf f`).

1. What the file contains.
   `foldColG`           The fold of an opened column at the link's point gamma: the sum over the
                        table's rows b of eq(gamma, b) c_b.
   `colVecG`            A draw's row as a vector on the entries of a folded row. It is the row of
                        the generator matrix of the tables' code. The part of that row on the
                        message is at the entries 0 .. l - 1. The part on the tail is at the entries
                        t0 .. t0 + r - 1, where t0 (`Par.t0`) is where the folded tail begins.
   `eqVecG`             The equality row's vector: eq(phi, e) at the entries e below the cut, 0 from
                        the cut on. The cut (`Par.cut`) is the entry below which the two tables are
                        compared.
   `foldCol`, `colRow`, `eqRow`, `smpRow`
                        The format's versions. The last three are rows given member by member
                        (Fmt/M2Types.lean, `MRow`): for each member a form on that member's own
                        table, and the target.
                        - A draw's row stands on its own table's member alone.
                        - The equality row stands on both, with opposite signs, and has the
                          target 0.
                        - A sample row stands on its member. It is the linear equation that the
                          prover's answer to a sample claims (Fmt/M2Send.lean, `sampleOf`, at a
                          member with no mask rows and R rows over E; the head of that file says
                          what z, beta and the pad are).
   `rowsLit`            All rows, in the order in which they are combined: the equality row; the
                        sample rows of the first table's member and of the copy's; the draws' rows
                        as drawn, repeats counted, the first table's first. The result is none if a
                        drawn column was not opened or does not have 2^v words.

2. What is checked when the file compiles. Fifteen tests (#guard). Twelve use made-up data
(namespace `LinkT`): tables of two rows, l = 5 (not a power of two), r = 3, R = 3 rows of 4 places,
two draws of the first table and three of the copy, so eight rows in all.
   One: an honest committer and prover, made by the definitions: all eight rows hold of the two
   members' tables.
   Three with altered data.
   - One cell of the copy below the cut is altered: the equality row alone fails.
   - The copy's folded row has another tail than the copy's: the rows of the copy's three draws
     fail.
   - A column of the first table is shown for the copy: that draw's row fails.
   Five with one entry of a folded row raised by 1. In these the answers to the samples are the true
   ones of the altered tables, so the two sample rows hold throughout.
   - Entry 0 of the copy's folded row: the equality row and the copy's draws' rows fail.
   - The first entry of the copy's tail: the copy's draws' rows fail and nothing else.
   - Entry 0 of both folded rows: the equality row holds, all draws' rows fail.
   - The last entry before the cut: it is compared, as entry 0 is.
   - The entry at the cut: all eight rows hold, since the equality row stops before it and no
     draw's row reads it.
   Two: a drawn column that was not opened, and a column of another width, give none.
   One: the sizes of the combined row.
   Three: `foldColG`, `colVecG` and `eqVecG` at another carrier (the integers modulo 101).

3. Theorems. None in this file.

4. What is not claimed.
   It is not claimed that the programs compute in this way; see the head of Fmt/M3Dec.lean.
   The rows of a record (s > 0) are not rendered.
-/
import Fmt.M3Types
import Fmt.M2Send
import Fmt.M1BaseOps

set_option autoImplicit false

namespace Fmt.M3
open Fmt.M1 Fmt.M2

section
variable {α : Type} (A : FOps α)

/-- The fold of an opened column `col` at the point `gamma`. -/
def foldColG (gamma col : List α) : α := dotG A (pvG A A.one gamma) col.toArray

/-- A draw's row as a vector on entries; `n` is the number of entries. It is made by selection:
nothing is added. Below the length of `gm`, entry e is entry e of `gm`; from t0 on, as far as `gt`
reaches, it is entry e - t0 of `gt`; everywhere else it is 0. -/
def colVecG (t0 n : Nat) (gm gt : List α) : Array α :=
  let a := gm.toArray
  let b := gt.toArray
  Array.ofFn (n := n) fun e =>
    if e.val < a.size then a.getD e.val A.zero
    else if t0 ≤ e.val then b.getD (e.val - t0) A.zero
    else A.zero

/-- The equality row's vector, on entries; n: the number of entries. -/
def eqVecG (cut n : Nat) (phi : List α) : Array α :=
  let w := pvG A A.one phi
  Array.ofFn (n := n) fun e => if e.val < cut then w.getD e.val A.zero else A.zero

def negVG (v : Array α) : Array α := v.map A.neg

end

def foldCol (f : Fld) (gamma : List E) (col : List UInt64) : E :=
  foldColG (opsOf f) gamma (col.map Fld.ofF)

/-- The row of a draw x of the table `which`; col: the opened column. -/
def colRow (P : Par) (gamma : List E) (which x : Nat) (col : List UInt64) : MRow :=
  ⟨oneAt 2 which
      (layHi P
        (colVecG (opsOf P.fld) P.t0 P.nTab ((genM P.T x).map Fld.ofF) ((genT P.T x).map Fld.ofF))),
    [],
    foldCol P.fld gamma col⟩

/-- The equality row. -/
def eqRow (P : Par) (phi : List E) : MRow :=
  let w := eqVecG (opsOf P.fld) P.cut P.nTab phi
  ⟨[layHi P w, layHi P (negVG (opsOf P.fld) w)], [], Fld.zeroE⟩

/-- The sample row of member i; y: the answer, which is the row's target. -/
def smpRow (P : Par) (z : List E) (beta : E) (i : Nat) (y : E) : MRow :=
  ⟨oneAt 2 i (sampleOf P.fld P.C.l P.Z.l P.mem z beta y).1, [], y⟩

/-- The draws with their tables (0: the first table, 1: the copy). -/
def drawsOf (P : Par) (xs : List Nat) : List (Nat × Nat) :=
  (xs.take P.nu0).map (fun x => (0, x)) ++ (xs.drop P.nu0).map fun x => (1, x)

/-- The draws' rows; none if a drawn column was not opened or does not have 2^v words. -/
def colRows (P : Par) (V : View) (gamma : List E) : List (Nat × Nat) → Option (List MRow)
  | [] => some []
  | (w, x) :: ds =>
    match storedAt V w x, colRows P V gamma ds with
    | some col, some rs =>
      if col.length == 2 ^ P.v then some (colRow P gamma w x col :: rs) else none
    | _, _ => none

/-- All rows, in the order in which they are combined. -/
def rowsLit (P : Par) (V : View) (gamma z : List E) (beta y0 yj : E)
    (xs : List Nat) (phi : List E) : Option (List MRow) :=
  (colRows P V gamma (drawsOf P xs)).map fun rs =>
    eqRow P phi :: smpRow P z beta 0 y0 :: smpRow P z beta 1 yj :: rs

/-- The sum of all rows (`rowsLit`) under the powers of theta, on the group's table. -/
def batchLit (P : Par) (V : View) (gamma z : List E) (beta y0 yj : E) (xs : List Nat)
    (phi : List E) (theta : E) : Option KRow :=
  (rowsLit P V gamma z beta y0 yj xs phi).map fun rows =>
    toK P.mems P.C.l P.Z.l (sumM P.fld theta rows)

/-! ## Tests: an honest committer and prover, defined here -/

namespace LinkT

def f : Fld := .two
def wd (n : Nat) : UInt64 := Fld.two.red (1000003 * n + 17)
def el (n : Nat) : E := (wd n, wd (n * n + 3), wd (7 * n + 1))

/-- The rows' messages; below, `tail`: the tails of the first table (i = 0), the copy (i = 1). -/
def msg (b : Nat) : List UInt64 := (List.range 5).map fun e => wd (10 * b + e + 1)
def tail (i b : Nat) : List UInt64 := (List.range 3).map fun e => wd (100 * (i + 1) + 10 * b + e)
/-- The message of row b of table i; spoil: cell 0 of row 1 of the copy's message is `wd 999`.
-/
def msgOf (spoil : Bool) (i b : Nat) : List UInt64 :=
  if spoil && i == 1 && b == 1 then (msg b).set 0 (wd 999) else msg b
def gamma : List E := [el 1]
def phi : List E := [el 2, el 3, el 4]
def z : List E := (List.range 4).map fun t => el (20 + t)
def beta : E := el 30

/-- The folded row's vector: 12 entries in use, the last the sample's pad. -/
def vec (spoil otherTail : Bool) (i : Nat) : Array E :=
  let w := pv f Fld.oneE gamma
  let fold (rows : List (List UInt64)) (e : Nat) : E :=
    (List.range 2).foldl
      (fun s b => f.addE s (f.mulE (ent w b) (Fld.ofF ((rows.getD b []).getD e 0)))) Fld.zeroE
  Array.ofFn (n := 16) fun e =>
    if e.val < 5 then fold ((List.range 2).map (msgOf spoil i)) e.val
    else if 8 ≤ e.val && e.val < 11 then
      fold ((List.range 2).map (tail (if otherTail && i == 1 then 7 else i))) (e.val - 8)
    else if e.val == 11 then el (40 + i) else Fld.zeroE
/-- The member's table. -/
def tab (spoil otherTail : Bool) (i : Nat) : Array E :=
  Array.ofFn (n := 16) fun j => ent (vec spoil otherTail i) (loAt true 2 2 j.val)

def holds (spoil otherTail : Bool) (R : MRow) : Bool :=
  f.addE (dot f (R.main.getD 0 #[]) (tab spoil otherTail 0))
      (dot f (R.main.getD 1 #[]) (tab spoil otherTail 1)) == R.t

def xs : List Nat := [3, 9, 9, 0, 14]
/-- A member's table with 1 added at an entry of its vector. -/
def bump (t : Array E) (e : Nat) : Array E :=
  t.setIfInBounds (hiAt true 2 2 e) (f.addE (ent t (hiAt true 2 2 e)) Fld.oneE)
end LinkT

-- 1 + 2 + nu0 + nuj rows; the honest ones all hold
-- one cell of the copy below the cut: the equality row alone fails
-- the copy's folded row with another tail: the copy's three draws' rows fail
-- a column of the first table shown for the copy: that draw's row fails
-- entry 0 of the copy's folded row raised: the equality row and all the copy's draws' rows fail
-- the first entry of the copy's folded tail raised: all the copy's draws' rows fail and nothing
-- else
-- the same change in both folded rows: the equality row stays true, all draws' rows fail
-- the last entry before the cut is compared, the entry at the cut is not
-- a drawn column that was not opened; a column of another width
-- the combined row is a form on the group's table, which has 2^3 rows of 4 places; it has no kept
-- part, and no mask part but zeros
-- the generic functions at another carrier
#guard foldColG OpsT.m101 [10] [3, 4] == ((101 + 1 - 10) * 3 + 10 * 4) % 101
#guard colVecG OpsT.m101 4 8 [1, 2, 3] [7, 8] == #[1, 2, 3, 0, 7, 8, 0, 0]
#guard eqVecG OpsT.m101 3 6 [0, 1] == #[0, 0, 1, 0, 0, 0] && eqVecG OpsT.m101 2 6 [0, 1] == #[0, 0, 0, 0, 0, 0]

end Fmt.M3
