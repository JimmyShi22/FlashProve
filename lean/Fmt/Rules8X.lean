-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/Rules8X.lean: a chain in a file that reads stored tables: the strict reader of Fmt/Rules8.lean
with, after a round's draw of positions, the openings of stored trees, each at its own part of the
draws.

A proof file can open Merkle trees whose roots are not sent in the file but are in the statement
(stored tables). This file extends the strict reader of Fmt/Rules8.lean, which cuts the file,
recomputes the hash chain and checks every opening, to such openings. A layer on Fmt/Rules8.lean:
none of its definitions is changed. Every function is total; whatever test on the file's bytes fails
ends in "refused" (none; false in `verifyXW` and `verifyX`). The programs are the C++ implementation
that comes with this Lean code.

Sources. The format page (docs/format/FORMAT.md, which comes with the programs),
rules R4.6, R7.4, R7.14, R7.19, R8.7, R13.10 and R13.12 as named here;
this file is not held against that page,
and may differ from it. Part 4 below renders R7.19's last sentences on the record of met vertices.
No Mathlib.




   R7.19: a step can give the draws of one round to several trees: the first draws to one, the next
   to the next, and so on. The plan's entry has the sum of these numbers and one range. Each part's
   list is made from its draws alone: sorted, each position once within the part; a position drawn
   in two parts stands in both lists. Listed positions are one list for the round, the set of all
   its draws.
   R8.7: stored trees stand in no chain's list of trees; those that a round reads are opened first,
   in the order of the statement's items that hold their roots; then the chain's own trees.
   R4.6: the root under which a stored table's openings are checked is the root in the statement's
   item, and no other.
   R7.4: a stored tree's leaves are hashed under 174, from the configuration's digest, and its tree
   has the number 0.
   R7.14: the record of met vertices is keyed by the root's 32 bytes, within a session: a stored
   tree's as a chain's own (Fmt/Rules8.lean: addSeen): two items that hold one root share a record.

1. What the file contains.
    `Stored`: A stored tree as one round opens it: its shape; the bytes of a leaf's salt in it
       (R13.10: a stored table's column stands under the salt of the table's shape, which need not
       be the plan's); the number of the statement's item that has its root; its part of the round's
       draws (from lo on, count of them). Its root and its leaves' start are no fields: the root
       stands in the statement, the start is the configuration's digest (`Spec.cfg`). Each has its
       one home in the description, and the reader takes it from there.
    `SpecX`: A description (`Spec`) and, round by round, the stored trees that the round opens.
    `itemRoot`: R4.6: the root that the statement's item number k has.
    `SpecX.ok`: The description is in order; one list a round; in each that is not empty: increasing
       items, each of which the statement has, with a root of 32 bytes; shapes that are stored trees
       with the number 0, within the format's bounds, the salt's length among them, none deeper than
       the round's range; no part is empty; the parts follow one another from the first draw on and
       use up all draws (R7.19: the entry has their sum). Such a round opens no tree of the chain's
       own (by R8.7 each tree of a cut round is opened at the list of its own part, and here the
       stored trees' parts leave no draw over), nor a tree given from outside (`Src.given`):
       `Round.opens` must be empty.
    `readStored`, `roundX`, `foldRoundsX`, `readChainX`, `wholeChainX`: The reader.
    `storedKey which`: 2^16 + which: the name under which a stored tree's columns are in a view (a
       chain's own trees have numbers below 2^16).
    `viewX`: The view: Fmt/View.lean's type as it is; in each round the stored trees' columns first,
       in the items' order, then the own trees'; within a tree by increasing position.
    `verifyXW`, `verifyX`: The verifier on bytes: the reader, then a decision on the view.

2. What is checked when the file compiles. 16 tests (#guard), at a made-up example of this library's
own (no protocol; no file or number of the programs'): two stored tables of depth 2 under one
configuration, the same columns under other salts; the statement: their two items; a chain of one
round with work that draws five positions, cut 2 | 3, and one last round that draws nothing. A
table's salts have 40 bytes, the plan's word is 48. The draws: 0, 1 | 3, 1, 1. The honest file is
read; the lists are those of the parts; the view has the columns under storedKey 0 and 1. Refused:
one bit at every byte of both openings; a byte short, a byte more; the two openings changed over;
each table at the other's part or at the list of all draws; the cut 3 | 2 on the same file (the file
made for that cut is read). R13.10: the same file under a description that gives the tables the
plan's length of a salt. R4.6: a statement with another root in either item, or the roots changed
over, the file made anew for that statement by the honest rules from the true tables. R7.4: a table
whose leaves were hashed from another start, its own root in the statement, shown in order (with a
control: read by itself with that start, the opening ends in that root). Descriptions that are not
in order (eight kinds; a further kind, a salt's length that the format does not admit, in the test
of R13.10), and two that are. R7.14: both items hold one root and the file shows that table twice:
read: one record for both. The last test is not at this example: at `Known8.file2` (Fmt/Rules8.lean)
`wholeChainX` at `SpecX.plain` and `wholeChain` end in the same chain value.

3. Theorems (at the identity monad, any hash).
    `X8.plain`: At `SpecX.plain S` (S with an empty list for every round) wholeChainX is wholeChain.
    `X8.plain_view`: And viewX is viewOf (for what has as many rounds as the description).

4. What is this library's own, and what is not claimed.
   This library's own, where the page is silent or wider. Parts are given to stored trees alone here
   (R7.19 speaks of trees): a round in which a chain's own tree has a part of the draws is not
   rendered: a description with stored and own openings in one round is not in order. A stored tree
   may be shallower than the round's range and is then opened at its part's draws modulo 2^(its
   depth), as R13.12 has it for a chain's trees (idle where range and depth are one). The record of
   R7.14 is kept, though by R7.19 a verifier that keeps none for the two tables of a link gives the
   same verdict unless their roots are the same 32 bytes. The session is one chain, as in
   Fmt/Rules8.lean: a verdict that reads a key's chains and an entry's together must hand the record
   on (readChainX takes one and gives it back): not rendered.
   Not claimed: which description belongs to which protocol. Anything on a table's name, its
   record's answers or the commitment ID (R4.10, R4.8, R4.11). That the numbers of the parts stand
   in a parameter item (R7.19): that is the matter of whoever makes the description.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Fmt.M1View
import Fmt.ParamsRead

namespace Fmt

/-- A stored tree as one round opens it. -/
structure Stored where
  sh    : Shape
  /-- the bytes of a leaf's salt in this table's tree: the table's own number (R13.10), not
  `Plan.salt`; it is no field of `Shape` -/
  salt  : Nat
  /-- the number, from 0, of the statement's item that holds the root -/
  item  : Nat
  /-- its part of the round's draws: from the draw number lo on, count of them -/
  lo    : Nat
  count : Nat
  deriving DecidableEq, Inhabited

/-- A chain that reads stored tables. -/
structure SpecX where
  base   : Spec
  /-- round by round -/
  stored : List (List Stored)

/-- R4.6: the root that the statement's item number k holds: the item's value begins with the root
as a string of bytes -/
def itemRoot (statement : ByteArray) (k : Nat) : Option ByteArray :=
  ((rdItems statement.size statement 0).bind fun x => x.1[k]?).bind fun it =>
    (rdText it.2 0).map (·.1)

/-- If the parts follow one another without a gap from the draw number i on: the number of the draw
after the last part; else none. -/
def partsFrom : Nat → List Stored → Option Nat
  | i, [] => some i
  | i, t :: ts => if t.lo == i then partsFrom (i + t.count) ts else none

/-- the conditions on one round's stored trees -/
def storedOk (statement : ByteArray) (r : Round) (ts : List Stored) : Bool :=
  ts.isEmpty ||
  (r.opens.isEmpty && increasing (ts.map (·.item)) && partsFrom 0 ts == some r.entry.poss &&
    ts.all fun t =>
      t.sh.stored && decide (t.sh.a ≤ r.entry.logN) && depthOK t.sh.a && decide (1 ≤ t.sh.W) &&
        decide (t.sh.W < 2 ^ 24) && t.sh.tree == 0 && saltLenOK t.salt &&
        ((itemRoot statement t.item).any fun x => x.size == 32) && decide (1 ≤ t.count))

/-- The conditions that do not look at a file. -/
def SpecX.ok (S : SpecX) : Bool :=
  S.base.ok && S.stored.length == S.base.rounds.length &&
    (S.base.rounds.zip S.stored).all fun x => storedOk S.base.statement x.1 x.2

/-- a stored tree's part of the draws -/
def partOf (t : Stored) (poss : List Nat) : List Nat := (poss.drop t.lo).take t.count

def storedKey (which : Nat) : Nat := 2 ^ 16 + which

section
variable {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)

/-- the openings of a round's stored trees, each at the list of its part of the draws, checked
against its root and against what was met under that root before -/
def readStored (cfg statement : ByteArray) (P : Plan) (poss : List Nat) (b : ByteArray) :
    List Stored → Seen → Nat → m (Option (List (Shape × List Nat × OpenOut) × Seen × Nat))
  | [], sn, i => pure (some ([], sn, i))
  | t :: ts, sn, i => do
    let xs := listOf ((partOf t poss).map (· % 2 ^ t.sh.a))
    match ← readOpeningW h cfg P.field t.salt t.sh cfg xs b i with
    | none => pure none
    | some o =>
      if some o.root == itemRoot statement t.item then
        match addSeen o.root (entered o.seen) sn with
        | none => pure none
        | some sn' =>
          match ← readStored cfg statement P poss b ts sn' o.next with
          | none => pure none
          | some (l, sn'', k) => pure (some ((t.sh, xs, o) :: l, sn'', k))
      else pure none

/-- One round: Fmt/Rules8.lean's step, with the stored trees' openings between the list and the own
trees' -/
def roundX (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray) (s : St)
    (r : Round) (ts : List Stored) : m (Option St) :=
  match slice b s.pos r.entry.msg with
  | none => pure none
  | some msg =>
    match whole (readItems P.field r.items) msg with
    | none => pure none
    | some vals =>
      match readNonce P r.entry.work b (s.pos + r.entry.msg) with
      | none => pure none
      | some (nonce, i1) => do
        match ← Chain.queryW h s.chain msg r.kind r.entry.work nonce
            ((wordsAtMost r.entry r.kind + 3) / 4) with
        | none => pure none
        | some (c, vb) =>
          let drawn := drawRound P.field r.entry r.kind (rowOf vb)
          let l := listOf drawn.poss
          match readList P r.entry.poss l b i1 with
          | none => pure none
          | some (_, i2) =>
            let roots := s.roots ++ (rootsOf vals).toArray
            match ← readStored h cfg statement P drawn.poss b ts s.seen i2 with
            | none => pure none
            | some (colsS, sn1, i2') =>
              match ← readOpens h cfg P run roots drawn.poss b r.opens sn1 i2' with
              | none => pure none
              | some (cols, sn, i3) =>
                pure
                  (some ⟨i3, c, roots, sn, s.out.push ⟨msg, vals, nonce, drawn, l, colsS ++ cols⟩⟩)

def foldRoundsX (cfg statement : ByteArray) (P : Plan) (run : Option ByteArray) (b : ByteArray) :
    List (Round × List Stored) → St → m (Option St)
  | [], s => pure (some s)
  | r :: rs, s => do
    match ← roundX h cfg statement P run b s r.1 r.2 with
    | none => pure none
    | some s' => foldRoundsX cfg statement P run b rs s'

/-- A chain in a file, from the place i on. -/
def readChainX (S : SpecX) (seen : Seen) (b : ByteArray) (i : Nat) : m (Option (ChainOut × Nat)) :=
  if !S.ok then pure none
  else
    let rnd : Option (Option ByteArray × Nat) :=
      match S.base.rand with
      | .inFile => (slice b i 32).map fun x => (some x, i + 32)
      | .given x => some (some x, i)
      | .none => some (none, i)
    match rnd with
    | none => pure none
    | some (x, i0) => do
      let pd ← paramsDigestW h S.base.params
      match ← startChainW h S.base.label pd S.base.statement x with
      | none => pure none
      | some hd =>
        match ← foldRoundsX h S.base.cfg S.base.statement S.base.plan hd.run b
            (S.base.rounds.zip S.stored) ⟨i0, ⟨S.base.label, hd.rho0, 0⟩, #[], seen, #[]⟩ with
        | none => pure none
        | some s => pure (some (⟨pd, hd.run, hd.rho0, s.chain.rho, s.seen, s.out⟩, s.pos))

/-- The same, and nothing stands behind the chain. -/
def wholeChainX (S : SpecX) (b : ByteArray) : m (Option ChainOut) := do
  match ← readChainX h S [] b 0 with
  | some (o, j) => pure (if j == b.size then some o else none)
  | none => pure none

end

/-- the opened columns of one round: the stored trees' first, under their items' keys; then the own
trees' -/
def openedX (first : Nat) (ts : List Stored) (r : RoundOut) : List (Nat × Nat × List UInt64) :=
  ((ts.zip r.opens).flatMap fun y =>
      (y.2.2.1.zip y.2.2.2.cols).map fun p => (storedKey y.1.item, p.1, p.2)) ++
    openedOf first { r with opens := r.opens.drop ts.length }

/-- The view. -/
def viewX (S : SpecX) (o : ChainOut) : View where
  rounds := o.rounds.toList.map fun r => ⟨noRoots r.vals, r.drawn⟩
  opened := (S.stored.zip o.rounds.toList).flatMap fun y => openedX S.base.firstTree y.1 y.2

def verifyXW {m : Type → Type} [Monad m] (h : Nat → Nat → Nat → ByteArray → ByteArray → m ByteArray)
    {Y : Type} (S : SpecX) (dec : Y → View → Bool) (y : Y) (file : ByteArray) : m Bool := do
  match ← wholeChainX h S file with
  | none => pure false
  | some o => pure (dec y (viewX S o))

def verifyX {Y : Type} (S : SpecX) (dec : Y → View → Bool) (y : Y) (file : ByteArray) : Bool :=
  verifyXW (m := Id) formatHash S dec y file

/-- a description without a stored tree -/
def SpecX.plain (S : Spec) : SpecX := ⟨S, S.rounds.map fun _ => []⟩

namespace X8
namespace Spec

def plain : Prop :=
  ∀ (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray) (S : Spec) (b : ByteArray),
    wholeChainX (m := Id) h (SpecX.plain S) b = wholeChain (m := Id) h S b

def plain_view : Prop :=
  ∀ (S : Spec) (o : ChainOut),
    o.rounds.size = S.rounds.length → viewX (SpecX.plain S) o = viewOf S.firstTree o

end Spec
end X8


/-! ## The two theorems -/

namespace X8

theorem all_plain (st : ByteArray) (l : List Round) :
    ((l.zip (l.map fun _ => ([] : List Stored))).all fun x => storedOk st x.1 x.2) = true := by
  induction l with
  | nil => rfl
  | cons r l ih => simpa [storedOk] using ih

theorem ok_plain (S : Spec) : (SpecX.plain S).ok = S.ok := by
  unfold SpecX.ok SpecX.plain
  simp [all_plain]

theorem step_plain (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray) (cfg st : ByteArray)
    (P : Plan) (run : Option ByteArray) (b : ByteArray) (s : St) (r : Round) :
    roundX (m := Id) h cfg st P run b s r [] = step (m := Id) h cfg P run b s r := by
  unfold roundX step
  rfl

theorem fold_plain (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray) (cfg st : ByteArray)
    (P : Plan) (run : Option ByteArray) (b : ByteArray) (l : List Round) (s : St) :
    foldRoundsX (m := Id) h cfg st P run b (l.zip (l.map fun _ => [])) s =
      foldRounds (m := Id) h cfg P run b l s := by
  induction l generalizing s with
  | nil => rfl
  | cons r l ih =>
    show (do match ← roundX (m := Id) h cfg st P run b s r [] with
      | none => pure none
      | some s' => foldRoundsX (m := Id) h cfg st P run b (l.zip (l.map fun _ => [])) s') = (do match ← step (m := Id) h cfg P run b s r with
      | none => pure none
      | some s' => foldRounds (m := Id) h cfg P run b l s')
    rw [step_plain]
    cases step (m := Id) h cfg P run b s r with
    | none => rfl
    | some s' => exact ih s'

theorem readChain_plain (h : Nat → Nat → Nat → ByteArray → ByteArray → Id ByteArray) (S : Spec)
    (seen : Seen) (b : ByteArray) (i : Nat) :
    readChainX (m := Id) h (SpecX.plain S) seen b i = readChain (m := Id) h S seen b i := by
  unfold readChainX readChain
  rw [ok_plain]
  simp only [SpecX.plain, fold_plain]
  rfl

theorem plain : Spec.plain := by
  intro h S b
  unfold wholeChainX wholeChain
  rw [readChain_plain]
  rfl

theorem opened_plain (first : Nat) (r : RoundOut) : openedX first [] r = openedOf first r := by
  unfold openedX
  simp

theorem flat_plain (first : Nat) :
    ∀ (l : List Round) (rs : List RoundOut), rs.length = l.length →
      (((l.map fun _ => ([] : List Stored)).zip rs).flatMap fun y => openedX first y.1 y.2) =
        rs.flatMap (openedOf first)
  | [], [], _ => rfl
  | _ :: l, r :: rs, e => by
    simp only [List.map_cons, List.zip_cons_cons, List.flatMap_cons, opened_plain]
    rw [flat_plain first l rs (by simpa using e)]
  | [], _ :: _, e => by simp at e
  | _ :: _, [], e => by simp at e

theorem plain_view : Spec.plain_view := by
  intro S o e
  unfold viewX viewOf SpecX.plain
  simp only
  rw [flat_plain S.firstTree S.rounds o.rounds.toList (by simpa using e)]

end X8

/-! ## A made-up toy: two stored tables, one round that reads both -/

namespace ToyX8

open Toy8M (good cfg0 buildH)

def plan : Plan where
  field := .two
  salt := 48
  nonce := 2
  posB := 0
  samples := 0
  saved := 1
  entries := [
    { name := "x: both tables", work := 4, msg := 8, poss := 5, logN := 2 },
    { name := "x: nothing", msg := 8 } ]

def ent (i : Nat) : Entry := plan.entries.getD i default
def params : ByteArray := paramsBytes plan cfg0 []
/-- the chain's random bytes: chosen so that the five draws at the true roots tell the cases
apart: 0, 1 | 3, 1, 1: a position twice within a part; a position in both parts; each table's list
differs from the other's, from the list of all draws and from its own list at the cut 3 | 2 -/
def rnd : ByteArray := pattern 32 9 2

/-- both tables have one shape; a stored table's tree has the number 0 -/
def sh : Shape := { a := 2, W := 3, stored := true, tree := 0 }
def col (x : Nat) : List UInt64 := [UInt64.ofNat (x * x), 1, UInt64.ofNat (5 * x)]
/-- the same columns under other salts; a table's salts have 40 bytes, the plan's word is 48 -/
def saltT (which x : Nat) : ByteArray := pattern 40 (which + 2) (x + 1)
/-- all values of a table's tree, its leaves hashed from a given start -/
def valuesAt (start : ByteArray) (which : Nat) : List (List ByteArray) :=
  buildH good sh.a
    ((List.range (2 ^ sh.a)).map fun x =>
      Id.run (leafW good (leafNo sh.stored) sh.tree sh.a x start (col x) (saltT which x)))
def values (which : Nat) : List (List ByteArray) := valuesAt cfg0 which
def openT (which : Nat) (xs : List Nat) : ByteArray :=
  openingBytes sh.a col (saltT which) (values which) xs
def root0 : ByteArray := rootOf (values 0)
def root1 : ByteArray := rootOf (values 1)

/-- R4.6: the statement: the two tables' items: each its root as a string of bytes and an empty list
of answers -/
def stmt (r0 r1 : ByteArray) : ByteArray :=
  tableItem "x: the first table" r0 [] ++ tableItem "x: the further table" r1 []

def base (r0 r1 : ByteArray) : Spec where
  label := 11
  plan := plan
  params := params
  statement := stmt r0 r1
  rand := .inFile
  cfg := cfg0
  rounds := [
    { entry := ent 0, kind := .positions, items := [.word] },
    { entry := ent 1, kind := .nothing, items := [.f] } ]

/-- the description: the two roots (in the statement alone), and where the draws are cut -/
def specAt (r0 r1 : ByteArray) (n0 : Nat) : SpecX :=
  ⟨base r0 r1, [[⟨sh, 40, 0, 0, n0⟩, ⟨sh, 40, 1, n0, 5 - n0⟩], []]⟩

def spec : SpecX := specAt root0 root1 2

/-- the toy prover at a statement: the least nonce, the draws -/
def drawnAt (r0 r1 : ByteArray) : Nat × List Nat := ((do
  let hd ← Id.run (startChainW good 11 (Id.run (paramsDigestW good params)) (stmt r0 r1) (some rnd))
  let q := fun n =>
    (Id.run (Chain.queryW good ⟨11, hd.rho0, 0⟩ (u64n 5) .positions (ent 0).work n
          (blocksFor (wordsAtMost (ent 0) .positions)))).map
      fun x => (drawRound .two (ent 0) .positions (rowOf x.2)).poss
  let nonce ← (List.range 4096).find? fun n => (q n).isSome
  (q nonce).map fun p => (nonce, p)) : Option (Nat × List Nat)).getD (0, [])

/-- the two parts' lists at a statement and a cut -/
def listsAt (r0 r1 : ByteArray) (n0 : Nat) : List Nat × List Nat :=
  (listOf ((drawnAt r0 r1).2.take n0), listOf ((drawnAt r0 r1).2.drop n0))

/-- the file at a statement, from its two openings -/
def fileAt (r0 r1 o0 o1 : ByteArray) : ByteArray :=
  rnd ++ u64n 5 ++ (u64n (drawnAt r0 r1).1).extract 0 2 ++ o0 ++ o1 ++ u64n 8

def lists : List Nat × List Nat := listsAt root0 root1 2
def fileOf (o0 o1 : ByteArray) : ByteArray := fileAt root0 root1 o0 o1
def honest : ByteArray := fileOf (openT 0 lists.1) (openT 1 lists.2)

def read (S : SpecX) (b : ByteArray) : Option ChainOut := wholeChainX (m := Id) formatHash S b

end ToyX8

open ToyX8 in
#guard spec.ok && (drawnAt root0 root1).2 == [0, 1, 3, 1, 1] && lists == ([0, 1], [1, 3]) && itemRoot (stmt root0 root1) 0 == some root0 && itemRoot (stmt root0 root1) 1 == some root1 && itemRoot (stmt root0 root1) 2 == none
-- The honest file is read; the two lists are those of the two parts of the draws
open ToyX8 in
#guard ((read spec honest).bind fun o => o.rounds[0]?.map fun r => r.opens.map (·.2.1)) == some [lists.1, lists.2]
-- The view: the first table's columns under storedKey 0, then the second's under storedKey 1, each
-- by increasing position
open ToyX8 in
#guard ((read spec honest).map fun o => (viewX spec o).opened) == some (lists.1.map (fun x => (storedKey 0, x, col x)) ++ lists.2.map fun x => (storedKey 1, x, col x))
open ToyX8 in
#guard storedKey 0 = 65536 && ((read spec honest).map fun o => (viewX spec o).rounds.map (·.drawn.poss)) == some [(drawnAt root0 root1).2, []]
-- Refused: a byte short; a byte more; one bit at every place of the two openings (columns, salts,
-- given digests of either table)
open ToyX8 in
#guard (read spec (honest.extract 0 (honest.size - 1))).isNone && (read spec (honest ++ zeroBytes 1)).isNone
open ToyX8 in
#guard (List.range (honest.size - 42 - 8)).all fun i => (read spec (flipAt honest (42 + i))).isNone
-- the two openings changed over; each table opened at the other's part, or at the list of all draws
-- (the lists are not the same)
open ToyX8 in
#guard (read spec (fileOf (openT 1 lists.2) (openT 0 lists.1))).isNone && lists.1 != lists.2 && (read spec (fileOf (openT 0 lists.2) (openT 1 lists.1))).isNone &&
  (read spec (fileOf (openT 0 (listOf (drawnAt root0 root1).2)) (openT 1 (listOf (drawnAt root0 root1).2)))).isNone
-- R4.6: the root is the statement's. A statement whose first (second) item holds another root, the
-- file made anew for that statement by the honest rules (its nonce, its draws, the true tables'
-- openings at the lists of these draws): refused: the walk does not end in the statement's root.
-- The control: the same making at the true roots gives the honest file
open ToyX8 in
#guard (read (specAt zero32 root1 2) (fileAt zero32 root1 (openT 0 (listsAt zero32 root1 2).1) (openT 1 (listsAt zero32 root1 2).2))).isNone &&
  (read (specAt root0 zero32 2) (fileAt root0 zero32 (openT 0 (listsAt root0 zero32 2).1) (openT 1 (listsAt root0 zero32 2).2))).isNone &&
  (read (specAt root1 root0 2) (fileAt root1 root0 (openT 0 (listsAt root1 root0 2).1) (openT 1 (listsAt root1 root0 2).2))).isNone &&
  fileAt root0 root1 (openT 0 (listsAt root0 root1 2).1) (openT 1 (listsAt root0 root1 2).2) == honest
-- the tables changed over in statement and file: read (the two tables have one shape)
open ToyX8 in
#guard (read (specAt root1 root0 2) (fileAt root1 root0 (openT 1 (listsAt root1 root0 2).1) (openT 0 (listsAt root1 root0 2).2))).isSome
-- R13.10: a stored table's leaves are read under the table's own length of a salt (40), not the
-- plan's (48): the honest file under a description that gives the tables the plan's: in order, and
-- refused
open ToyX8 in
#guard plan.salt == 48 && (⟨base root0 root1, [[⟨sh, 48, 0, 0, 2⟩, ⟨sh, 48, 1, 2, 3⟩], []]⟩ : SpecX).ok && (read ⟨base root0 root1, [[⟨sh, 48, 0, 0, 2⟩, ⟨sh, 48, 1, 2, 3⟩], []]⟩ honest).isNone && !(⟨base root0 root1, [[⟨sh, 41, 0, 0, 5⟩], []]⟩ : SpecX).ok
-- The cut belongs to the description: the same file under the cut 3 | 2: refused; the file made for
-- that cut: read
open ToyX8 in
#guard (read (specAt root0 root1 3) honest).isNone && (read (specAt root0 root1 3) (fileOf (openT 0 (listsAt root0 root1 3).1) (openT 1 (listsAt root0 root1 3).2))).isSome
-- descriptions that are not in order: parts that leave a draw out, or overlap; items not
-- increasing; an item that the statement does not have; a shape that is no stored tree; a stored
-- tree with another number than 0; a list of stored trees too few; an own tree's opening in the
-- round that reads stored trees. In order: one table at all five draws
open ToyX8 in
#guard !(⟨base root0 root1, [[⟨sh, 40, 0, 0, 2⟩, ⟨sh, 40, 1, 2, 2⟩], []]⟩ : SpecX).ok && !(⟨base root0 root1, [[⟨sh, 40, 0, 0, 3⟩, ⟨sh, 40, 1, 2, 3⟩], []]⟩ : SpecX).ok && !(⟨base root0 root1, [[⟨sh, 40, 1, 0, 2⟩, ⟨sh, 40, 1, 2, 3⟩], []]⟩ : SpecX).ok &&
  !(⟨base root0 root1, [[⟨sh, 40, 0, 0, 2⟩, ⟨sh, 40, 2, 2, 3⟩], []]⟩ : SpecX).ok && !(⟨base root0 root1, [[⟨{ sh with stored := false }, 40, 0, 0, 5⟩], []]⟩ : SpecX).ok && !(⟨base root0 root1, [[⟨{ sh with tree := 1 }, 40, 0, 0, 5⟩], []]⟩ : SpecX).ok &&
  !(⟨base root0 root1, [[⟨sh, 40, 0, 0, 5⟩]]⟩ : SpecX).ok && (⟨base root0 root1, [[⟨sh, 40, 0, 0, 5⟩], []]⟩ : SpecX).ok &&
  !storedOk (stmt root0 root1) { entry := ent 0, kind := .positions, items := [.word], opens := [({ a := 2, W := 1, tree := 0 }, .own 0)] } [⟨sh, 40, 0, 0, 5⟩] && storedOk (stmt root0 root1) { entry := ent 0, kind := .positions, items := [.word] } [⟨sh, 40, 0, 0, 5⟩]
-- R7.14: one table named by two items (both items hold the first table's root; the file shows the
-- first table twice): read: one root, one record; at the two tables' own roots: two
open ToyX8 in
#guard ((read (specAt root0 root0 2) (fileAt root0 root0 (openT 0 (listsAt root0 root0 2).1) (openT 0 (listsAt root0 root0 2).2))).map fun o => o.seen.length) == some 1 && ((read spec honest).map fun o => o.seen.length) == some 2
-- R7.4: the reader starts a stored tree's leaves from the configuration's digest: a first table
-- whose leaves were hashed from another start (the vertices' start, the columns and the salts as
-- before), its own root in the statement, the file made for that statement, the table shown in
-- order: refused
open ToyX8 in
#guard rootOf (valuesAt zero32 0) != root0 && (read (specAt (rootOf (valuesAt zero32 0)) root1 2) (fileAt (rootOf (valuesAt zero32 0)) root1 (openingBytes sh.a col (saltT 0) (valuesAt zero32 0) (listsAt (rootOf (valuesAt zero32 0)) root1 2).1) (openT 1 (listsAt (rootOf (valuesAt zero32 0)) root1 2).2))).isNone
-- the control: that opening by itself, read with that other start, ends in that root: so the start
-- alone refuses the file above
open ToyX8 in
#guard ((Id.run (readOpeningW Toy8M.good Toy8M.cfg0 .two 40 sh zero32 (listsAt (rootOf (valuesAt zero32 0)) root1 2).1 (openingBytes sh.a col (saltT 0) (valuesAt zero32 0) (listsAt (rootOf (valuesAt zero32 0)) root1 2).1) 0)).map fun o => o.root == rootOf (valuesAt zero32 0)) == some true
-- at `SpecX.plain` the layer is Fmt/Rules8.lean's reader (the theorem; here once by evaluation, at
-- the page's own file)
#guard ((wholeChainX (m := Id) formatHash (SpecX.plain (Known8.spec .two)) Known8.file2).map fun o => hex o.rho) == ((wholeChain (m := Id) formatHash (Known8.spec .two) Known8.file2).map fun o => hex o.rho)

end Fmt
