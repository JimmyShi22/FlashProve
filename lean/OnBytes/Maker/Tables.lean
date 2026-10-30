-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Tables.lean: the openings that the three chains of one file hold, as one list of
tables keyed by the tree's number over the whole file, and the stored table's openings as one table.

Definitions alone. The file is a key file or a proof file as the program's reader returns it
(`Proof.TailRead`); which tree an opening belongs to is read off the plain data of the three chains
(`Three.Whole`, OnBytes/Three/Data.lean), round by round and in the file's order: first the stored
table's openings of a round, then the trees'. The pattern at one chain is `Run.toBPrfP`
(Run/ParseThin.lean) and, for stored tables, `Run.PQ.extOf` (Run/PlanQX.lean).

Main names:
  `roundsFit`: a test: a chain as read has the data's number of rounds, and each round as many
    openings as the data's round has stored tables and trees.
  `ownRowsW`, `storedRowsW`: all openings of the three chains, in the file's order: a tree's under
    its number over the whole file, a stored table's beside its description.
  `rowOK`, `storedOK`: the tests on one opening. The shape as read must be the data's own before
    `Run.OpenB.ok` is asked, which computes with the depth.
  `tabsW`: for each opened tree one table, a row for each listed position: the column, the typed
    salt, the path. The typed salt begins with the run's value of the chain that sent the tree, also
    where a later chain opens it. The tables of a tree that is opened more than once are appended.
  `extTabW`, `extW`: the same for the stored table, whose leaves begin with the configuration's
    digest; as a list, and as a function of the position.
  `tabsWFull`, `extTabWFull`, `extWFull`: the same tables with whole paths: at each listed position
    the siblings from the leaves up, looked up among the vertices that the reader's walk has met
    (`Run.pathFrom`, Run/ParseFull.lean); nothing if a vertex lacks. In `tabsW` a path is made from
    the pruned set of that one opening's own list (`Run.OpenB.paths`).
  `sameTwice`: a test: two rows at one position hold one column and one salt. The tables return
    nothing where it fails.
  `SameTwice`: that test's matter as a hypothesis on the file as read.
Limits: nothing is proved here. `SameTwice` is a hypothesis: where one position is opened at two
lists the file holds column and salt twice, and a reading that returns has one digest of the leaf
there, not one column. That a yes of the program gives `tabsW` a value is not stated. No hash is
computed here: that a row's path leads to a root is not tested. Nothing on soundness.


-/
import OnBytes.Three.Data
import Run.ParseThin
import Run.PlanQX

set_option autoImplicit false

namespace OnBytes.Maker

open Iop Rom Compile
open _root_.Run (OpenB Row3 atT pathFrom)
open _root_.Run.PQ (SgX)

/-- An opening as a reader holds it: the shape, the listed positions, what was read. -/
abbrev Opened : Type := Fmt.Shape × List ℕ × Fmt.OpenOut

/-- The same as the library's typing takes it. -/
def asOpenB (x : Opened) : OpenB := ⟨x.1.a, x.2.1, x.2.2.cols, x.2.2.salts, x.2.2.given⟩

/-- The three chains as read, by number: 0, 1, 2. -/
def chainOf (r : Proof.TailRead) : ℕ → Fmt.ChainOut
  | 0 => r.first.out
  | 1 => r.shared.out
  | _ => r.second.out

/-- A chain as read has the data's number of rounds, and each round as many openings as the data's
round has stored tables and trees. -/
def roundsFit (ds : List Three.RDL) (o : Fmt.ChainOut) : Bool :=
  ds.length == o.rounds.size &&
    (ds.zip o.rounds.toList).all fun x => x.2.opens.length == x.1.stored.length + x.1.opens.length

/-- The trees' openings of one chain, each under its tree's number over the whole file. In a round
they stand behind the stored tables' openings. -/
def ownRows (ds : List Three.RDL) (o : Fmt.ChainOut) : List (ℕ × Opened) :=
  (ds.zip o.rounds.toList).flatMap fun x => x.1.opens.zip (x.2.opens.drop x.1.stored.length)

/-- The stored tables' openings of one chain, each beside its description. -/
def storedRows (ds : List Three.RDL) (o : Fmt.ChainOut) : List (Fmt.Stored × Opened) :=
  (ds.zip o.rounds.toList).flatMap fun x => x.1.stored.zip x.2.opens

/-- The three chains fit. -/
def fitsW (W : Three.Whole) (r : Proof.TailRead) : Bool :=
  roundsFit W.ds₁ r.first.out && roundsFit W.ds₂ r.shared.out && roundsFit W.ds₃ r.second.out

/-- All trees' openings of the file, in the file's order. -/
def ownRowsW (W : Three.Whole) (r : Proof.TailRead) : List (ℕ × Opened) :=
  ownRows W.ds₁ r.first.out ++ (ownRows W.ds₂ r.shared.out ++ ownRows W.ds₃ r.second.out)

/-- All openings of stored tables in the file, in the file's order. -/
def storedRowsW (W : Three.Whole) (r : Proof.TailRead) : List (Fmt.Stored × Opened) :=
  storedRows W.ds₁ r.first.out ++ (storedRows W.ds₂ r.shared.out ++ storedRows W.ds₃ r.second.out)

/-- The tests on a tree's opening: the tree is in the table; the shape as read is the table's; then
the library's own test, at the plan's bytes of a salt. -/
def rowOK (W : Three.Whole) (saltBytes : ℕ) (x : ℕ × Opened) : Bool :=
  match W.table[x.1]? with
  | none => false
  | some t => x.2.1 == t.shape && (asOpenB x.2).ok saltBytes t.shape.W

/-- The tests on a stored table's opening: the shape as read is the description's; the depth is a;
the table stands under the statement's item 0; then the library's own test, at the table's bytes of
a salt. -/
def storedOK (a : ℕ) (x : Fmt.Stored × Opened) : Bool :=
  x.2.1 == x.1.sh && x.1.sh.a == a && x.1.item == 0 && (asOpenB x.2).ok x.1.salt x.1.sh.W

/-- The run's value of the chain that sent the tree number j. -/
def runOfTree (W : Three.Whole) (r : Proof.TailRead) (j : ℕ) : Option ByteArray :=
  (W.table[j]?).bind fun t => (chainOf r t.chain).run

/-- One opening's table, at the sender's run value, with the library's own paths. -/
def tableOf (W : Three.Whole) (r : Proof.TailRead) (x : ℕ × Opened) :
    Option (ℕ × List (ℕ × Row3)) :=
  (runOfTree W r x.1).map fun run => (x.1, (asOpenB x.2).table run (asOpenB x.2).paths)

/-- One table a tree: the tables under one number appended, in their order. -/
def merged (rows : List (ℕ × List (ℕ × Row3))) : List (ℕ × List (ℕ × Row3)) :=
  (rows.map (·.1)).eraseDups.map fun j => (j, (rows.filter (·.1 == j)).flatMap (·.2))

/-- Two rows at one position hold one column and one salt. -/
def sameTwice (tab : List (ℕ × Row3)) : Bool :=
  tab.all fun y =>
    match tab.lookup y.1 with
    | none => false
    | some z => z.1 == y.2.1 && z.2.1 == y.2.2.1

/-- **The tables over the whole file.** saltBytes: the plan's bytes of a salt. Nothing: the chains
do not fit the data, an opening fails its tests, a sender has no run's value, or one position of a
tree is opened twice with two columns or two salts. -/
def tabsW (W : Three.Whole) (saltBytes : ℕ) (r : Proof.TailRead) :
    Option (List (ℕ × List (ℕ × Row3))) :=
  if fitsW W r && (ownRowsW W r).all (rowOK W saltBytes) then
    ((ownRowsW W r).mapM (tableOf W r)).bind fun rows =>
      if (merged rows).all (fun t => sameTwice t.2) then some (merged rows) else none
  else none

/-- **The stored table's openings as one table.** a: the table's depth. cfg: the configuration's
digest, with which a stored leaf's typed salt begins. -/
def extTabW (a : ℕ) (cfg : ByteArray) (W : Three.Whole) (r : Proof.TailRead) :
    Option (List (ℕ × Row3)) :=
  if fitsW W r && (storedRowsW W r).all (storedOK a) then
    let tab := (storedRowsW W r).flatMap fun x => (asOpenB x.2).table cfg (asOpenB x.2).paths
    if sameTwice tab then some tab else none
  else none

/-- The same as a function of the position. A symbol holds its position and its column. -/
def extW (a : ℕ) (cfg : ByteArray) (W : Three.Whole) (r : Proof.TailRead) :
    Option ((oneExternalString (2 ^ a) SgX).Pos → Option (Opening 256 SgX)) :=
  (extTabW a cfg W r).map fun tab p => atT (fun c => some (p.val, c)) tab p.val

/-! ## The same with whole paths -/

/-- The whole path of each listed position, from the vertices that the reader's walk has met. -/
def fullPaths (x : Opened) : Option (List (List (Dig 256))) :=
  x.2.1.mapM (pathFrom x.1.a x.2.2.seen)

/-- One opening's table, at the sender's run value, with whole paths. -/
def tableOfFull (W : Three.Whole) (r : Proof.TailRead) (x : ℕ × Opened) :
    Option (ℕ × List (ℕ × Row3)) :=
  (runOfTree W r x.1).bind fun run =>
    (fullPaths x.2).map fun ps => (x.1, (asOpenB x.2).table run ps)

/-- **The tables over the whole file, with whole paths.** The tests are `tabsW`'s. Nothing also
where a vertex of a path lacks. -/
def tabsWFull (W : Three.Whole) (saltBytes : ℕ) (r : Proof.TailRead) :
    Option (List (ℕ × List (ℕ × Row3))) :=
  if fitsW W r && (ownRowsW W r).all (rowOK W saltBytes) then
    ((ownRowsW W r).mapM (tableOfFull W r)).bind fun rows =>
      if (merged rows).all (fun t => sameTwice t.2) then some (merged rows) else none
  else none

/-- **The stored table's openings as one table, with whole paths.** -/
def extTabWFull (a : ℕ) (cfg : ByteArray) (W : Three.Whole) (r : Proof.TailRead) :
    Option (List (ℕ × Row3)) :=
  if fitsW W r && (storedRowsW W r).all (storedOK a) then
    ((storedRowsW W r).mapM fun x =>
      (fullPaths x.2).map fun ps => (asOpenB x.2).table cfg ps).bind fun ts =>
        if sameTwice ts.flatten then some ts.flatten else none
  else none

/-- The same as a function of the position. -/
def extWFull (a : ℕ) (cfg : ByteArray) (W : Three.Whole) (r : Proof.TailRead) :
    Option ((oneExternalString (2 ^ a) SgX).Pos → Option (Opening 256 SgX)) :=
  (extTabWFull a cfg W r).map fun tab p => atT (fun c => some (p.val, c)) tab p.val

/-! ## The hypothesis -/

/-- What an opening holds at its listed positions: position, column, the file's salt. -/
def listed (x : Opened) : List (ℕ × List UInt64 × ByteArray) :=
  x.2.1.zip (x.2.2.cols.zip x.2.2.salts)

/-- **A hypothesis on a file as read and on the data's numbering**: wherever two listed entries, in
one opening or in two, stand at one position of one tree by the data's number, or of the stored
table, they hold one column and one salt. -/
def SameTwice (W : Three.Whole) (r : Proof.TailRead) : Prop :=
  (∀ x ∈ ownRowsW W r, ∀ y ∈ ownRowsW W r, x.1 = y.1 →
    ∀ u ∈ listed x.2, ∀ v ∈ listed y.2, u.1 = v.1 → u.2 = v.2) ∧
  (∀ x ∈ storedRowsW W r, ∀ y ∈ storedRowsW W r,
    ∀ u ∈ listed x.2, ∀ v ∈ listed y.2, u.1 = v.1 → u.2 = v.2)

end OnBytes.Maker
