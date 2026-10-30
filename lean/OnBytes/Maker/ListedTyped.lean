-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ListedTyped.lean: where openings can stand in the proof string that the typing of a
whole file makes (typeFile, OnBytes/Maker/TypeFile.lean), as two lists of numbers taken off the
file as read. Definitions.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

The verifier along lists (verifyWholeL, OnBytes/Maker/ListedWhole.lean) asks its caller at which
leaves of the file's own trees, and at which positions of the stored table, the proof string holds
an opening. The typing's openings are look-ups in finite tables, and a table has a row only at a
position that an opening of the file lists. So the listed positions of the file's openings are
enough, and no table is built here.

Main definitions.
  leavesUnder rows j: the positions that the openings under the tree's number j list, in the file's
    order. A position that two openings list stands twice.
  ownChain shared keys b ds: for a chain's written rounds, from the number b of its first tree on:
    round by round and tree by tree the list keys gives at the tree's number over the whole file; in
    the shared component's place if the flag shared is set, else in the slot's.
    It has the form of rdChain (OnBytes/Maker/ListedWhole.lean).
  ownWhole D keys: the same for all rounds of the file (the front, the joining round and the seam
    have no tree), with the flag set for the second chain alone. It has the form of rdWhole.
  ownOfRead a W r: ownWhole at the listed positions of the trees' openings of the file as read.
  listedOfRead a W r: the listed positions of the stored table's openings of the file as read, those
    below 2 ^ a, as positions of the stored table.

Limits. Definitions alone: that the typing's string has no opening elsewhere is shown in
OnBytes/Maker/ListedTypedLaws.lean. The lists are not sorted and can hold a number twice. They can
hold a number at which the string has no opening. They are made whether or not the typing returns a
string. Nothing on time or memory is a theorem: that no list of length 2 ^ depth or 2 ^ a is built
is by reading the bodies; each list of leaves, and the list of positions, is at most as long as the
number of positions that the openings of the file as read list. Nothing on soundness. The program
does not import this file.


-/
import OnBytes.Maker.ListedWhole
import OnBytes.Maker.Tables
import OnBytes.Maker.WholeOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Compile.Batch (Leaves)
open _root_.Iop (oneExternalString)
open _root_.Run.PQ (SgX)

/-- The positions that the openings under the number j list, in the file's order. -/
def leavesUnder (rows : List (ℕ × Opened)) (j : ℕ) : List ℕ :=
  (rows.filter fun x => x.1 == j).flatMap fun x => x.2.2.1

/-- A chain's written rounds, from tree number b on: for each tree the list that keys gives at its
number over the whole file. -/
def ownChain (shared : Bool) (keys : ℕ → List ℕ) : ℕ → List RDT → Leaves
  | _, [] => []
  | b, d :: ds =>
    let ls := (List.range d.trees.length).map fun k => keys (b + k)
    (if shared then (ls, []) else ([], ls)) :: ownChain shared keys (b + d.trees.length) ds

/-- All rounds of the file. -/
def ownWhole (D : WholeD) (keys : ℕ → List ℕ) : Leaves :=
  ([], []) :: (ownChain false keys 0 D.ds₁ ++
    ([], []) :: (ownChain true keys D.t₁ D.ds₂ ++
      ([], []) :: ownChain false keys (D.t₁ + D.t₂) D.ds₃))

/-- **The leaves of the file's own trees at which the typing's string can hold an opening.** -/
def ownOfRead (a : ℕ) (W : Three.Whole) (r : Proof.TailRead) : Leaves :=
  ownWhole (WholeD.of a W) (leavesUnder (ownRowsW W r))

/-- **The positions of the stored table at which the typing's string can hold an opening.** -/
def listedOfRead (a : ℕ) (W : Three.Whole) (r : Proof.TailRead) :
    List (oneExternalString (2 ^ a) SgX).Pos :=
  ((storedRowsW W r).flatMap fun x => x.2.2.1).filterMap fun x =>
    if h : x < 2 ^ a then some (⟨x, h⟩ : Fin (2 ^ a)) else none

end OnBytes.Maker
