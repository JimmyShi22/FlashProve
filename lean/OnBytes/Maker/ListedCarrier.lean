-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/ListedCarrier.lean: where openings can stand in the proof string that is laid of an
outside parser's carrier (File.toBPrf, OnBytes/Maker/CarrierTyping.lean), as two lists of numbers
taken off the carrier's rows. Definitions.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

The verifier along lists (verifyWholeL, OnBytes/Maker/ListedWhole.lean) asks its caller at which
leaves of the file's own trees, and at which positions of the stored table, the proof string holds
an opening. The string's openings are look-ups in the carrier's rows, so the leaves that the rows
name are enough. The lists are made here, in Lean, of a carrier k; the laws ask that it is the k of
which the string is laid, and verifyCarrier (OnBytes/Maker/ListedCarrierTop.lean) lays one k at all
three places. No list is handed over beside the carrier.

Main definitions.
  leavesOfCarrier k j: the leaves that the rows under the tree's number j name, in the carrier's
    order. A leaf that two rows name stands twice.
  ownOfCarrier D k: round by round and tree by tree these leaves (ownWhole,
    OnBytes/Maker/ListedTyped.lean).
  listedOfCarrier a k: the leaves that the stored table's rows name, those below 2 ^ a, as positions
    of the stored table.

Limits. Definitions alone: that the string has no opening elsewhere is shown in
OnBytes/Maker/ListedCarrierLaws.lean. The lists are not sorted and can hold a number twice. They can
hold a number at which the string has no opening: a second entry under one tree's number, a column
that does not type. So an honest file's tree must ride as one entry, its leaves each once; the
carrier's reader (Carrier.read, OnBytes/Maker/Carrier.lean) refuses numbers that do not rise
strictly. They are made whether or not a string is laid of the carrier. leavesOfCarrier walks all
trees of the carrier once for each tree's number. Nothing on time or memory is a theorem. Nothing on
soundness.
The program does not import this file.


-/
import OnBytes.Maker.ListedTyped
import OnBytes.Maker.Carrier

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Maker

open TypedOracleCompiler.Compile.Batch (Leaves)
open _root_.Iop (oneExternalString)
open _root_.Run.PQ (SgX)

/-- The leaves that the rows under the tree's number j name, in the carrier's order. -/
def leavesOfCarrier (k : Carrier.File) (j : ℕ) : List ℕ :=
  (k.trees.filter fun t => t.tree == j).flatMap fun t => t.rows.map fun x => x.leaf

/-- **The leaves of the file's own trees at which the carrier's string can hold an opening.** -/
def ownOfCarrier (D : WholeD) (k : Carrier.File) : Leaves := ownWhole D (leavesOfCarrier k)

/-- **The positions of the stored table at which the carrier's string can hold an opening.** -/
def listedOfCarrier (a : ℕ) (k : Carrier.File) : List (oneExternalString (2 ^ a) SgX).Pos :=
  (k.stored.map fun x => x.leaf).filterMap fun x =>
    if h : x < 2 ^ a then some (⟨x, h⟩ : Fin (2 ^ a)) else none

end OnBytes.Maker
