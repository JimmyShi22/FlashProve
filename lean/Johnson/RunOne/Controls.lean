-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Controls.lean: a few turns of a parsed key file or proof file, MADE IN MEMORY behind
the reader of the parsed file (OnBytes/Maker/Carrier.lean), for the files of lean/Ask/ that run a
verifier on a stored example and must also show a "no". Each is a plain function on the parsed
record; no file is written; no program is changed. Definitions with code.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

Words. A turn: one planted change of the record. The seal: the last round of the first chain. The
slot's leaf: the leaf of the binding tree (the library's request tree) that holds this file's value.

Each turn returns none where the record has no place for it: a caller says so aloud. Where a NO is
expected it may take orSame instead: a turn without a place then changes nothing, gets the true
file's yes, and so shows itself. Where a YES is expected orSame must not be taken: an idle turn
would pass for a control.

Main names; where something is expected to refuse, with what that is, by reading (the verifier:
verifyOneProtocol, OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean):
  turnRoot     one bit of the first root that the first chain sends. It stands in hashed strings, so
               every later draw moves: openings then stand where the verifier does not read (the
               strict format), and where it reads there is none.
  turnLacks    the first row of the first tree that has one is left out: a place that is read has
               no opening. The strict format lets that pass; the forests cannot be made.
  turnMore     one row more in such a tree, a copy of a row under the next leaf's number, where that
               leaf is one of the tree's and is not opened: an opening where the verifier does not
               read: the strict format alone refuses.
  turnSalt     one bit of an opened leaf's salt. It enters the leaf's hash alone: the tree's root is
               not made again; every other part holds.
  turnColumn   the first word of an opened column is another element of the field: the root is not
               made again; the decision reads the symbol, so it may refuse too.
  turnRequest  one bit of the salt of the slot's leaf in the binding tree. It enters that leaf's
               hash alone: the check in the binding tree refuses; every other part holds.
  turnLonger   that salt is one zero byte longer: a test in front of the verifier refuses (rsaltFit,
               OnBytes/Maker/Page/GuardVerify.lean; File.slotFits,
               OnBytes/Maker/CarrierTyping.lean); the verifier tests no length there and would
               refuse at the binding tree's check.
  turnTable    one bit of the field root (the stored table's root). The typing does not read that
               field: it is refused only at an entry that makes the commitment ID of it, or holds it
               against the table that it has from elsewhere; at another entry: the true file's yes.
  turnCopy     the number of the stored copy is one more. The typing does not read it either: it
               comes in where the entry lays it into the first silent round, or tests it.
  turnSeal     the seal's nonce is one more: no proof string is laid: the typing asks that the seal
               has no item and the nonce 0 (File.sealBare).
  turnUnread   A YES IS EXPECTED: one bit of the last digest of a stored row's path, where another
               opened leaf lies below that vertex: the stored table's tree is walked jointly over
               all opened leaves; the walk computes the vertex itself and does not read the digest.
  replyOther   on the user's side: one bit of the reply's first byte. Where the request ends at the
               window's end, as in the stored small example, and the changed token is still below
               the size of the vocabulary (at the small size it always is: that size, 512, is
               even), that is a well-formed false claim, and the decision holds the reply against
               the proof's own; elsewhere the reader of request and reply refuses in front.
Limits: the expectations are by reading and hang on the entry that calls the verifier (what it tests
in front; whence it takes the table and the copy's number). Turned data that are refused show that
these tests can say no at one file; they are no search for a false proof. The turn with a yes shows
that a parsed file holds bytes that bind nothing. Nothing on soundness.
The program does not import this file.


-/
import OnBytes.Maker.Carrier

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Controls

open OnBytes.Maker.Carrier (File Round Row TreeRows)

/-- One bit of the first byte; none at no byte. -/
def bit0 (b : ByteArray) : Option ByteArray :=
  if b.size = 0 then none else some (b.set! 0 (b.get! 0 ^^^ 1))

/-- f at the first member at which it returns; none if it returns nowhere. -/
def atFirst {α : Type} (f : α → Option α) : List α → Option (List α)
  | [] => none
  | a :: l =>
    match f a with
    | some b => some (b :: l)
    | none => (atFirst f l).map (a :: ·)

/-- f at the last member. -/
def atLast {α : Type} (f : α → Option α) (l : List α) : Option (List α) :=
  match l.reverse with
  | [] => none
  | a :: r => (f a).map fun b => (b :: r).reverse

/-- Another element of the field: one less; 1 at 0. -/
def otherElt (w : UInt64) : UInt64 := if w == 0 then 1 else w - 1

/-- The turn, or the record as it is where the turn has no place. Only where a no is expected. -/
def orSame (f : File → Option File) (k : File) : File := (f k).getD k

def turnRoot (k : File) : Option File :=
  (atFirst (fun r : Round =>
    (atFirst (fun g : _root_.Fmt.ItemValue =>
      match g with
      | .root d => (bit0 d).map _root_.Fmt.ItemValue.root
      | _ => none) r.items).map fun it => { r with items := it }) k.rounds1).map
    fun rs => { k with rounds1 := rs }

/-- f at the rows of the first tree at which it returns. -/
def atTree (f : List Row → Option (List Row)) (k : File) : Option File :=
  (atFirst (fun t : TreeRows => (f t.rows).map fun rs => { t with rows := rs }) k.trees).map
    fun ts => { k with trees := ts }

def turnLacks : File → Option File :=
  atTree fun rows =>
    match rows with
    | [] => none
    | _ :: rs => some rs

/-- Behind the first row whose next leaf is one of the tree's (its number is below 2 ^ the length of
the row's path) and is not among the rows: a copy of it under that leaf's number. The rows stay in
rising order. -/
def moreRow (rows : List Row) : Option (List Row) :=
  let seen := rows.map (·.leaf)
  let rec go : List Row → Option (List Row)
    | [] => none
    | x :: l =>
      if seen.contains (x.leaf + 1) || 2 ^ x.path.length ≤ x.leaf + 1 then (go l).map (x :: ·)
      else some (x :: { x with leaf := x.leaf + 1 } :: l)
  go rows

def turnMore : File → Option File := atTree moreRow

def turnSalt : File → Option File :=
  atTree (atFirst fun x => (bit0 x.salt).map fun s => { x with salt := s })

def turnColumn : File → Option File :=
  atTree (atFirst fun x =>
    match x.column with
    | [] => none
    | w :: ws => some { x with column := otherElt w :: ws })

def turnRequest (k : File) : Option File :=
  (bit0 k.slotSalt).map fun s => { k with slotSalt := s }

def turnLonger (k : File) : Option File := some { k with slotSalt := k.slotSalt.push 0 }

def turnTable (k : File) : Option File := (bit0 k.root).map fun r => { k with root := r }

def turnCopy (k : File) : Option File := some { k with copy := k.copy + 1 }

/-- Does another stored row's leaf lie below the sibling of x's vertex just below the root. -/
def topShared (l : List Row) (x : Row) : Bool :=
  let top := x.path.length - 1
  x.path.length != 0 && l.any fun y => y.leaf >>> top == (x.leaf >>> top) ^^^ 1

def turnUnread (k : File) : Option File :=
  (atFirst (fun x : Row =>
    if topShared k.stored x then (atLast bit0 x.path).map fun p => { x with path := p }
    else none) k.stored).map fun st => { k with stored := st }

def turnSeal (k : File) : Option File :=
  (atLast (fun r : Round => some { r with nonce := r.nonce + 1 }) k.rounds1).map
    fun rs => { k with rounds1 := rs }

def replyOther (y : ByteArray) : Option ByteArray := bit0 y

end Johnson.RunOne.Controls
