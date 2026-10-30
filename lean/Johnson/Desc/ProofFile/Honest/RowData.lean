-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/RowData.lean: the data of an oracle message's main rows, as one
function of the readers (`Cells`, `Weights`, `TableRand`: Honest/ForKinds.lean), of what was heard,
and of the message's address. The name and the type; no filling. Executable definitions, and tests
at a toy example;
no theorem.

The lines that begin with `#guard` are tests, checked by evaluation: Lean's evaluator runs each of
them when the file is compiled, and the build fails if one is false. The kernel does not check them,
and they prove nothing.

What it is. The entries of the main rows' messages that are no coin of the book's: the witness's and
the index's elements as the layout packs them, and values that are computed from these, from the
stored tables' pads and encoding randomness (a folded row) and from challenges. No random tail, no
mask row, no pad.
What it is not. The rows of a carrying message, which hold what a fold has left: these are computed
from the book's coins too, and no coin of the book's is among this function's arguments.

  `MsgAddr`   a message's address: the part that holds its sending, and its number in that sending,
     from 0: the two by which `carriedName` names a carried block
  `Readers`   the witness, the index, the stored tables' pads and encoding randomness by table: no
     default
  `RowData`   two fields are public: `heardAt`: how many challenges have been heard when the
     message's sending begins; `lays`: whether there is an element of data at (row, place). `entry`:
     the element, of the base field or of the extension field. `ready`: the filling's one test: on
     the challenges heard (they have the form that `entry` reads) and on the public data from which
     the filling is computed
  `RowDataOf Xi`   a filling as a function of the public instance
  `RowData.at_`   the one call: it cuts the list of challenges to `heardAt`, so that a caller which
     has heard more gets the sender's own term; `none` where `lays` returns false
  `RowData.heardOk`, `padInMain`, `RowData.clear`   two executable tests on public data, for the
     place of use: enough has been heard; no data is put at a pad's place
  `RowData.readyAt`   a test that every caller can ask before it reads
  `RowData.ask`   `at_` after that test: it returns an error with a message. A caller is to read
     `entry` through `at_` or `ask` alone (`join`, `over`, `comap` pass it on); no type enforces
     that. `at_` asks neither `heardOk` nor `ready`
  `RowData.forSend`, `asE`, `asProgE`   the forms in which the kinds' definitions take it
  `RowData.empty`, `join`, `over`, `apart`, `comap`   for a filling that is given message by message
     (`join`: by the address) or array by array inside one message (`over`: by the place; `apart`:
     no place is filled twice); for a kept message that is sent again, whose data is that of the
     message that bore it

A coin goes first. Whether an entry is a coin is said by the message's shape, not by the data: every
caller is to put the coin there and is not to ask this function. Where there is neither a coin nor
data, `asE` returns 0. For the folded row, Omega and W that is the format's own rule for the entries
that the vector leaves free (docs/format/09-key-and-leaf-files.md, "Where a vector is in an oracle
message's main rows"); for a segment's own messages no line of the format is cited here: whoever
fills them says what is at a place where the layout puts no element.

Limits.
  * Nothing here fills it: `switchData` (Honest/K2/OwnData.lean) and `wData` (Honest/K13/WData.lean)
    are fillings.
  * `Readers` holds three of the four parts of the input of a prover's side: the instance has no
    reader. A message whose data depends on the request (the output head's vector of reads: which
    positions have a cost) is filled by a `RowDataOf`, never from data that was computed for another
    request.
  * `entry` is given no round that was shown: a message whose data depends on a sent value has no
    place here.
  * That the list which a caller gives begins with the challenges that the sender had heard has to
    be proved by the caller.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.ForKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open OnBytes.Slice (toE toF ofE ofF)

/-- **An oracle message's address.** -/
structure MsgAddr where
  /-- the part that holds the sending -/
  sender : Addr
  /-- the message's number in that sending, from 0 -/
  msg : Nat
  deriving DecidableEq

/-- **The readers**: all that the data of a message's main rows is computed from, beside the
challenges: the witness, the index, and the stored tables' pads and encoding randomness, for each
committed table, by the statement's item: a folded row holds the fold of a stored table's rows'
messages, pads and random tails. These are no coins of the book's: they are part of the prover's
input. No field has a default: a caller that reads none of a reader still says which it gives. -/
structure Readers where
  cells : Cells
  weights : Weights
  rand : Nat → TableRand

/-- **The data of the main rows of all messages.** -/
structure RowData where
  /-- public: how many challenges have been heard when the message's sending begins -/
  heardAt : MsgAddr → Nat
  /-- public: there is an element of data at this main row and place -/
  lays : MsgAddr → Nat → Nat → Bool
  /-- the element there, computed from the readers, the challenges heard before the sending, the
  address, the main row, the place. Read only where `lays` returns true -/
  entry : Readers → List Fmt.Drawn → MsgAddr → Nat → Nat → Cb.Gl.F ⊕ Cb.Gl.E
  /-- the filling's one test: on the challenges heard before the sending (they have the form that
  `entry` reads of them) and on the public data from which the filling is computed. Every test of
  its own that a filling has is put in here: `readyAt` and `ask` ask nothing else. Where it returns
  false, the value of `entry` means nothing -/
  ready : List Fmt.Drawn → MsgAddr → Bool := fun _ _ => true

/-- **A filling may be a function of the public instance**, which each caller applies to its own
input's instance (`Local.x`, Honest/Frame.lean): so a message whose data depends on words of the
request has a place, and no reader is given a fixed value for them. It reads the public instance
alone. `Xi`: the description's instance. -/
abbrev RowDataOf (Xi : Type) : Type := Xi → RowData

/-- **The one call.** `heard`: all that the caller has heard, the oldest first. -/
def RowData.at_ (D : RowData) (R : Readers) (heard : List Fmt.Drawn) (a : MsgAddr) (r j : Nat) :
    Option (Cb.Gl.F ⊕ Cb.Gl.E) :=
  if D.lays a r j then some (D.entry R (heard.take (D.heardAt a)) a r j) else none

/-- A test for the place of use: a caller that has heard n challenges has heard all that the
message's data reads. -/
def RowData.heardOk (D : RowData) (a : MsgAddr) (n : Nat) : Bool := decide (D.heardAt a ≤ n)

/-- **A test that every caller can ask before it reads**: enough has been heard, and the filling's
own test returns true. -/
def RowData.readyAt (D : RowData) (heard : List Fmt.Drawn) (a : MsgAddr) : Bool :=
  D.heardOk a heard.length && D.ready (heard.take (D.heardAt a)) a

/-- **The call that asks first**: `at_` after `readyAt`: it returns an error with a message where
fewer challenges have been heard than the message's data reads, or where the filling's own test
(`ready`) returns false. `at_` itself asks neither: where `ready` returns false its value means
nothing, and `asE` would turn a `none` into 0 silently. So: a caller that can return an error calls
`ask`; a caller that must stay total calls `at_`, and `readyAt` is among the tests at its place of
use or among the named hypotheses of the lemma on it. -/
def RowData.ask (D : RowData) (R : Readers) (heard : List Fmt.Drawn) (a : MsgAddr) (r j : Nat) :
    Except String (Option (Cb.Gl.F ⊕ Cb.Gl.E)) :=
  if !D.heardOk a heard.length then
    .error "fewer challenges have been heard than the message's data reads"
  else if !D.ready (heard.take (D.heardAt a)) a then
    .error "the message's data is not ready: its test on the public data and the challenges says no"
  else .ok (D.at_ R heard a r j)

/-- The places of the pad of a message's sample where it lies in a main row: the last places of the
last main row: one for each answer if the main rows are over the extension field, three for each if
they are over the base field. `ell`: the base code's message length. None where the message has a
mask row or no sample. -/
def padInMain (ell : Nat) (s : OnBytes.OracleShape) : List (Nat × Nat) :=
  if s.maskRows != 0 || s.mainRows == 0 then []
  else
    let n := (if s.mainDeg == 3 then 1 else 3) * s.answers
    (List.range n).map fun i => (s.mainRows - 1, ell - n + i)

/-- **A test for the place of use: no data is put at any of the pad's places.** As a spot check
alone: nor at the first row beyond the rows, nor at the first place beyond the length. -/
def RowData.clear (D : RowData) (a : MsgAddr) (ell : Nat) (s : OnBytes.OracleShape) : Bool :=
  ((padInMain ell s).all fun p => !D.lays a p.1 p.2) &&
    !D.lays a s.mainRows 0 && (List.range s.mainRows).all fun r => !D.lays a r ell

/-! ## The three forms -/

/-- As the shared sending takes it: the part's address fixed; the message's number, row, place. -/
def RowData.forSend (D : RowData) (R : Readers) (sender : Addr) (heard : List Fmt.Drawn)
    (k r j : Nat) : Option (Cb.Gl.F ⊕ Cb.Gl.E) :=
  D.at_ R heard ⟨sender, k⟩ r j

/-- An entry as an element of the extension field; 0 where there is no data. -/
def asE : Option (Cb.Gl.F ⊕ Cb.Gl.E) → Cb.Gl.E
  | some (.inr x) => x
  | some (.inl x) => toE (ofF x, 0, 0)
  | none => toE (0, 0, 0)

/-- The same as the programs' element. -/
def asProgE (x : Option (Cb.Gl.F ⊕ Cb.Gl.E)) : OnBytes.E := OnBytes.E.ofTriple (ofE (asE x))

/-! ## A filling that is given message by message -/

/-- No message has data. -/
def RowData.empty : RowData :=
  { heardAt := fun _ => 0, lays := fun _ _ _ => false, entry := fun _ _ _ _ _ => .inl (toF 0) }

/-- A's at the addresses that `mine` names, B's at the others. -/
def RowData.join (mine : MsgAddr → Bool) (A B : RowData) : RowData :=
  { heardAt := fun a => if mine a then A.heardAt a else B.heardAt a
    lays := fun a => if mine a then A.lays a else B.lays a
    entry := fun R h a => if mine a then A.entry R h a else B.entry R h a
    ready := fun h a => if mine a then A.ready h a else B.ready h a }

/-- **Two fillings of one message, joined by place**: A's element where A has one, else B's. Each is
given the challenges cut to its own `heardAt`. For arrays of two writers that lie in one oracle
message. -/
def RowData.over (A B : RowData) : RowData :=
  { heardAt := fun a => max (A.heardAt a) (B.heardAt a)
    lays := fun a r j => A.lays a r j || B.lays a r j
    entry := fun R h a r j =>
      if A.lays a r j then A.entry R (h.take (A.heardAt a)) a r j
      else B.entry R (h.take (B.heardAt a)) a r j
    ready := fun h a => A.ready (h.take (A.heardAt a)) a && B.ready (h.take (B.heardAt a)) a }

/-- An executable test: no place is filled by both, at the rows and places below the bounds. -/
def RowData.apart (A B : RowData) (a : MsgAddr) (rows ell : Nat) : Bool :=
  (List.range rows).all fun r => (List.range ell).all fun j => !(A.lays a r j && B.lays a r j)

/-- The data of the message at f a, under the address a: a kept message that is sent again. -/
def RowData.comap (f : MsgAddr → MsgAddr) (D : RowData) : RowData :=
  { heardAt := fun a => D.heardAt (f a), lays := fun a => D.lays (f a)
    entry := fun R h a => D.entry R h (f a), ready := fun h a => D.ready h (f a) }

/-! ### Tests at a toy example -/

namespace RowDataToy

def a₀ : MsgAddr := ⟨toyTo 0, 0⟩
def a₁ : MsgAddr := ⟨toyTo 0, 1⟩
def a₂ : MsgAddr := ⟨toyTo 4, 0⟩
def dE (x : UInt64) : Fmt.Drawn := ⟨[(x, 0, 0)], [], [], none⟩
def cells : Cells := ⟨fun _ _ r j => toF (10 * r.toUInt64 + j.toUInt64)⟩
def weights : Weights := ⟨fun _ _ => toF 0⟩
/-- The pads and encoding randomness: the entry q of row r of table i's tail is 100 i + 10 r + q. -/
def rand (i : Nat) : TableRand :=
  ⟨fun _ _ => toF 0, fun r q => toF (100 * i.toUInt64 + 10 * r.toUInt64 + q.toUInt64)⟩
def R : Readers := ⟨cells, weights, rand⟩

/-- Message 0: two rows of three cells, over the base field; a row has eight places. Message 1: one
element, the second challenge heard times nothing: that challenge itself. -/
def D : RowData :=
  { heardAt := fun a => if a == a₁ then 2 else 0
    lays := fun a r j => if a == a₀ then decide (r < 2 ∧ j < 3)
      else (a == a₁ || a == a₂) && r == 0 && j == 0
    entry := fun R h a r j =>
      if a == a₀ then .inl (R.cells.cell 0 "m" r j)
      else if a == a₂ then .inl ((R.rand 1).tail r j)
      else .inr (toE (((h.getLast?.bind (·.elems.head?)).getD (0, 0, 0))))
    ready := fun h a => a != a₁ || (h.getLast?.any fun d => d.elems.length == 1) }

def seeE (x : Option (Cb.Gl.F ⊕ Cb.Gl.E)) : UInt64 × UInt64 × UInt64 := ofE (asE x)

#guard seeE (D.at_ R [] a₀ 1 2) == (12, 0, 0) && (D.at_ R [] a₀ 1 3).isNone
-- a caller that has heard more gets the sender's term: the second challenge, not the last
#guard seeE (D.at_ R [dE 5, dE 7] a₁ 0 0) == (7, 0, 0) &&
  seeE (D.at_ R [dE 5, dE 7, dE 9, dE 11] a₁ 0 0) == (7, 0, 0)
#guard D.heardOk a₁ 2 && !D.heardOk a₁ 1 && D.heardOk a₀ 0
-- ready: enough heard, and the second challenge holds one element; not so where it holds none
#guard D.readyAt [dE 5, dE 7, dE 9] a₁ && !D.readyAt [dE 5] a₁ &&
  !D.readyAt [dE 5, ⟨[], [], [], none⟩, dE 9] a₁ && D.readyAt [] a₀
-- the call that asks first: the element where all is ready; an error where too little was heard,
-- and where the second challenge holds no element: there `at_` returns (0, 0, 0) silently
#guard ((D.ask R [dE 5, dE 7, dE 9] a₁ 0 0).toOption.map seeE) == some (7, 0, 0) &&
  (D.ask R [dE 5] a₁ 0 0).toOption.isNone &&
  (D.ask R [dE 5, ⟨[], [], [], none⟩, dE 9] a₁ 0 0).toOption.isNone &&
  seeE (D.at_ R [dE 5, ⟨[], [], [], none⟩, dE 9] a₁ 0 0) == (0, 0, 0)
-- the pad's places: two rows of eight over the base field, one answer, no mask row: the last three
-- of the last row; with a mask row: none
#guard padInMain 8 { mainRows := 2, mainDeg := 1, maskRows := 0, answers := 1 } ==
  [(1, 5), (1, 6), (1, 7)]
#guard padInMain 8 { mainRows := 2, mainDeg := 1, maskRows := 1, answers := 1 } == []
#guard D.clear a₀ 8 { mainRows := 2, mainDeg := 1, maskRows := 0, answers := 1 }
-- at a length of four the third cell of the last row would be on the pad: the test returns false
#guard !D.clear a₀ 4 { mainRows := 2, mainDeg := 1, maskRows := 0, answers := 1 }
-- the shared sending's form; a kept message under another address; a join
#guard seeE (D.forSend R (toyTo 0) [] 0 0 1) == (1, 0, 0)
#guard seeE ((D.comap fun a => if a == a₂ then a₀ else a).at_ R [] a₂ 1 1) == (11, 0, 0)
-- an entry that is computed from the pads and encoding randomness: table 1's tail
#guard seeE (D.at_ R [] a₂ 0 0) == (100, 0, 0)
#guard ((RowData.join (· == a₀) D RowData.empty).at_ R [dE 5, dE 7] a₁ 0 0).isNone &&
  seeE ((RowData.join (· == a₀) D RowData.empty).at_ R [] a₀ 0 2) == (2, 0, 0)
-- two fillings of one message, by place: D fills the places 0 to 2 of two rows; the other the place
-- 5 of row 0, from the first challenge heard, where D's own message reads none
def D' : RowData :=
  { heardAt := fun _ => 1, lays := fun a r j => a == a₀ && r == 0 && j == 5
    entry := fun _ h _ _ _ => .inr (toE ((h.getLast?.bind (·.elems.head?)).getD (0, 0, 0))) }
#guard seeE ((D.over D').at_ R [dE 5, dE 7] a₀ 0 5) == (5, 0, 0) &&
  seeE ((D.over D').at_ R [dE 5, dE 7] a₀ 1 2) == (12, 0, 0) &&
  ((D.over D').at_ R [dE 5, dE 7] a₀ 0 4).isNone && (D.over D').heardAt a₀ == 1
#guard D.apart D' a₀ 2 8 && !D.apart D a₀ 2 8
-- a filling that depends on the instance: two instances, two entries
def DX : RowDataOf Nat := fun x =>
  { heardAt := fun _ => 0, lays := fun a r j => a == a₀ && r == 0 && j == 0
    entry := fun _ _ _ _ _ => .inl (toF x.toUInt64) }
#guard seeE ((DX 4).at_ R [] a₀ 0 0) == (4, 0, 0) && seeE ((DX 9).at_ R [] a₀ 0 0) == (9, 0, 0)
#guard asProgE none == OnBytes.E.ofTriple (0, 0, 0)

end RowDataToy

end ProofFile.Honest
