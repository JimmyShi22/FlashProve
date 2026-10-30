-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/PubK13.lean: six public items of the first chain's table of promises, each with
its test on the record, as code: the half with code of one layer of the table's filling. No
Mathlib stands beneath this file, so what is written here can be run.

Why. Meaning.pub (Johnson/Desc/First/Borders.lean) is a letter: what each public item says of the
record. It is filled in layers: each layer lays its own items and hands every other item on to a
function that it is given.

What is said.
  noneSentC N    no oracle message has been sent, the frame awaits none at the start, the groups
                 are as many as the plan says there, and no row is pending.
  indexIsC n     the record's number of the index masks' message is n.
  indexThereC    the statement holds a message of that number.
  frontOkC P     where the record holds a linear claim: its masks are mask entries, and W's layout
                 has room for the column variables.
  evalLaidC P    the record holds a linear claim with these two; the row (Eval) can be made and lies
                 open on the own group; W's number, its table's size and the masks' places fit.
  wSitsC cs P    evalLaidC; and the record's codes are the plan's, W's number bears the plan's
                 shape, the codes' lengths are powers of two, the shape's code is in the list.
  wSeatC seat    W's message sits at that place of the book of trees.
  pileMasksC     every row on the table names mask entries of the index masks' message alone.
  ledgerAtC      a ledger is that of so many takes since it was made: its rows and row bits are the
                 shape's; what is left is at most the shape's count of free entries; "next" is
                 the number behind the last entry given (0 where none was given).
  ledgersFitC    every ledger in the statement is so.
  rowsWithinC    every mask entry that a row on the table names lies within its table.
  pileWithinC    ledgersFitC and rowsWithinC: ONE SENTENCE, so that it rides by itself past a block
                 that takes fresh entries of a ledger and lays them into a row.
  oneRowC        where the chain stands at its end: the rows on the table are one row, and it
                 names a mask entry. True wherever the chain does not stand there.
  pubK13C         THE LAYER's HALF WITH CODE: noneSent, indexIs, indexThere, frontOk, evalLaid and
                 the door's item "K13.wSits" are these; every other item is handed on.
                 It answers "K13.pileMasks", "K13.pileWithin", "K13.oneRow" no more:
                 these three have left the table's door; their tests stand here unturned.
  pubK13PlusC     the three names' half with code, apart: for a meaning at whose door they stand.
  k13ItemC, pubK13C_else   which items are the layer's; every other is left as it was.
That each test is the one of which the kind's laws speak is proved beside, in
Johnson/Desc/K13/Law/FillK13Laws.lean.
Called by name, of the verifier program's files: two that say yes or no: Statement.has,
Codes.lengthsOk (OnBytes/Iop/Ground.lean); a maker that may return nothing: linEvalRow; two that
always return: linLayW (OnBytes/Iop/Lin.lean), Statement.tableBits; two plain functions of numbers:
Send.freeMaskEntries (OnBytes/Iop/Send.lean), ceilLog2 (OnBytes/Iop/Ground.lean).

Limits. Nothing says here who makes or keeps an item. Nothing on soundness.

-/
import Johnson.Desc.First.Borders
import Johnson.Desc.K13.AtS
import OnBytes.Iop.Lin
import OnBytes.Iop.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13
open OnBytes
open VerifiableInference.Desc.First (S Pub Numbers rowOfClaim)

/-! Whether two rows are the same row can be decided: for "the row (Eval) lies open on the
group". -/
deriving instance DecidableEq for OnBytes.Tensor
deriving instance DecidableEq for OnBytes.Term
deriving instance DecidableEq for OnBytes.Single
deriving instance DecidableEq for OnBytes.Coeffs
deriving instance DecidableEq for OnBytes.Run
deriving instance DecidableEq for OnBytes.Form
deriving instance DecidableEq for OnBytes.MainForm
deriving instance DecidableEq for OnBytes.Row

/-- No oracle message has been sent, the frame awaits none at the start, and the statement has as
many groups as the plan says there; and no row is pending. -/
def noneSentC (N : Numbers) (s : S) : Bool :=
  (s.st.oracles.isEmpty && s.check.frame.atStart.isEmpty) && (s.st.groups.size == N.groupAt 0) &&
    s.out.pending.isEmpty

/-- The record's number of the index masks' message is n. -/
def indexIsC (n : Nat) (s : S) : Bool := s.out.indexMasks == n

/-- The statement holds a message of that number. -/
def indexThereC (s : S) : Bool := (s.st.oracles[s.out.indexMasks]?).isSome

/-- What goes on to the last chain, where the record holds it. -/
def linAtC (s : S) : Option LinFirst :=
  match s.here with
  | .mem a => a.lin
  | _ => none

/-- Every mask of the claim is a mask entry. -/
def claimMadeC (c : LinClaim) : Bool := c.masks.toList.all fun u => decide (u.part = .mask)

/-- The number of entries of a table; 0 for a table that is not there. -/
def tableSizeC (St : Statement) (o : Nat) (part : OnBytes.Part) : Nat :=
  if St.has o part then 2 ^ St.tableBits o part else 0

/-- In front of the batching's place. -/
def frontOkC (P : Where) (s : S) : Bool :=
  match linAtC s with
  | none => true
  | some l => claimMadeC l.claim && decide (P.lin.kCol ≤ (linLayW s.st.codes P.lin).bits)

/-- W's number, its table's size and the masks' places fit the statement. -/
def evalInC (St : Statement) (w : Nat) (lay : VectorLay) (masks : MaskForm) : Bool :=
  decide (w < St.oracles.size) && decide (tableSizeC St w .main = 2 ^ lay.bits) &&
    masks.all fun t => decide (t.1.oracle < St.oracles.size) &&
      decide (t.1.index < tableSizeC St t.1.oracle .mask)

/-- Behind W's sending. -/
def evalLaidC (P : Where) (s : S) : Bool :=
  match linAtC s with
  | none => false
  | some l =>
    claimMadeC l.claim && decide (P.lin.kCol ≤ (linLayW s.st.codes P.lin).bits) &&
      match linEvalRow P.lin l.claim l.w (linLayW s.st.codes P.lin), s.st.groups[l.own]? with
      | some r, some G =>
        decide (r ∈ G.rows.toList) &&
          evalInC s.st l.w (linLayW s.st.codes P.lin) (rowOfClaim l.claim).masks
      | _, _ => false

/-- W sits as the plan says: as a list of named clauses. -/
def wSitsLC (cs : Codes) (P : Where) (s : S) : List (String × Bool) :=
  ("the record has what the block behind W's commitment leaves", evalLaidC P s) ::
    match (linAtC s).bind fun l =>
      (linEvalRow P.lin l.claim l.w (linLayW s.st.codes P.lin)).map fun _ => l.w with
    | some w =>
      [("the reader gives a record of (Eval)", true),
       ("the record's codes are the plan's", decide (s.st.codes = cs)),
       ("W's number bears the plan's shape",
         decide ((s.st.oracles[w]?).map (·.shape) = some P.lin.w)),
       ("W's layout is the plan's", decide (linLayW s.st.codes P.lin = linLayW cs P.lin)),
       ("the codes' lengths are powers of two", cs.lengthsOk),
       ("the shape's code is in the list", decide (P.lin.w.code < cs.base.size))]
    | none => [("the reader gives a record of (Eval)", false)]

def wSitsC (cs : Codes) (P : Where) (s : S) : Bool := (wSitsLC cs P s).all (·.2)

/-- W's message sits at that place of the book of trees. -/
def wSeatC (seat : Nat × Nat) (s : S) : Bool :=
  (linAtC s).any fun l => s.book.place[l.w]? == some seat

/-- Every row on the table names mask entries of the index masks' message alone. -/
def pileMasksC (s : S) : Bool :=
  s.rows.all fun r => r.masks.all fun t => t.1.oracle == s.out.indexMasks

/-- The number behind the last of k entries that a ledger over m mask rows has given; 0 at k = 0. In
an entry's number the row is low: entry number j is row j % m, place j / m. -/
def nextAtC (m : Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => j % m + 2 ^ ceilLog2 m * (j / m) + 1

/-- A ledger is that of so many takes since it was made. -/
def ledgerAtC (codes : Codes) (x : OnBytes.Oracle) (l : OnBytes.Ledger) : Bool :=
  let m := x.shape.maskRows
  let free := Send.freeMaskEntries m (codes.mask.getD x.shape.maskCode default).ell x.shape.answers
  decide (0 < m) && decide (1 ≤ x.shape.answers) && l.rows == m && l.logRows == ceilLog2 m &&
    decide (l.left ≤ free) && l.next == nextAtC m (free - l.left)

/-- Every ledger in the statement is so. -/
def ledgersFitC (s : S) : Bool :=
  s.st.oracles.all fun x =>
    match x.ledger with
    | none => true
    | some l => ledgerAtC s.st.codes x l

/-- Every mask entry that a row on the table names lies within its table. -/
def rowsWithinC (s : S) : Bool :=
  s.rows.all fun r => r.masks.all fun t => decide (t.1.index < tableSizeC s.st t.1.oracle .mask)

/-- Every ledger fits, and every mask entry that a row on the table names lies within its table. -/
def pileWithinC (s : S) : Bool := ledgersFitC s && rowsWithinC s

/-- Where the chain stands at its end: one row on the table, with a mask entry. -/
def oneRowC (s : S) : Bool :=
  match s.here with
  | .mem _ =>
    match s.rows with
    | [r] => !r.masks.isEmpty
    | _ => false
  | _ => true

/-- Is the item one of this layer's? -/
def k13ItemC : Pub → Bool
  | .noneSent => true
  | .indexIs => true
  | .indexThere => true
  | .frontOk => true
  | .evalLaid => true
  | .more seg name => seg.isNone && name == "K13.wSits"
  | _ => false

/-- **The layer's half with code**: over whatever says the other items. P: the kind's numbers; cs:
the plan's codes; N: the table's numbers (of which indexNo and w are read). -/
def pubK13C {Pp : Type} (P : Where) (cs : Codes) (N : Numbers) (f : Pub → Pp × S → Bool) :
    Pub → Pp × S → Bool :=
  fun q a =>
    match q with
    | .noneSent => noneSentC N a.2
    | .indexIs => indexIsC N.indexNo a.2
    | .indexThere => indexThereC a.2
    | .frontOk => frontOkC P a.2
    | .evalLaid => evalLaidC P a.2
    | .more seg name =>
      if seg.isNone && name == "K13.wSits" then wSitsC cs P a.2 && wSeatC N.w a.2
      else f (.more seg name) a
    | q => f q a

section
variable {Pp : Type} (P : Where) (cs : Codes) (N : Numbers) (f : Pub → Pp × S → Bool)

theorem pubK13C_noneSent (a : Pp × S) : pubK13C P cs N f .noneSent a = noneSentC N a.2 := rfl
theorem pubK13C_indexIs (a : Pp × S) : pubK13C P cs N f .indexIs a = indexIsC N.indexNo a.2 := rfl
theorem pubK13C_indexThere (a : Pp × S) : pubK13C P cs N f .indexThere a = indexThereC a.2 := rfl
theorem pubK13C_frontOk (a : Pp × S) : pubK13C P cs N f .frontOk a = frontOkC P a.2 := rfl
theorem pubK13C_evalLaid (a : Pp × S) : pubK13C P cs N f .evalLaid a = evalLaidC P a.2 := rfl
theorem pubK13C_wSits (a : Pp × S) :
    pubK13C P cs N f (.more none "K13.wSits") a = (wSitsC cs P a.2 && wSeatC N.w a.2) := rfl

/-- Every other item is handed on. -/
theorem pubK13C_else (q : Pub) (h : k13ItemC q = false) (a : Pp × S) :
    pubK13C P cs N f q a = f q a := by
  cases q with
  | more seg name =>
    have h1 : (seg.isNone && name == "K13.wSits") = false := h
    show (if seg.isNone && name == "K13.wSits" then _ else _) = _
    rw [h1]
    rfl
  | _ => first | rfl | (simp [k13ItemC] at h)

end

/-! ## The three names that have left the layer

They carry a fact on the chain's state past many sub-protocols.
`pubK13C` does not answer them. Their tests stand above, unturned. The half below answers them over
whatever says the other items: for whoever wants a meaning at whose door they still stand. -/

/-- Is the item one of the three? -/
def k13PlusItemC : Pub → Bool
  | .more seg name =>
    seg.isNone && (name == "K13.pileMasks" || name == "K13.pileWithin" || name == "K13.oneRow")
  | _ => false

/-- The three names' half with code. -/
def pubK13PlusC {Pp : Type} (f : Pub → Pp × S → Bool) : Pub → Pp × S → Bool :=
  fun q a =>
    match q with
    | .more seg name =>
      if seg.isNone && name == "K13.pileMasks" then pileMasksC a.2
      else if seg.isNone && name == "K13.pileWithin" then pileWithinC a.2
      else if seg.isNone && name == "K13.oneRow" then oneRowC a.2
      else f (.more seg name) a
    | q => f q a

section
variable {Pp : Type} (f : Pub → Pp × S → Bool)

theorem pubK13PlusC_pileMasks (a : Pp × S) :
    pubK13PlusC f (.more none "K13.pileMasks") a = pileMasksC a.2 := rfl
theorem pubK13PlusC_pileWithin (a : Pp × S) :
    pubK13PlusC f (.more none "K13.pileWithin") a = pileWithinC a.2 := rfl
theorem pubK13PlusC_oneRow (a : Pp × S) :
    pubK13PlusC f (.more none "K13.oneRow") a = oneRowC a.2 := rfl

/-- Every other item is handed on. -/
theorem pubK13PlusC_else (q : Pub) (h : k13PlusItemC q = false) (a : Pp × S) :
    pubK13PlusC f q a = f q a := by
  cases q with
  | more seg name =>
    have h' : (seg.isNone && (name == "K13.pileMasks" || name == "K13.pileWithin" ||
      name == "K13.oneRow")) = false := h
    have h2 : (seg.isNone && name == "K13.pileMasks") = false := by
      cases hs : seg.isNone <;> simp_all
    have h3 : (seg.isNone && name == "K13.pileWithin") = false := by
      cases hs : seg.isNone <;> simp_all
    have h4 : (seg.isNone && name == "K13.oneRow") = false := by
      cases hs : seg.isNone <;> simp_all
    show (if seg.isNone && name == "K13.pileMasks" then _
      else if seg.isNone && name == "K13.pileWithin" then _
      else if seg.isNone && name == "K13.oneRow" then _ else _) = _
    rw [h2, h3, h4]
    rfl
  | _ => rfl

end

end VerifiableInference.Desc.K13
