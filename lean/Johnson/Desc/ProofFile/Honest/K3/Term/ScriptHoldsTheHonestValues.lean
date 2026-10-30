-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AT ANY SCRIPT.
Johnson/Desc/ProofFile/Honest/K3/Term/ScriptHoldsTheHonestValues.lean: the honest side of the kind
"lookup" (K3): FOUR NAMED PREMISES, on the `Script` and on the trace, from which the lookup's own
readings of the witness are the trace's values. Definitions alone.

Why. The lookup's items speak of a witness through four readings (`digNu`, `attNu`, `layNu`,
`headNu`, Johnson/Desc/First/Look/K3…GoodIn.lean). On the honest side the witness is
`Script.wit Q k w heard` (Honest/Thread/First.lean). This file lays no `Script`, and the
messages that these readings read are sent by other kinds (the opening, the switch, the job
"digits"). So what the lookup needs of the `Script` is named here, general in the `Script`; what it
needs of the trace is named beside it.

WHO PAYS. The first and the third speak through the lookup's OWN reader of the witness: they are no
asks to another file: THEY ARE THE ENDS OF LEMMAS OF THIS FOLDER, from the frame's sentence on
`Script.msg` alone, public facts under the library's head, and laws of the trace
(Term/PackedTraceCellsFromLaysFilling.lean; Term/DigitArraysFromTheDigitsFilling.lean). The second is the
trace's. The fourth is an equation on the `Script`'s field `cells`.
THE VALUES AT WHICH THEY ARE WANTED, under the head h : `P5J.AtMgA …`: D := h.𝔇.sent · Lk := h.𝔇.l3 ·
(x, tl) := what `attAt` | `layAt` with `tlAt` | `headAt` | `digAt` answer at the link · valid := the
thread's · challengesHeard := a number at most the challenges heard behind the lookup's border ·
traceMatrices := fun w => `traceMatricesOfTheCells` X (the input's cells) link
(Term/TraceMatricesOfTheCells.lean) · digitsOfTheTrace := fun w heard => `zzOwn` X link (the input's
cells) (`tritsAt` heard ‹the sampling round›) · weightEntry := the index's entries.

  `ScriptHoldsThePackedTraceCells`   ON THE SCRIPT, at one link's calls: every committed symbol of the
                                     link's list of matrices is the packing of the trace's integers
  `TraceCellsAreSmall`               ON THE TRACE ALONE: these integers are below twice the shift
  `ScriptHoldsTheDigitArrays`        ON THE SCRIPT, at one link's digits: the entries of the arrays
                                     BZ and ZZ are the counts' bits and the digits
  `ScriptCellsAreTheIndexWeights`    ON THE SCRIPT, its stored table: the weights' entries

The guards are those of `OwnMsgs` (Honest/Thread/ScriptLots.lean): only inputs at which `valid` holds
and lists of at least `challengesHeard` challenges are spoken of. At a `valid` that holds of no input,
or where no list is that long, each premise asks nothing.

Every premise on the `Script` is stated through the library's own reading of the witness's tables
(`msgsOf`, Johnson/Desc/Sound/MsgSig.lean): whether a seat lies on a pad or off it, and which number
the message has in the witness, is not asked and not told.

Limits. Definitions: forms of hypotheses. SHOWN HERE OF NO SCRIPT OR TRACE. Not
tried for emptiness by Lean: that the four can hold together at the full size is argued by reading
alone. Across links: a matrix that a link borrows bears its first sender's message, so the first
premise at the borrower's link and at the owner's link ask one entry for two values: they can hold
together only where `traceMatrices` answers the same under both (a law of the trace, on the seams
between links; not shown here). Nothing on any property.
-/
import Johnson.Desc.First.Look.K3FillWorth
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.Desc.ProofFile.Honest.K3.WitFill
import Johnson.HonestTrace.CountsDigits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First.Look (Sent sigListCalls seatCalls symAt szOf enOf)
open VerifiableInference.OnPublicFiles (K3Letters attMs digMu)
open OnBytes.HonestTrace (LaidBZ)
open ProofFile.Honest.FirstThread (Script)

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

variable {Bk : ProverCoinCounts} {W Cells Tok : Type} (Q : Script Bk W Cells Tok MsgT) (D : Sent)
  (Lk : K3Letters Cells Tok)

/-- **THE FIRST PREMISE: ON THE SCRIPT, at the calls of one link.** Asked of whoever lays the
`Script`'s messages of link `x.link` and of the links from which it borrows.

`traceMatrices w`: the trace's integer matrices of that link (number in the link's list of matrices,
row, column). `tl`: the plan's record of the link's smallness test, whose sizes are `szOf tl`.

What it asks. At every run's coins `k`, every input `w` at which `valid` holds and every list `heard`
of at least `challengesHeard` challenges: for every matrix `matrix` of the list, every column `column`
and every row of symbols `symbolRow`, the committed symbol that the lookup's caller reads off the
witness's messages (`symAt`, at the messages that stand sent when the shift of the lookup on the
link's calls is drawn) is the packing (`Alg.pack`, three rows of one column in one element, at the
sizes' radix) of that column of `traceMatrices w`, cast into the field.

Where it asks nothing. Of rows and columns outside the sizes; of the mask row; of the stored table;
of inputs and lists outside the guards. IT DOES NOT SAY THAT THE INTEGERS ARE SMALL: that is
`TraceCellsAreSmall`. `symAt` is 0 where the reading of a seat fails: so where a symbol has no seat
in the list, the premise asks the packing there to be 0.

How it is meant to be paid (by reading; this file does not do it). The senders' sentence is `OwnMsgs` at each
own message of moment 0 of a link: the `Script`'s message holds, at the place that the layout's rule
gives entry (`symbolRow`, `column`) of the symbol array of matrix number `matrix`, the value
`OnBytes.HonestTrace.packedCells` of the filling's sizes and the trace's cells at (link, `matrix`,
`symbolRow`, `column`); the frame's own sentence for it is `LaysFilling`, with `msg_of_lays`
(Honest/K5/Law/LaysFilling.lean). From there three steps lead here. (i) ON PUBLIC DATA: the symbol's
address has a seat in the list `sigListCalls`, the seat lies in its message's main rows and off the
pad, and the member's number `Lk.arr (Lk.seat x.link false member)` is the message's number in the
witness (`SymsRoom` and `val_sym`, Honest/K5/Law/CellsQRaw.lean; `seat_number_head`,
Honest/K5/Law/SeatNumber.lean, for attention's links). (ii) `pack3_eq_pack`
(Johnson/HonestTrace/Packed.lean): `packedCells` is `Alg.pack` at the radix 2 ^ 20, which is
`(szOf tl).rad`; the cast goes through the packing (`Alg.pack_intCast`). (iii) ON PUBLIC DATA: the
filling's sizes of the matrix are `szOf tl`'s. `traceMatrices w` is the trace at the link BY THE LINK's
OWN LIST, a borrowed matrix under the borrower's number. -/
def ScriptHoldsThePackedTraceCells (valid : W → Prop) (challengesHeard : Nat) (x : PlaceL)
    (tl : HTailF2) (traceMatrices : W → OnBytes.Road.Mats ℤ) : Prop :=
  ∀ (k : Coins Bk) (w : W) (heard : List Fmt.Drawn), valid w → challengesHeard ≤ heard.length →
    ∀ (matrix : Fin (szOf tl).NM) (column : Fin ((szOf tl).k matrix))
      (symbolRow : Fin (Alg.symRows ((szOf tl).m matrix))),
      symAt D.codes (sigListCalls D Lk.rad x.link) (seatCalls D x.link) tl
          (attMs x D Lk.rad (fun j => Lk.seat x.link false j.1) Lk.arr (Q.wit k w heard))
          matrix symbolRow column =
        ((Alg.pack (((szOf tl).rad : Nat) : ℤ)
          (fun row : Fin ((szOf tl).m matrix) => traceMatrices w matrix.val row.val column.val)
          symbolRow : ℤ) : Cb.Gl.E)

/-- **THE SECOND PREMISE: ON THE TRACE ALONE.** Asked of whoever has the trace's laws. No `Script`,
no coin and no challenge stands in it.

What it asks. At every input at which `valid` holds, every entry of `traceMatrices w` within the sizes
of the link's smallness test is, in absolute value, below twice the sizes' shift: the library's own
bound for the packing to have one unpacking (`Cb.Pv.Tail.BaseAt`'s first clause), not the format's
bound on a cell.

Where it asks nothing. Of rows, columns and matrices outside the sizes. -/
def TraceCellsAreSmall (valid : W → Prop) (tl : HTailF2)
    (traceMatrices : W → OnBytes.Road.Mats ℤ) : Prop :=
  ∀ w, valid w → ∀ (matrix : Fin (szOf tl).NM) (column : Fin ((szOf tl).k matrix))
    (row : Fin ((szOf tl).m matrix)),
    |traceMatrices w matrix.val row.val column.val| < 2 * (((szOf tl).beta : Nat) : ℤ)

/-- **THE THIRD PREMISE: ON THE SCRIPT, at the digits of one link.** Asked of whoever lays the
`Script`'s message that holds the link's arrays ZZ and BZ.

`digitsOfTheTrace w heard`: the array ZZ (combination, column), over the base field. It takes the
challenges, since the combinations are made with drawn values: so `challengesHeard` is meant to reach
behind the round that draws them. IT IS HANDED THE WHOLE LIST `heard`, while the witness's message
number n is read at `heard.take (Q.fixedMsg n)`: so the premise can hold only of a function that
reads no challenge from `Q.fixedMsg n` on (at the value meant: one round's trits alone).

Where it asks nothing. Of entries outside BZ's 32 rows and `tl.bzColumns` columns and outside ZZ's
`tl.tau` rows and `2 * tl.mz` columns; of the mask row; of inputs and lists outside the guards. The
entries are read by the digits' caller's own reading `digMu`, which is 0 at an address that the
link's arrays do not have: there the premise asks the value to be 0. -/
structure ScriptHoldsTheDigitArrays (valid : W → Prop) (challengesHeard : Nat) (x : PlaceL)
    (tl : HTailF2) (digitsOfTheTrace : W → List Fmt.Drawn → ℕ → ℕ → Cb.Gl.F) : Prop where
  /-- the entries of BZ are the bits of the counts of these digits: the library's own form `LaidBZ`
  (Johnson/HonestTrace/CountsDigits.lean) -/
  countsBits : ∀ (k : Coins Bk) (w : W) (heard : List Fmt.Drawn), valid w →
    challengesHeard ≤ heard.length →
    LaidBZ tl (inExt (digitsOfTheTrace w heard)) fun row column =>
      digMu x D Lk.rad (fun j => Lk.seat x.link true j.1) Lk.arr (Q.wit k w heard)
        (enOf x.arrays (tl.ix.BZ, row, column))
  /-- the entries of ZZ are these digits -/
  digits : ∀ (k : Coins Bk) (w : W) (heard : List Fmt.Drawn), valid w →
    challengesHeard ≤ heard.length → ∀ combination column, combination < tl.tau →
    column < 2 * tl.mz →
      digMu x D Lk.rad (fun j => Lk.seat x.link true j.1) Lk.arr (Q.wit k w heard)
        (enOf x.arrays (tl.ix.ZZ, combination, column)) =
        inExt (digitsOfTheTrace w heard) combination column

/-- **THE FOURTH PREMISE: ON THE SCRIPT's STORED TABLE.** Asked of whoever lays the `Script`'s field
`cells`. It is the one place where the lookup reads that field: at the letters of the composed
meaning (`k3StoredAt`, Johnson/Desc/First/Look/K3LettersAt.lean) `Lk.msgW` reads the witness's cells
alone, and `Lk.wOf` is their entry inside their shape and 0 outside.

What it asks. At the guards: the stored table's entry (row, column), as the letters read it off the
witness, is `weightEntry w`'s, taken into the extension field, AT EVERY ROW AND COLUMN: so where the
letters' reader is 0 outside a shape, `weightEntry w` must be 0 there. At those letters neither the
coins nor the challenges are read (`Script.wit`'s cells are `Q.cells w`): there the guard on `heard` is
idle. -/
def ScriptCellsAreTheIndexWeights (valid : W → Prop) (challengesHeard : Nat)
    (weightEntry : W → ℕ → ℕ → Cb.Gl.F) : Prop :=
  ∀ (k : Coins Bk) (w : W) (heard : List Fmt.Drawn), valid w → challengesHeard ≤ heard.length →
    ∀ row column,
      Lk.wOf (Lk.msgW (Q.wit k w heard)) row column =
        algebraMap Cb.Gl.F Cb.Gl.E (weightEntry w row column)

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.ScriptHoldsThePackedTraceCells
#print axioms ProofFile.Honest.K3.Term.TraceCellsAreSmall
#print axioms ProofFile.Honest.K3.Term.ScriptHoldsTheDigitArrays
#print axioms ProofFile.Honest.K3.Term.ScriptCellsAreTheIndexWeights
