-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SendingsVia.lean: the honest side of the two sendings of the
batch's shared rounds, "send o_u" and "send o_omega", as CALLS of the shared sending's own part
(sendPart, Johnson/Desc/ProofFile/Honest/K1/Part.lean). This file holds definitions only; no theorem
is stated.

What a caller says of its sending: the sending's parameters; the number that its first new message
gets; which of its tables is laid of fewer coins than it has entries; and its data: for a message, a
row and a place either a value, or nothing, where the entry comes from the coins. All else (the
order of the coins, the tables, the columns, the out-of-domain (OOD) answers) is the shared part's.

  ViaPub      the public data: the shared chain's own parameters; the number, among the chain's
              rounds, of "LIN point"; the number that o_u gets
  viaPad      a place of the pad of a message without a mask row: the last places of its last main
              row, as many as it has OOD answers
  vectorData  the data of a message whose main table carries a vector v: nothing at a place of the
              pad, beyond the rows and beyond the code's message length; elsewhere v's entry at the
              number that the vector's layout gives the place (entryAt), WHATEVER v HOLDS THERE.
              That it is 0 at a place that the vector leaves free is no property of vectorData: the
              two vectors laid here are 0 from their lengths on, because uHonE and omegaHonE return
              zeroE there (Johnson/Desc/K14/Honest/Coded.lean)
  viaPoint, pointReady   the shared point, off the challenges in front of a part; a test with code
              on a list of challenges: one stands at the number atPoint and holds kCol elements
  viaU        "send o_u": o_u carries the folded row (uAtE, Johnson/Desc/K14/Honest/Coded.lean); the
              first mask of the proximity test on G_u is a fold's fresh table (Ride)
  viaOmega    "send o_omega": o_omega carries omega_col (omegaAtE); every entry of o_sp is a coin
  viaHalves   the two halves, lifted to the shared chain's type parameters

What the parts read. As Honest/K14/Sendings.lean's: of the input the committed table's rows before
encoding; of the challenges psi_sh, by its number among the chain's rounds, and the sending's own
OOD seeds. No witness, no instance, no key.

The shared part returns an error in both moves where the job does not fit its place (sendFits,
Johnson/Desc/ProofFile/Honest/K1/Coins.lean: a test with code on public data): so do these two.

Limits. The fold's numbers k and h are read off the first stage of the proximity test on G_u in the
shape; that k is the number of that fold's rounds is held by nothing here. Typed for messages whose
main rows are over the extension field. viaPoint makes the point of whatever stands at the number
atPoint, and of nothing where nothing stands there, without a word: pointReady is the test for it;
among the files that stand in the library with this one none calls pointReady or viaHalves, so
there nothing asks that test.
MET BY A DEFAULT VALUE IN SILENCE. (1) viaPad and vectorData read the code by
`codes.base.getD s.code default`: at a code's number beyond the array it is the default code.
(2) viaU and viaOmega read what goes out with o_u by `(Desc.K14.withU A.P.S).getD #[]`: where the
library returns nothing there (Johnson/Desc/K14/Text.lean; OnBytes/Iop/Lin.lean, linWithU: masks are
sent ahead and the test on G_u has no stage), "send o_u" is a sending of NO message, not of o_u
either, and o_omega gets the number A.first. (3) viaU's ride at the message number 1 is
`A.P.S.testU.head?.map …`: where the test on G_u has no stage it is none, so a message number 1
would be laid as any table of coins; by the same two texts the sending has no message number 1
there. (4) In both calls the data is `if k == 0 then … else none`: every message but the first has
no data, so all its entries come from the coins.
That these parts lay what Honest/K14/Sendings.lean's parts lay: the tables' entries, the pads, the
tails and the counts have lemmas (Honest/K14/SendingsViaRows.lean, SendingsViaHolds.lean,
SendingsViaCounts.lean), and so have the OOD answers at the sampled messages and the play
(SendingsViaAnswers.lean, SendingsViaShows.lean, SendingsViaPaid.lean). THE COLUMNS AND SYMBOLS AT
THE TWO CALLS viaU AND viaOmega ARE HELD BY NO LEMMA AND BY NO EVALUATION IN THIS LIBRARY. What is
shown of columns is general in the job: where the two texts' rows agree, read (RowsAgree,
Honest/K14/TieDefs.lean), they lay the same columns and the same tables (column_tie, sentTables_tie,
Honest/K14/TieColumns.lean); and the rows agree at every job of Sendings.lean's form that passes
sendShapeFits, at the data vecData, which calls this file's vectorData (rows_tie,
Honest/K14/TieRows.lean). No statement says that viaU's or viaOmega's data is vecData at jobU or
jobOmega. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K1.Part
import Johnson.Desc.ProofFile.Honest.K14.Parts
import Johnson.Desc.K14.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (E Codes OracleShape vectorLay)
open OnBytes.Slice (toE)
open ProofFile.Honest.K1 (Ride sendPart)

variable {W₀ Rc Ky X : Type}

/-- **The public data of the two calls.** -/
structure ViaPub where
  P : Desc.K14.P14
  /-- the number, from 0, among the shared chain's rounds, of "LIN point" -/
  atPoint : Nat
  /-- the number that o_u gets among the statement's messages -/
  first : Nat

/-- The place j of the row r is a place of the pad of a message without a mask row. The code is
`codes.base.getD s.code default`: the default code at a number beyond the array. -/
def viaPad (codes : Codes) (s : OracleShape) (r j : Nat) : Bool :=
  s.maskRows == 0 && r + 1 == s.mainRows &&
    decide ((codes.base.getD s.code default).ell - s.answers ≤ j) &&
    decide (j < (codes.base.getD s.code default).ell)

/-- **The data of a message whose main table carries the vector v**: none at a place of the pad,
beyond the rows and beyond the code's message length; elsewhere v's entry, as an element of the
extension field, at the number that the vector's layout gives the index of (row r, place j),
whatever v holds there. The code is read with the same default as in viaPad. -/
def vectorData (codes : Codes) (s : OracleShape) (high : Bool) (v : Nat → E) (r j : Nat) :
    Option (Cb.Gl.F ⊕ Cb.Gl.E) :=
  if viaPad codes s r j || decide (s.mainRows ≤ r) ||
      decide ((codes.base.getD s.code default).ell ≤ j) then none
  else some (.inr (toE (v ((vectorLay codes s high).entryAt
    (r + j * 2 ^ (vectorLay codes s high).rowBits))).triple))

/-- The shared point, off the challenges in front of a part: the elements of the challenge at the
number atPoint; the empty list, without a word, where none stands there. -/
def viaPoint (A : ViaPub) (fr : Front Unit) : List E := elems ((fr.heard.drop A.atPoint).take 1)

/-- A challenge stands at the number atPoint, and holds kCol elements. -/
def pointReady (A : ViaPub) (hs : List Fmt.Drawn) : Bool :=
  (hs[A.atPoint]?).any fun d => d.elems.length == A.P.S.kCol

/-- **"send o_u".** Three silent moves. Where `withU` returns nothing the sending has NO message
(`getD #[]`). The ride at the message number 1 is read off the first stage of the test on G_u, and
is none where that test has no stage. The message number 0 carries the folded row; every other
message has no data, so all its entries come from the coins. -/
def viaU (A : ViaPub) : ProofFile.Honest.K1.SendJob Ask Unit :=
  { P := Desc.K14.parK1 A.P 2 "o_u and the first mask" ((Desc.K14.withU A.P.S).getD #[])
    first := A.first
    ride := fun k => if k == 1 then A.P.S.testU.head?.map fun s => { k := s.k, h := s.h } else none
    data := fun w fr k r j =>
      if k == 0 then vectorData A.P.codes A.P.S.fold.u A.P.S.fold.rowsHigh
        (Desc.K14.Honest.uAtE A.P.S (viaPoint A fr) w.rows) r j
      else none }

/-- **"send o_omega".** Its first message gets the number A.first plus the number of messages of
"send o_u", which is 0 where `withU` returns nothing (`getD #[]`). No table rides. The message
number 0 carries omega_col; every other message has no data, so all its entries come from the
coins. -/
def viaOmega (A : ViaPub) : ProofFile.Honest.K1.SendJob Ask Unit :=
  { P := Desc.K14.parK1 A.P 5 "o_omega and o_sp" (Desc.K14.withOmega A.P.S)
    first := A.first + ((Desc.K14.withU A.P.S).getD #[]).size
    ride := fun _ => none
    data := fun w fr k r j =>
      if k == 0 then vectorData A.P.codes A.P.S.omega A.P.S.omegaRowsHigh
        (Desc.K14.Honest.omegaAtE A.P.S (viaPoint A fr) w.rows) r j
      else none }

/-- **The two halves**, lifted. weights, rand: the two readers. -/
def viaHalves (A : ViaPub) (weights : W₀ → Weights) (rand : Rc → TableRand) :
    List (Placed Empty (Common W₀ Rc Ky) X) :=
  let lifted (p : Part Empty Ask Unit) : Part Empty (Common W₀ Rc Ky) X :=
    p.lift (fun v => v) (fun c => ⟨rowsOf A.P.S (weights c.w₀) (rand c.rc)⟩) (fun _ => ())
      fun x _ => x
  [⟨(viaU A).P.place, [lifted (sendPart (viaU A))]⟩,
   ⟨(viaOmega A).P.place, [lifted (sendPart (viaOmega A))]⟩]

end ProofFile.Honest.K14
