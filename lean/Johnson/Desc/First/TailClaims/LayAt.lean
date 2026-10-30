-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/LayAt.lean: THE SMALLNESS TEST's ENTRIES, READ OFF MESSAGES: which place of which
row of which message an entry of a lay is; the entries off the file's one witness and off the messages of a
sending's signature; and the one law that ties the two.

For the letters that Johnson/Desc/First/K8/LawLay.lean leaves free (J, Y, entE, entW, hE): entE, entW and hE
are TRADED for one function seat (or: layout, num, own, copy, maskSeat) and one premise on the plan. Definitions,
statements and proofs. NOTHING IS TYPED AGAIN THAT OTHER FILES HOLD: where an element of a link's array
lies in its oracle message is seatIn (Johnson/Desc/LaidAt.lean); the witness, its messages and the
signature's messages off it are Wit (Johnson/Desc/Msg.lean), MsgT and msgsOf
(Johnson/Desc/Sound/MsgSig.lean); the signature is sigOf (Johnson/Pack/PortF.lean); a lay, its addresses
and its reading of a cell are Lay, Addr, Lay.cellAt, Lay.cellAt_addr (OnBytes/Tie/Pv/Led/).
Main names:
  Seat: a copy of a message (its shape; the message's number in the witness; the tree and the tenant that hold the
    copy); mask row or main row; the row; the place: ALL THAT THE WITNESS's ONE ACCESSOR Wit.tab IS HANDED.
  seatOf layout num own copy maskSeat: the seat of an address: of a cell (t, r, c) through own t (which link
    owns array number t of the ledger's list, under which name: LinkCtx.arrayOf), seatIn, and copy (a message's
    number ↦ the shape, tree and tenant of a copy of it: a letter); of a slot's mask entry by the letter maskSeat.
  entW cs seat Y w: the entries off the witness: w.tab at the entry's seat (MsgSig.lean: «whoever reads a message
    off a witness reads it through this»); 0 where it has none.
  placeOf: the seat at which a member of the signature holds one of its places (msgsOf's own rule).
  entE seat Y M: the entries off the signature's messages: M at a member's place that has the entry's
    seat; 0 where there is none.
  msgsOf_place: msgsOf at a member's place is the witness's message at placeOf.
  **InSig**, **hE_of_inSig**: where every early entry that has a seat has it at a place of a member, the
    two readings agree on the early entries: LawLay.lean's hE to the letter.
  cell_is_place: the lay's cell (t, r, c), read off the witness, IS place q of main row p of the copy (s, n, tr, te),
    through Wit.tab, where J has that cell and its seat is that. cell_is_laid: the same at seatOf: where seatIn,
    at the link and name that own t gives, says (n, p, q).
Over Johnson/Desc/Msg.lean | Johnson/Desc/Sound/MsgSig.lean (a witness has a component pad for each
copy; msgsOf reads through Wit.tab).
Limits. STILL LETTERS: layout, num, own, copy, maskSeat; cs, l, seat', arr; J, Y. InSig is a premise on the plan's
letters alone; no test with code for it is typed here and nothing has ridden. hE_of_inSig IS TRUE BY THE MAKE
OF entE, AT EVERY seat WITH InSig, A WRONG ONE TOO: entE looks up a member's place that has the entry's seat;
that seat is the layout's (seatOf at LinkCtx.arrayOf and the plan's num) is asked by no theorem but
cell_is_laid, which speaks of the witness's side alone. InSig holds idly where no early entry has a seat, and
at a J without an early address. It may be false at a real plan: a cell of an array that another sending
holds, or of a message without a sample, has no place in this signature unless l takes these members in.
entE takes A place with the seat (by choice): at M = msgsOf w the law does not care which; at another M,
where two members have one shape and one seat (tree, tenant), entE reads an unnamed one of them. Of an entry that is not early InSig asks
nothing: entW reads the witness at its seat, inside or outside every member's ranges; NOR DOES ANYTHING ASK ITS COPY
(shape, tree, tenant; that the copy holds that number): a wrong shape moves the pad's places, and entW then reads what
no pin fixes (Wit.tab's own warning). InSig asks an early entry's seat to be a member's place IN ALL SEVEN COMPONENTS:
so copy must name just the copy that the signature's member holds. At a pad's place atSeat reads the copy's pad:
whether a cell of a link's array can sit there is not looked at (LaidAt.lean's Limits: reqLayoutOk, «miss the
sample's pad»). Nothing says
that the witness's messages are what was committed (words_are_committed's row).

-/
import Johnson.Desc.Sound.MsgSig
import Johnson.Desc.LaidAt
import OnBytes.Tie.Pv.Led.LedLay
import OnBytes.Tie.Pv.Tail.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.First.TailClaims.Law
open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Road.Rows Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open OnBytes.Tie.Pv.Tail (early)

/-- A copy's shape; the message's number in the witness; the copy's tree and tenant; mask row (true) or main row;
the row; the place. -/
abbrev Seat : Type := OnBytes.OracleShape × ℕ × ℕ × ℕ × Bool × ℕ × ℕ

/-- The seat of an address. -/
def seatOf (layout : OnBytes.Params.ReqLayout) (num : ℕ → ℕ → ℕ) (own : ℕ → ℕ × String)
    (copy : ℕ → OnBytes.OracleShape × ℕ × ℕ) (maskSeat : ℕ → Option Seat) : Addr → Option Seat
  | .cell t r c => (seatIn layout num (own t).1 (own t).2 r c).map fun x =>
      ((copy x.1).1, x.1, (copy x.1).2.1, (copy x.1).2.2, false, x.2.1, x.2.2)
  | .mask s => maskSeat s

section
variable {J : Type} (cs : OnBytes.Codes) (seat : Addr → Option Seat) (Y : Lay J)

/-- The witness at a seat: through its one accessor. -/
def atSeat {Cells Tok : Type} (w : Wit Cells Tok MsgT) (a : Seat) : GE :=
  w.tab cs a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1 a.2.2.2.2.2.2

/-- The entries off the file's one witness. -/
def entW {Cells Tok : Type} (w : Wit Cells Tok MsgT) (j : J) : GE :=
  match seat (Y.addr j) with
  | some a => atSeat cs w a
  | none => 0

variable (l : List (OnBytes.OracleShape × ℕ)) (seat' : Fin l.length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)

/-- The seat at which member i of the signature holds its place x: msgsOf's own rule. -/
def placeOf (i : Fin l.length) : ((sigOf cs l).om i).C.J → Seat
  | .inl q => ((l.get i).1, arr (seat' i).1 (seat' i).2, (seat' i).1, (seat' i).2, false, q.1.val, q.2.val)
  | .inr q => ((l.get i).1, arr (seat' i).1 (seat' i).2, (seat' i).1, (seat' i).2, true, q.1.val, q.2.val)

/-- msgsOf at a member's place is the witness's message at that place's seat. -/
theorem msgsOf_place {Cells Tok : Type} (w : Wit Cells Tok MsgT) (i : Fin l.length)
    (x : ((sigOf cs l).om i).C.J) :
    msgsOf cs l seat' arr w i x = atSeat cs w (placeOf cs l seat' arr i x) := by
  cases x <;> rfl

open Classical in
/-- The entries off the messages of the signature. -/
def entE (M : (sigOf cs l).Msg) (j : J) : GE :=
  match seat (Y.addr j) with
  | some a =>
    if h : ∃ p : (i : Fin l.length) × ((sigOf cs l).om i).C.J, placeOf cs l seat' arr p.1 p.2 = a then
      M (Classical.choose h).1 (Classical.choose h).2
    else 0
  | none => 0

/-- Every early entry that has a seat has it at a place of a member of the signature. -/
def InSig (tl0 : HTailF2) : Prop :=
  ∀ j a, early tl0 (Y.addr j) = true → seat (Y.addr j) = some a →
    ∃ p : (i : Fin l.length) × ((sigOf cs l).om i).C.J, placeOf cs l seat' arr p.1 p.2 = a

/-- **The one law**: on the early entries the two readings agree. -/
theorem hE_of_inSig {Cells Tok : Type} (tl0 : HTailF2) (hin : InSig cs seat Y l seat' arr tl0) :
    ∀ (w : Wit Cells Tok MsgT) (j : J), early tl0 (Y.addr j) = true →
      entE cs seat Y l seat' arr (msgsOf cs l seat' arr w) j = entW cs seat Y w j := by
  intro w j he
  unfold entE entW
  cases hs : seat (Y.addr j) with
  | none => rfl
  | some a =>
    have h := hin j a he hs
    simp only [dif_pos h]
    rw [msgsOf_place, Classical.choose_spec h]

end

/-- **An entry (row, column) of an array is a place of a row of a message.** -/
theorem cell_is_place {J : Type} [Fintype J] (cs : OnBytes.Codes) (seat : Addr → Option Seat) (Y : Lay J)
    {Cells Tok : Type} (w : Wit Cells Tok MsgT) (t r c : ℕ) (j : J) (hj : Y.addr j = .cell t r c)
    (s : OnBytes.OracleShape) (n tr te p q : ℕ) (hs : seat (.cell t r c) = some (s, n, tr, te, false, p, q)) :
    Y.cellAt (entW cs seat Y w) t r c = w.tab cs s n tr te false p q := by
  rw [Lay.cellAt_addr _ _ t r c j hj]
  unfold entW
  rw [hj, hs]
  rfl

/-- **The same at the layout's own seats.** -/
theorem cell_is_laid {J : Type} [Fintype J] (cs : OnBytes.Codes) (layout : OnBytes.Params.ReqLayout)
    (num : ℕ → ℕ → ℕ) (own : ℕ → ℕ × String) (copy : ℕ → OnBytes.OracleShape × ℕ × ℕ)
    (maskSeat : ℕ → Option Seat) (Y : Lay J) {Cells Tok : Type}
    (w : Wit Cells Tok MsgT) (t r c : ℕ) (j : J) (hj : Y.addr j = .cell t r c) (n p q : ℕ)
    (hs : seatIn layout num (own t).1 (own t).2 r c = some (n, p, q)) :
    Y.cellAt (entW cs (seatOf layout num own copy maskSeat) Y w) t r c =
      w.tab cs (copy n).1 n (copy n).2.1 (copy n).2.2 false p q :=
  cell_is_place cs _ Y w t r c j hj _ n _ _ p q (by
    show (seatIn layout num (own t).1 (own t).2 r c).map _ = _
    rw [hs]
    rfl)

end VerifiableInference.Desc.First.TailClaims.Law

#print axioms VerifiableInference.Desc.First.TailClaims.Law.msgsOf_place
#print axioms VerifiableInference.Desc.First.TailClaims.Law.cell_is_laid
#print axioms VerifiableInference.Desc.First.TailClaims.Law.hE_of_inSig
#print axioms VerifiableInference.Desc.First.TailClaims.Law.cell_is_place
