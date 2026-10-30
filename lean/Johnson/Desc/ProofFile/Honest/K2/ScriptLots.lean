-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/ScriptLots.lean: the kind "the code switch" (K2) in the frame for
the honest side: THE TEXTS OF THE KIND's LOTS FOR A LAYING OF THE THREADS' SCRIPT (`MsgLot`,
`PadLot`, Honest/Thread/ScriptLots.lean): of all a run's coins, the input and the challenges, in the
types that the laying by lots asks. DEFINITIONS WITH CODE ALONE: NINE; NO THEOREM. Nothing is laid
here; no statement is made of these texts.

  `switchRowsLaid`    the switch's messages in full, by number in the order of sending, at what the
                      part is handed
  `handed`            what the frame's `lendPart` hands the part off a run's coins; nothing where it
                      refuses
  `switchMsgTxt`      message number n, entry by entry, into Option
  `switchPadTxt`      the pad's own component: at the library's `padB`'s places alone
  `firstSender`       whether the switch is message n's first sender
  `switchMsgLots`     one lot for each message of which it is
  `switchPadLots`     one lot for each tenant of the switch's tree
  `maskOrOneAnswer`   A PUBLIC TEST: each message of the place has a mask row or just one answer
  `numsApart`         A PUBLIC TEST: the place's lots of messages bear different numbers

THE LETTERS. ch: the chain's number; meant: the first chain's, 0. num: message n's number in the
witness. tree, tenant: the switch's tree, and message n's part in it. fx: how many challenges stand
in front of the member. NOTHING HERE TIES A LETTER TO WHAT IT IS MEANT TO BE.

WHOSE CONVENTIONS. Those of the shared sending's lots (Honest/K1/ScriptAt.lean, ScriptLots.lean, of
other authors): rows are read into a witness's message by THEIR `rowsMsg`, called here; a message's
text answers at every entry or at none; a pad's text at `padB`'s places alone; the lot's number is
the witness's own. Their `lentCut` is called for the part's own cut.

THE MAKE. `switchRowsLaid` WRITES ONCE MORE WHAT THE SWITCH's PART SENDS IN ITS FIRST ROUND: it is
the first move's own lines (`switchPart`, Honest/K2/Part.lean) with the sender's `tables` unfolded
one step at `coreSender freshTable` (Honest/K2/Sending.lean): `rowsAll`, of which that sender makes
the switch's table. ITS TIE TO ITS FIRST: `says_of_rows`, `table_of_rows`
(Honest/K2/Law/RowsTie.lean): equations without a hypothesis. No law on the switch's part speaks of
this text in the part's stead.

WHERE THIS KIND IS NOT THE SHARED SENDING. (i) `switchMsgTxt` READS MORE OF THE RUN THAN THE PART's
OWN CUT: the part is handed its own stretch AND THE STRETCHES THAT IT CARRIES, whose counts stand at
other senders' addresses (`SwitchPlace.carries`); the carrying message's main rows are made of the
closing over these. THAT A CARRIED STRETCH IS THE RUN OF ITS OWNER's CUT THAT THE BOOK's ENTRY
NAMES, BY START AND COUNT, IS SHOWN NOWHERE HERE. `switchPadTxt` reads the own cut alone. (ii) THE
ROWS ARE AN `Except`: `switchMsgTxt` ANSWERS NOTHING, AT ALL ENTRIES, where the frame's lending
refuses (at the own address or a carried one), where a public test of the part says no, where a
message's stretch does not fit, OR WHERE THE CLOSING REFUSES. THAT THIS HANGS ON PUBLIC DATA ALONE
IS NOT SHOWN IN THIS FILE: it is shown, at the lot's own closing `lotClosingAt` under the public
test `closingOk`, by `msgTxt_isSome` and `msgTxt_public` (Honest/K2/Law/LotsAnswer.lean), and for
the pad's text by `padTxt_isSome` and `padTxt_public` there. (iii) A kept copy gets no lot of
messages: by the library's `Wit.tab` (Johnson/Desc/Sound/MsgSig.lean) all copies share the message's
number. (iv) `switchPadTxt` lays zeros for the data: it is meant under `maskOrOneAnswer` alone: at a
message with no mask row and no answer the pad's list is empty, and `messageRows` reads the data at
`padB`'s places. (v) The two texts come to the part's own cut differently: `lendPart` asks that the
part takes JUST the book's count, `lentCut` that the book's count covers it: the pad's text may
answer where the message's answers nothing. (vi) The closing finds a fold's challenges by their
numbers among the chain's rounds from 0: that fits a thread with no round in front of the chain
alone: a law that opens the closing's text is to ask that; a law that hands these texts on whole
need not. (vii) `switchWit` reads the input: the input holds the committer's coins: what `switchWit`
reads of the committer's pads and tails is DATA here, never a coin.

Limits. NO LOT IS LAID HERE. Nothing in this file holds these texts against any Script, any table or
any other lot. That two lots of one place bear different numbers is a test here (`numsApart`), shown
here at no place. num n is meant to be the witness's number at the seat (tree, tenant n): NO LAW IN
THIS FILE SAYS THAT THE SPENDERS' LOTS BEAR THAT NUMBER. `maskOrOneAnswer` is shown here at no
place. Where two lots answer at one entry and do not agree, the laying's first wins, and nothing
marks it. Where no lot answers the laying lays 0: whoever quotes, at a book, a law over what is laid
from these texts names beside it that the part gets from that book its own cut and every stretch
that it carries. The part spends nothing (`spends := []`). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchMoves
import Johnson.Desc.ProofFile.Honest.K2.AtPlan
import Johnson.Desc.ProofFile.Honest.K1.ScriptAt
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc (padB)
open VerifiableInference.Desc.K2.Honest (zeroG)
open ProofFile.Honest.FirstThread (MsgLot PadLot)
open Law (SwitchCoins)

variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- **The switch's messages in full**, by number in the order of sending: of what the part is
handed, the input and the challenges in front of the part. The own cut c.1 goes to `rowsAll` as this
sending's coins. THE CARRIED STRETCHES c.2.2 GO THROUGH THE CLOSING INTO THE MAIN ROWS, AS DATA: so
a coin that an earlier sender laid as a tail or in a pad stands again, as data, in the carrying
message. -/
def switchRowsLaid (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing)
    (p : SwitchPlace) (c : SwitchCoins p.sizes p.others p.foldVars p.carries)
    (w : Local W₀ Rc Xi Tr) (h : List Fmt.Drawn) :
    Except String (Nat → Johnson.Prover.Send.Rows) :=
  if !p.sizes.serves then .error "the switch's rest does not lie in main rows" else
  if !p.sizes.roomy then .error "the sizes do not fit a switch" else
  (switchRowsAt p.sizes p.carries c.2.2 ⟨switchWit D readers closing p w, h, ()⟩ 0).bind fun M =>
    rowsAll freshTable p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) M c.1

/-- **What the frame hands the part** off a run's coins, at the chain number ch; nothing where
`lendPart` refuses. -/
def handed (ch : Nat) (p : SwitchPlace) (k : Coins Bk) :
    Option (SwitchCoins p.sizes p.others p.foldVars p.carries) :=
  (lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨p.place, 0⟩
    (switchPart (coreSender freshTable) p.sizes p.others p.foldVars p.carries)).toOption

/-- **Message number n, entry by entry**: nothing where the part is handed nothing, or the rows
refuse. -/
def switchMsgTxt (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (n : Nat) :
    Coins Bk → Local W₀ Rc Xi Tr → List Fmt.Drawn → Bool → Nat → Nat → Option Cb.Gl.E :=
  fun k w h mask r j =>
    (handed ch p k).bind fun c =>
      (switchRowsLaid D readers closing p c w h).toOption.map fun V =>
        K1.rowsMsg ((switchSent p.sizes p.others).getD n default).shape (V n) mask r j

/-- **The pad's own component**: at `padB`'s places alone: the same rows at data of zeros, off the
part's own cut. -/
def switchPadTxt (ch : Nat) (p : SwitchPlace) (n : Nat) :
    Coins Bk → Bool → Nat → Nat → Option Cb.Gl.E :=
  fun k mask r j =>
    if padB p.sizes.codes ((switchSent p.sizes p.others).getD n default).shape mask r j then
      (K1.lentCut k ch ⟨p.place, 0⟩ (sendingDue p.sizes.codes (switchSent p.sizes p.others)
        (switchFresh p.sizes p.others p.foldVars))).bind fun c₁ =>
        (rowsAll freshTable p.sizes.codes (switchSent p.sizes p.others)
          (switchFresh p.sizes p.others p.foldVars) (fun _ _ _ => zeroG) c₁).toOption.map fun V =>
          K1.rowsMsg ((switchSent p.sizes p.others).getD n default).shape (V n) mask r j
    else none

/-- **Whether the switch is message n's first sender**: the carrying message, and all behind the
kept copies. (The order of sending: the target's message, the target's kept copies, the others.) -/
def firstSender (p : SwitchPlace) (n : Nat) : Bool :=
  n == 0 || decide (p.sizes.target.kept.size < n)

/-- **The lots of messages**: one for each message of which the switch is the first sender. -/
def switchMsgLots (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (num : Nat → Nat) (fx : Nat) :
    List (MsgLot Bk (Local W₀ Rc Xi Tr)) :=
  ((List.range (switchSent p.sizes p.others).size).filter (firstSender p)).map fun n =>
    ⟨num n, fx, switchMsgTxt ch D readers closing p n⟩

/-- **The lots of pads**: one for each tenant of the switch's tree. -/
def switchPadLots (ch : Nat) (p : SwitchPlace) (tree : Nat) (tenant : Nat → Nat) :
    List (PadLot Bk (Local W₀ Rc Xi Tr)) :=
  (List.range (switchSent p.sizes p.others).size).map fun n =>
    ⟨tree, tenant n, fun k _ => switchPadTxt ch p n k⟩

/-- **A PUBLIC TEST**: each message of the place has a mask row or just one answer. -/
def maskOrOneAnswer (p : SwitchPlace) : Bool :=
  (switchSent p.sizes p.others).toList.all fun x =>
    x.shape.maskRows != 0 || x.shape.answers == 1

/-- **A PUBLIC TEST**: the place's lots of messages bear different numbers. -/
def numsApart (p : SwitchPlace) (num : Nat → Nat) : Bool :=
  decide (((List.range (switchSent p.sizes p.others).size).filter (firstSender p)).map num).Nodup

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.switchRowsLaid
#print axioms ProofFile.Honest.K2.handed
#print axioms ProofFile.Honest.K2.switchMsgTxt
#print axioms ProofFile.Honest.K2.switchPadTxt
#print axioms ProofFile.Honest.K2.firstSender
#print axioms ProofFile.Honest.K2.switchMsgLots
#print axioms ProofFile.Honest.K2.switchPadLots
#print axioms ProofFile.Honest.K2.maskOrOneAnswer
#print axioms ProofFile.Honest.K2.numsApart
