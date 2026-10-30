-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/SeatedL.lean: the kind "the code switch" (K2): THE RECORD AT A
SWITCH: what the kind's shares of "the exchange" (`ExchangeAtS`, Honest/Thread/SharesS.lean) are to
spend of the first chain's letters (`Letters`, Honest/Thread/First.lean) at a member of the kind:
THE NAMED PREMISES, IN ONE STRUCTURE. One abbreviation and one structure. NOTHING IS PROVED IN THIS
FILE, and it is none of the library's goals.

AFTER THE FORM OF the shared sending's record `K1Seated` (Honest/K1/Seated.lean, of other authors):
the fields on the letters' own (seats · ans · numbered · sits · rowM · firstNo · treesNo · port ·
books) are its fields, with the switch's own sending (`switchPar`) for the job's plan. That record
itself does not fit a switch: its field `half` asks the shared sending's half. `K2Seated`
(Honest/K2/Seated.lean), at a thread as a variable, has no field on the witness.

  `switchPar` a short name: the switch's own sending as the shared sending's public letter:
                    `sendingPar` (Honest/K2/Sending.lean) at the place's codes and messages
  `K2SeatedL` THE RECORD. A: on the member and the letters · B: public tests and equations · D: THE
                    TIE of the Script's messages and pads to the kind's own texts · J: the joint in
                    front

CAN IT BE MET? NOTHING HERE SHOWS IT, OF ANY FIELD. What is known of roads, by reading, none taken
here: `sends` IS `IsSend`'s SENTENCE (Johnson/Desc/K1/Law/GoodSend3.lean) AT THE SECOND ROUND CUT TO
THE SENDING's ANSWERS (`cutTo`, Johnson/Desc/K1/Law/SendP4.lean), NOT AT THE ROUND ITSELF: the
sending's decision refuses where an answer is left over, and the library's own law for the sending
inside a switch stands at the cut round (`decide_of_sendP`, SendP5.lean); a yes of the kind's
decision holds a yes of that sending (`yes_sendP`, Johnson/Top/H0/Tw/K2C/SendsOpen.lean). Between
these and the field lie: the place's own steps `before` and `after` · that the step behind the
sending keeps each message's shape, mark and sample rows (`yes_keeps`, K2C/Keeps.lean, asks that of
the relation) · that the library's letter there and `switchPar` are one to the sending's decision.
The field leaves the type Lt and the start d to whoever pays it. `msgs` ASKS THE TEXT OFF THE PAD's
PLACES ALONE, AND NOT THE WHOLE TEXT: a kept copy has the witness's number of its original (`keyOf`,
`arrOf`, Johnson/P5T/PlanSeats.lean), and at the pad's places it holds the later switch's own coins,
not the original's (`messageRows`, Honest/K2/Sending.lean): so at a place that has a kept copy with
a pad the whole text's tie would ask two coins of the book to be one (argued). The witness's table
reads the Script's message off the pad alone (`tab_rows_off`, Honest/K2/Law/TabRowsOff.lean), and
the library's one accessor is made so: `Wit.tab` (Johnson/Desc/Sound/MsgSig.lean), in its own words:
"`w.msg n` at a pad's place and `w.pad j t` outside the pad's places are pinned by nothing." At a
first sender the weaker tie follows from the whole text's (`ownMsgs_off`, the same file). AT A KEPT
COPY it asks the Script for THIS switch's text at a number at which an earlier sender's lot is laid:
that the two texts are one there, off the pad, is a law apart, not typed. `trees` has a law at
numbers that the library's maker returned (`place_shapes`, Honest/K2/Law/PlaysAtPlan.lean).
`seedsNo` and `nonZeroNo` are the two equations of `seeds_at_numbers`
(Honest/K2/Law/SeedsOfDraw.lean); `seeds_of_rule` and `seeds_of_nums` there say from what they
follow. `noWord` has a law under the opening, at each place of the plan (`noWord_open`,
Honest/K2/Law/SampledOpen.lean). `carryM` fixes the item "carry" as the sentence on the witness
`carryExact` (Johnson/Desc/K2/Honest/Carry/Exact.lean).

Limits. Every premise is a premise: none is shown at any letters. No toy member is typed: THAT THE
FIELDS CAN HOLD TOGETHER IS SHOWN NOWHERE. `sends` and `books` are asked at the thread's own states
in front of the member (`Thr`, Honest/Thread/Thr.lean). That the two fields can be paid in this form
is shown by nothing yet. `before`, `after`, `first`, `rad`, `arr`, `seats₀`, `ms` are letters. `rad`
is tied to no member's radius. The closing is the lot's own (`lotClosingAt`, Honest/K2/Exact.lean),
at a layout and segments that are letters. Nothing on the pins of the kept messages. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K1.Seated
import Johnson.Desc.ProofFile.Honest.K2.MsgOff
import Johnson.Desc.ProofFile.Honest.K2.Exact
import Johnson.Desc.ProofFile.Honest.K2.Law.Plays
import Johnson.Desc.K2.Honest.Carry.Exact
import Johnson.Desc.K1.Law.SendP4
import Johnson.Top.H0.Tw.K2C.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S Numbers Item rowSays wordsAtFirst)
open VerifiableInference.Desc.First.K2 (P2 decideWith)
open VerifiableInference.Desc.Sound (MsgT Mem SitsAt smpNamed)
open VerifiableInference.Desc.K2.Honest (carryExact)
open ProofFile.Honest.FirstThread (Letters OwnMsgs OwnPads)
open ProofFile.Honest.K1 (seatAtMember)
open Johnson.Prover.Send (shapeAt)
open _root_.Desc.Plain (DState)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}

/-- The switch's own sending as the shared sending's public letter. -/
abbrev switchPar (p : SwitchPlace) : VerifiableInference.Desc.K1.Par :=
  sendingPar p.sizes.codes (switchSent p.sizes p.others)

/-- **THE RECORD.** L: the letters. b, blk: the member's number; the member. D, readers: the half's
letters. lay, segs: the layout and the segments' public data, as the lot's closing takes them. p:
the place's public data. q: the place's numbers, as the kind's block takes them. before, after: what
the place's block lays in front of and behind the kind's own decision. seg: the segment into which
the switch leads; behind the last segment the number of segments. first: the number, in the
statement, of the sending's first message. Zp: the public parameters, as the exact carry takes them.
arr, seats₀, ms, rad: as in the shared sending's record. A definition: premises' forms. Nothing here
proves that it can be met. FREE LETTERS: D · readers · rad · before · after; and, inside `sends`,
the type Lt and the states d, d'. `readers` TAKES THE WHOLE INPUT. `closes` AND `publicAt` TOGETHER
GIVE, AT EVERY VALID INPUT, EVERY LIST OF CHALLENGES AND ALL CARRIED COINS, THAT THE LOT's CLOSING
RETURNS (`returnsLaw`, Honest/K2/Law/SegmentAlike.lean): the premise hl of `half_played_rows`
(Honest/K2/Law/PlayedOfRows.lean). NOT IN FRONT OF A LAW OVER COINS. -/
structure K2SeatedL (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT) (b : Nat)
    (blk : Block S Cl) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub) (p : SwitchPlace) (q : P2)
    (before : S → Except String S) (after : S → S → Except String S) (seg first : Nat)
    (Zp : ProofFile.Pub) (arr : ℕ → ℕ → ℕ) (seats₀ : List (ℕ × ℕ)) (ms : List Mem)
    (rad : ℕ → ℕ) : Prop where
  /-- A: the chain's member number b is blk -/
  member : L.bs[b]? = some blk
  /-- A: and the list of places has the switch's place there -/
  placeAt : L.ps[b]? = some p.place
  /-- A: the member's place, rounds and oracle messages are the kind's at the place's numbers -/
  shape : blk.place = p.place ∧ blk.rounds = First.K2.rounds q ∧ blk.oracles = [q.sent, []]
  /-- A: the half that stands at the place is the kind's one lot's -/
  half : (L.hs.find? fun g => g.place == p.place) =
    some (switchHalf (coreSender freshTable) D readers (lotClosingAt lay segs) p)
  /-- A: the member's decision: `before`, the kind's own, `after`: both ways -/
  decides : ∀ s rs gs t, rs.length = 2 → gs.length = q.read.length →
    (blk.decide s rs gs = .ok t ↔ ∃ s₁ m, before s = .ok s₁ ∧
      decideWith _root_.Tw.K2.sendByL8 q s₁ rs gs = .ok m ∧ after s₁ m = .ok t)
  /-- A: AT A STATE OF THE THREAD IN FRONT OF THE MEMBER (`Thr`, Honest/Thread/Thr.lean): the kind's
  decision takes what it sends off the state, so the sentence is asked at such states alone. A yes
  of the member holds a yes of the shared sending's decision AT THE SECOND ROUND CUT TO THE
  SENDING's ANSWERS, and leaves the messages' number, shapes, marks and sample rows. The type
  Lt, the states d and d', owed and ids stand under "there are": NOTHING TIES THE START d TO s -/
  sends : ∀ k s m E s' r₁ r₂ gs, Thr L.thread b k s m E → blk.decide s [r₁, r₂] gs = .ok s' →
    ∃ (Lt : Type) (d d' : DState Lt) (owed : Option Nat) (ids : Array Nat),
      K1.decideSend (switchPar p) owed d [r₁, K1.cutTo (switchPar p) r₂] = .ok (ids, d') ∧
        K1.SameMsgs d'.st s'.st ∧ s'.st.oracles.size = d'.st.oracles.size
  /-- A: and, at such a state, does to the verifier's book what a sending does -/
  books : ∀ k s m E s' r₁ r₂ gs, Thr L.thread b k s m E → blk.decide s [r₁, r₂] gs = .ok s' →
    K1.Booked (switchPar p) s.book s.st.oracles.size s'.book s'.st.oracles.size
  /-- B: the public tests on the place under which the half plays (Honest/K2/Law/Plays.lean);
  `placeFits`: the switch's own sending passes the shared sending's public test -/
  serves : p.sizes.serves = true
  roomy : p.sizes.roomy = true
  placeOk : placeFits p = true
  closes : closingOk freshTable (segs.take p.link) p = true
  /-- B: and the test on the filling, at the public instance of each valid input -/
  publicAt : ∀ w, L.valid w → publicOk D lay p (segs.take p.link) w.x = true
  /-- B: every message of the sending with a main row is sampled -/
  noWord : NoWord (switchSent p.sizes p.others)
  /-- B: the oracle messages that the place's numbers state beneath the first round's roots have the
  lengths and widths of the sending's trees -/
  trees : q.sent.map (fun o => (o.logLength, o.words)) =
    Law.treeShapes p.sizes.codes (switchSent p.sizes p.others)
  /-- B: the sending has as many answers as the place's numbers state -/
  answersNo : (switchPar p).answers = q.answers
  /-- B: the first round draws as many elements as the sending's seeds want: each seed its
  coordinates and one factor -/
  seedsNo : q.seeds = (switchPar p).seeds * ((switchPar p).coordinates + 1)
  /-- B: and as many of them are drawn non-zero as there are seeds -/
  nonZeroNo : q.nonZero = (switchPar p).seeds
  /-- B: THE NUMBER: the table's numbers count `first` oracle messages of the STATEMENT in front of
  the place -/
  firstNo : L.N.msgsAt (some p.place) = first
  /-- B: THE TREES: the chain's own blocks state as many trees in front of the member as the table's
  numbers count in front of the place -/
  treesNo : treesTo L.bs b = L.N.treesAt (some p.place)
  /-- B: the library's condition on the sending and the radii, as one Bool -/
  port : K1.condPort (switchPar p) rad = true
  /-- D: **the tie**: the Script's message at the WITNESS's number of each of the sending's
  messages, THE KEPT COPIES INCLUDED, is the kind's own text OFF THE PAD's PLACES (`switchMsgOff`,
  Honest/K2/MsgOff.lean) wherever that answers: at the thread's valid inputs, at lists of challenges
  no shorter than the rounds in front of the member. THE TEXT IS A FUNCTION OF THE RUN's COINS AND
  OF THE WHOLE INPUT: an equation at every k -/
  msgs : ∀ n, n < (switchPar p).sent.size →
    OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs b)
      (arr (seatAtMember L.bs b (switchPar p) n).1
        (seatAtMember L.bs b (switchPar p) n).2)
      (L.thread.front + roundsTo L.bs b) (switchMsgOff 0 D readers (lotClosingAt lay segs) p n)
  /-- D: the Script's pad at the seat of each of the sending's messages is the kind's own text
  wherever that answers. THE TEXT IS A FUNCTION OF THE RUN's COINS ALONE: an equation at every k -/
  pads : ∀ n, n < (switchPar p).sent.size →
    OwnPads L.Q L.valid (seatAtMember L.bs b (switchPar p) n).1
      (seatAtMember L.bs b (switchPar p) n).2
      (fun k _ => switchPadTxt 0 p n k)
  /-- A: the seats that the table's numbers pin at this member ("pin seg 0") are just the seats of
  the sending's sampled messages -/
  seats : ∀ x, x ∈ L.N.sent seg 0 ↔ ∃ n, n < (switchPar p).sent.size ∧
    (shapeAt (switchPar p) n).answers ≠ 0 ∧ x = seatAtMember L.bs b (switchPar p) n
  /-- A: a pin says at the threads what Honest/Thread/Ans.lean says -/
  ans : L.ans = ansJT (switchPar p).codes arr (smpNamed (switchPar p).codes seats₀) ms
  /-- A: the seat of each sampled message stands in that list, at the message's number in the
  STATEMENT -/
  numbered : ∀ n, n < (switchPar p).sent.size → (shapeAt (switchPar p) n).answers ≠ 0 →
    seatAtMember L.bs b (switchPar p) n ∈ seats₀ ∧
      seats₀.idxOf (seatAtMember L.bs b (switchPar p) n) = first + n
  /-- A: at that seat some member of ms sits, and every member that sits there has the message's
  shape -/
  sits : ∀ n, n < (switchPar p).sent.size → (shapeAt (switchPar p) n).answers ≠ 0 →
    (∃ x ∈ ms, SitsAt x (seatAtMember L.bs b (switchPar p) n).1
      (seatAtMember L.bs b (switchPar p) n).2) ∧
    ∀ x ∈ ms, SitsAt x (seatAtMember L.bs b (switchPar p) n).1
        (seatAtMember L.bs b (switchPar p) n).2 →
      (x.1.l.get x.2).1 = shapeAt (switchPar p) n
  /-- A: "row m c" says: every row of the class says its claim of the witness's words -/
  rowM : ∀ w, (L.Mg w).row = rowSays L.N (wordsAtFirst arr)
  /-- J: the switch leads into a later segment -/
  later : 1 ≤ seg
  /-- J: the claim that the closed segment hands on is open in front -/
  asks : Item.carry (seg - 1) ∈ L.thread.opened b
  /-- J: and says the exact carry: a sentence on the witness -/
  carryM : ∀ w, (L.Mg w).carry = carryExact Zp arr

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.switchPar
#print axioms ProofFile.Honest.K2.K2SeatedL
