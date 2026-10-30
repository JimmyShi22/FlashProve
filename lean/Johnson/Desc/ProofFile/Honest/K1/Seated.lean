-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Seated.lean: THE SHARED "SENDING" (the kind K1) AT A MEMBER OF THE
FIRST CHAIN: THE RECORD OF NAMED PREMISES ON THE CHAIN's LETTERS: every fact on the letters of the
first chain's thread (Honest/Thread/First.lean: Letters) that the kind K1's laws on "it plays" and
on the kind's share of "the exchange" (PlaysS, ExchangeAtS: Honest/Thread/PaysS.lean, SharesS.lean)
are to spend at such a member. Definitions alone: an inductive type, three functions, one structure
of propositions. IT PROVES NOTHING AND CLOSES NOTHING.

  K1Sort         the four sorts of member: the opening, a segment's reads, its digits, W's sending
  pinsAtSort     the seats (tree, tenant) that the table's items pin at a member
  classOf        the segment and the moment whose class of sample rows the member opens
  seatAtMember   the seat of the job's message number n: the library's own seatOfMsg
  K1Seated       THE RECORD: twenty fields, in three classes

THE CLASSES. A: ON THE LETTERS, no run in them: EQUATIONS, to be paid by unfolding where the letters
are laid: member, placeAt, shape, half, ans, numbered, sits, rowM; AND TWO LAWS ON THE MEMBER's OWN
DECISION, to be paid by lemmas: isSend, books. B: PUBLIC, no run in them: fits, oneAns, hasCoins,
firstNo, treesNo, port (each decidable) and heardOnly (a sentence on the job's data). D: THE
SCRIPT's TIES, which speak of a run's coins: msgs, pads (in the forms OwnMsgs and OwnPads of
Honest/Thread/ScriptLots.lean, at the texts msgTxt and padTxt of Honest/K1/ScriptLots.lean); and
seats, in which no run stands: it holds the seats that the table's numbers pin against the seats of
the job's sampled messages. There is no premise "from the thread in front to the state": the number
of the statement's messages follows from the thread's own form and firstNo.

TWO NUMBERS OF ONE MESSAGE. J.first + n is the message's number in the STATEMENT, kept copies and
all: firstNo and numbered speak of it. The WITNESS is read at arr (seat), one number for all copies
(msgsOf, Johnson/Desc/Sound/MsgSig.lean): msgs speaks of that.

THE TWO FENCES OF OwnMsgs AND OwnPads ARE NAILED: the inputs are the thread's own valid ones (valid
reads the input: it is not public by type); the lists are at least as long as the text's own bound,
the rounds in front of the member. At a fence that holds of no input both forms ask nothing.

hasCoins. At a book whose count at the part's address is short the two texts answer nothing, and
every Script meets msgs and pads. SO: a law that concludes that a step is met, or that the two texts
answer, spends hasCoins by name; a law under "Stepped" has the cut from the frame, and says in its
head that it holds of nothing at a book that does not cover the count.

Limits. NOTHING HERE PROVES THAT THE RECORD CAN BE MET: no letters are given here at which the
twenty fields hold together, and none at which the thread then holds of a run (the twenty fields
together, at each of the kind's 52 members, under the library's head, a return of onlineProverFromPublicFiles and a
premise on the other senders' lots: k1Seated_at_base, AtFullSide/K1/RecordAtBase.lean, which does
not say that the thread holds at any run). Nothing is said on the tables that are sent: they are no
field here. It is said nowhere here that a default is never read; that a pad is fresh, uniform or
used once; that the tie is met; that one answer holds at any real plan; that what the witness holds
is what is shown. At W's sending the data are another file's letter: nothing here calls its entries
coins. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ScriptLots
import Johnson.Desc.ProofFile.Honest.Thread.Ans
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob
import Johnson.Desc.ProofFile.Honest.K1.ScriptLots
import Johnson.Desc.K1.Law.WordsAtPlace
import Johnson.Desc.K1.Law.GoodSend3
import Johnson.Desc.First.Close.Law.FillRowFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S Numbers rowSays wordsAtFirst)
open VerifiableInference.Desc.Sound (MsgT Mem SitsAt smpNamed)
open ProofFile.Honest.FirstThread (Letters OwnMsgs OwnPads)
open Johnson.Prover.Send (shapeAt)

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X P Cells Tok : Type}

/-- The four sorts of member. -/
inductive K1Sort where
  | opening
  | reads (m : Nat)
  | digits (m : Nat)
  | w

/-- The seats (tree, tenant) that the table's items pin at a member, off the table's numbers
(Item.holds, Johnson/Desc/First/Borders.lean: pin m t, pinI, pinV). -/
def pinsAtSort (N : Numbers) : K1Sort → List (Nat × Nat)
  | .opening => N.sent 0 0 ++ [N.index]
  | .reads m => N.sent m 1
  | .digits m => N.sent m 2
  | .w => [N.w]

/-- The segment and the moment whose class of sample rows the member opens ("row m (sample t)",
Johnson/Desc/First/Borders.lean); none at W's sending. -/
def classOf : K1Sort → Option (ℕ × ℕ)
  | .opening => some (0, 0)
  | .reads m => some (m, 1)
  | .digits m => some (m, 2)
  | .w => none

/-- **The seat (tree, tenant) of the job's message number n at the member number b**: the library's
own seatOfMsg (Johnson/Desc/K1/Law/WordsAtPlace.lean) behind as many trees as the chain's blocks in
front state: where the verifier's book seats a sending's messages (Booked.place,
Johnson/Desc/K1/Law/BookAtRecord.lean). -/
def seatAtMember (bs : List (Block S Cl)) (b : Nat) (P : K1.Par) (n : Nat) : Nat × Nat :=
  K1.seatOfMsg P (treesTo bs b) n

/-- **THE RECORD: what the kind K1's laws spend of the first chain's letters at a member of the kind
K1.** L: the letters. b: the member's number. blk: the member. wit: the reader of the place's input.
J: the job. own₀: any value of X: under heardOnly nothing of it is read. sort: which of the table's
rows stands here: seats alone reads it. arr: the witness's number of the message at a seat. seats₀,
ms: the letters of the pin's text: the list of seats by which the reader of samples numbers the
statement's messages; the members. rad: A FREE LETTER: the radius of the place's message number n:
port alone reads it. A definition: premises' forms. Nothing here proves that it can be met. -/
structure K1Seated (L : Letters Bk Cl W₀ Rc Xi Tr X P Cells Tok MsgT) (b : Nat)
    (blk : Block S Cl) (wit : Local W₀ Rc Xi Tr → PlaceIn Xi) (J : SendJob (PlaceIn Xi) X)
    (own₀ : X) (sort : K1Sort) (arr : ℕ → ℕ → ℕ) (seats₀ : List (ℕ × ℕ))
    (ms : List Mem) (rad : ℕ → ℕ) : Prop where
  /-- A: the chain's member number b is blk -/
  member : L.bs[b]? = some blk
  /-- A: and the list of places has the job's place there -/
  placeAt : L.ps[b]? = some J.P.place
  /-- A: the member's place, rounds and oracle messages are the job's plan's. At a joined member
  (the opening; W) this is asked of the whole member: the joined half has no round -/
  shape : blk.place = J.P.place ∧ blk.rounds = K1.rounds J.P ∧ blk.oracles = K1.oracles J.P
  /-- A: the half that stands at the place is the kind K1's: placeHalf wit J -/
  half : (L.hs.find? fun g => g.place == J.P.place) = some (placeHalf wit J)
  /-- A: a yes of the member holds a yes of the kind's own decision at the job's plan, and leaves
  the messages' number, shapes, marks and sample rows (IsSend,
  Johnson/Desc/K1/Law/GoodSend3.lean) -/
  isSend : K1.IsSend J.P (fun s : S => s.st) blk
  /-- A: and does to the verifier's book what a sending does (Booked,
  Johnson/Desc/K1/Law/BookAtRecord.lean) -/
  books : ∀ s s' r₁ r₂ gs, blk.decide s [r₁, r₂] gs = .ok s' →
    K1.Booked J.P s.book s.st.oracles.size s'.book s'.st.oracles.size
  /-- B: the public test on the plan and the riding tables -/
  fits : sendFits J.P J.ride = true
  /-- B: of what stands in front the job's data read what was heard alone -/
  heardOnly : ∀ w fr fr', fr.heard = fr'.heard → J.data w fr = J.data w fr'
  /-- B: each message of the plan has at most one answer: a test with code: the library's test on a
  pad's place is "at one answer" (padB, Johnson/Desc/SeatAt.lean). AT THE SAMPLED MESSAGES
  port SAYS IT TOO: under port each sampled message has one answer (cond_tie,
  Johnson/Desc/K1/Law/Port6.lean); of a message that is not sampled cond_tie says nothing -/
  oneAns : answersAtMostOne J.P = true
  /-- B: THE PUBLIC COUNT: the book's count at the part's address in the first chain is the part's:
  what lendPart itself asks (Honest/Frame.lean) -/
  hasCoins : dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride
  /-- B: THE NUMBER: the table's numbers count J.first oracle messages of the STATEMENT in front of
  the place -/
  firstNo : L.N.msgsAt (some J.P.place) = J.first
  /-- B: THE TREES: the chain's own blocks state as many trees in front of the member as the table's
  numbers count in front of the place -/
  treesNo : treesTo L.bs b = L.N.treesAt (some J.P.place)
  /-- B: the library's condition on the plan and the radii, as one Bool (condPort,
  Johnson/Desc/K1/Law/Port6.lean). rad is tied to no member's radius: the field is to be spent for
  Tie, SeedIs and the codes' lengths, none of which names a radius -/
  port : K1.condPort J.P rad = true
  /-- D, COINS: **the tie**: the Script's message at the WITNESS's number of each of the job's
  messages is K1's lot's text (msgTxt) wherever that answers: AT THE THREAD's VALID INPUTS, AT LISTS
  OF CHALLENGES NO SHORTER THAN THE ROUNDS IN FRONT OF THE MEMBER -/
  msgs : ∀ n, n < J.P.sent.size →
    OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs b)
      (arr (seatAtMember L.bs b J.P n).1 (seatAtMember L.bs b J.P n).2)
      (L.thread.front + roundsTo L.bs b) (msgTxt 0 wit J own₀ n)
  /-- D, COINS: the Script's pad at the seat of each of the job's messages is K1's lot's text
  (padTxt) wherever that answers, which is at padB's places alone: AT THE THREAD's VALID INPUTS -/
  pads : ∀ n, n < J.P.sent.size →
    OwnPads L.Q L.valid (seatAtMember L.bs b J.P n).1 (seatAtMember L.bs b J.P n).2
      (fun k _ => padTxt 0 J n k)
  /-- D: the seats that the table's numbers pin at this member are just the seats of the job's
  sampled messages -/
  seats : ∀ x, x ∈ pinsAtSort L.N sort ↔ ∃ n, n < J.P.sent.size ∧
    (shapeAt J.P n).answers ≠ 0 ∧ x = seatAtMember L.bs b J.P n
  /-- A: a pin says at the threads what Honest/Thread/Ans.lean says, at the library's reader of
  samples by a list of seats (smpNamed, Johnson/Desc/Sound/SmpNamed.lean), at the plan's codes -/
  ans : L.ans = ansJT J.P.codes arr (smpNamed J.P.codes seats₀) ms
  /-- A: the seat of each sampled message of the job stands in that list, at the message's number in
  the STATEMENT -/
  numbered : ∀ n, n < J.P.sent.size → (shapeAt J.P n).answers ≠ 0 →
    seatAtMember L.bs b J.P n ∈ seats₀ ∧
      seats₀.idxOf (seatAtMember L.bs b J.P n) = J.first + n
  /-- A: at that seat some member of ms sits, and every member that sits there has the job's shape.
  The member's radius stays free -/
  sits : ∀ n, n < J.P.sent.size → (shapeAt J.P n).answers ≠ 0 →
    (∃ x ∈ ms, SitsAt x (seatAtMember L.bs b J.P n).1 (seatAtMember L.bs b J.P n).2) ∧
    ∀ x ∈ ms, SitsAt x (seatAtMember L.bs b J.P n).1 (seatAtMember L.bs b J.P n).2 →
      (x.1.l.get x.2).1 = shapeAt J.P n
  /-- A: "row m c" says: every row of the class says its claim of the witness's words -/
  rowM : ∀ w, (L.Mg w).row = rowSays L.N (wordsAtFirst arr)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.pinsAtSort
#print axioms ProofFile.Honest.K1.classOf
#print axioms ProofFile.Honest.K1.seatAtMember
#print axioms ProofFile.Honest.K1.K1Seated
#print axioms ProofFile.Honest.K1.K1Sort
