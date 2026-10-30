-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtKey/LotOwnWords.lean: THE WORDS AT THE KEY FILE's OWN TEST, AS A TERM: the
family of words that an honest key prover holds at the three members of the own group, IN THE NUMBERING OF THE OWN
TEST's STATEMENT (the first chain's messages, and behind them Omega's copy). Definitions alone, and what the tie of
these words to the job's rows asks, each under its name.

  `OwnTestNumbers`        six public numbers: where the two sendings' messages and Omega's copy stand in the
                          statement; how many challenges stand in front of each sending; the first chain's count
  `ownCoinsOfSending`     what a sending of the first chain is lent as its own: its purse, cut from 0 by its count
  `frontBeforeSending`    the front at which the words read a sending's data: the challenges in front of it alone
  `rowsOfSending`         K1's own rows (`rowsR`) at these two
  `wordsOfOmegaAtKey`     the shared chain's honest words (`words2` at `holds2`) at that chain's number 2
  `wordsAtKeyOwnTest`     THE TERM: K1's `held` at the two sendings; at the copy's number Omega's
  `SendersReadInFront`    WHAT THE TIE ASKS OF THE PARTS: a sending's data reads of the front none but the challenges
                          in front of the sending; "LIN point" is the shared chain's round 0
  `carriesMessage`        the public test on the book for a carried message of a sending of the kind K1
  `BookAtOwnTest`         WHAT THE TIE ASKS OF THE BOOK, all public: in the form of `member_held` (AtProof/HandedW.lean)
  `SharedPlanAtOwnTest`   WHAT THE TIE ASKS OF THE SHARED CHAIN's PLAN, all public
  `StatementAtOwnTest`    WHAT THE TIE ASKS OF THE STATE ON ENTRY, all public: members, shapes, codes
  `HeardAtOwnTest`        WHAT THE TIE ASKS OF THE CHALLENGES: the test's front and the witness's list agree where
                          the three senders read, and the point has its length

Why a term of its own. The last thread's meaning at the key (`lettersLastKey`, E2E/KeyLastThread.lean) is
`mgWords ℓ`, which reads `ℓ.get` at the SHARED chain's numbers (0 o_u, 2 o_omega, 3 o_sp); the own test's statement
is the FIRST chain's last statement with Omega's copy behind it (0 the index masks, the last but one W, then the
copy). One family cannot be read by both numberings at number 0. So the words are typed here in the statement's
numbering, and what a thread's witness owes is an equation to this term on the members' tables.

Limits.
- DEFINITIONS. No thread's witness is shown to be this term. No book, state or parts are shown to meet the three
  structures; each can be false.
- Where a sender's purse does not cover its count `ownCoinsOfSending` is the default purse: `BookAtOwnTest` rules it out.
- Off the three stretches of numbers the term is 0.
- Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.KeyFourTests
import Johnson.Desc.ProofFile.Honest.K14.Holds2
import Johnson.Desc.ProofFile.Honest.K12.NearAtHead
import Johnson.Desc.ProofFile.Honest.K12.SaysOfMet
import Johnson.Desc.ProofFile.Honest.K12.CutOfBook
import Johnson.Desc.ProofFile.Honest.K12.AtFile.OTie
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HandedW

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.AtKey
open OnBytes (Statement Group Oracle)
open OnBytes.Means (Words)
open OnBytes.Slice (GE)
open Johnson.Prover.Send (shapeAt)
open VerifiableInference.Desc (Place)
open AtPublicFiles.KeyFile (KeyParts In1 In2 randK14)
open AtPublicFiles.KeyTest (sIdx sW)
open ProofFile.Honest.K12.Light (sentOf cutFits)
open ProofFile.Honest.K12.AtFile (ellOmegaB)

/-- **The public numbers that the words at the own test read.** -/
structure OwnTestNumbers where
  /-- the number, in the own test's statement, of the first message of the index masks' sending -/
  indexMasksFirst : ℕ
  /-- the number there of the first message of W's sending -/
  vectorWFirst : ℕ
  /-- the number there of Omega's copy -/
  omegaCopy : ℕ
  /-- how many challenges of the first chain stand in front of the index masks' sending -/
  challengesBeforeIndexMasks : ℕ
  /-- how many stand in front of W's sending -/
  challengesBeforeVectorW : ℕ
  /-- how many challenges the first chain has -/
  challengesOfFirstChain : ℕ

variable {Bk : ProverCoinCounts} {W₀ Rc X₀ X Wk Wd : Type}

/-- **What a sending of the first chain is lent as its own**: its purse, cut from 0 by its count, as `lendPart`
cuts it. The default purse where the cut fails. -/
def ownCoinsOfSending (k : Coins Bk) (address : Addr) (J : K1.SendJob Wd X) :
    Cs (K1.dueR J.P J.ride) :=
  ((k.look 0 address).2.cut ⟨0, 0⟩ (K1.dueR J.P J.ride)).getD default

/-- The front at which the words read a sending's data: of what was heard the challenges in front of the sending;
the state that the parts pass on at a given value; nothing shown. -/
def frontBeforeSending (own : X) (heard : List Fmt.Drawn) (challengesInFront : ℕ) : Front X :=
  { heard := heard.take challengesInFront, own := own }

/-- **A sending's rows, as its sender makes them.** -/
def rowsOfSending (k : Coins Bk) (address : Addr) (J : K1.SendJob Wd X) (input : Wd) (own : X)
    (heard : List Fmt.Drawn) (challengesInFront : ℕ) : ℕ → Johnson.Prover.Send.Rows :=
  K1.rowsR J.P J.ride (J.data input (frontBeforeSending own heard challengesInFront))
    (ownCoinsOfSending k address J)

/-- What the shared chain's sides are handed of the own test's input. -/
def commonOfInput (input : In1 W₀ Rc) : In2 W₀ Rc := ⟨input.w₀, input.rc, input.x.key⟩

/-- **Omega's two tables**: the shared chain's honest words at that chain's number 2, at the holdings `holds2`, at
the first challenge behind the first chain's. -/
def wordsOfOmegaAtKey (K : KeyParts W₀ Rc X₀ X Wk) (N : OwnTestNumbers) (k : Coins Bk)
    (input : In1 W₀ Rc) (heard : List Fmt.Drawn) : OnBytes.Part → ℕ → GE :=
  Desc.K14.Honest.words2 K.send.P (sentOf K.send.P.S) (Desc.K14.first K.send.P.codes input.x.key)
    (K14.firstRv (heard.drop N.challengesOfFirstChain))
    (K14.holds2 K.send.P K.weights (fun c => randK14 (K.rand c)) k (commonOfInput input)) 2

/-- **THE WORDS AT THE KEY FILE's OWN TEST**, in the numbering of that test's statement. -/
def wordsAtKeyOwnTest (K : KeyParts W₀ Rc X₀ X Wk) (N : OwnTestNumbers) (k : Coins Bk)
    (input : In1 W₀ Rc) (heard : List Fmt.Drawn) : Words GE :=
  fun o part i =>
    if o = N.omegaCopy then wordsOfOmegaAtKey K N k input heard part i
    else
      Johnson.Prover.Send.held
        (Johnson.Prover.Send.held (fun _ _ _ => 0) N.indexMasksFirst K.idx.P
          (rowsOfSending k sIdx K.idx input K.own₀ heard N.challengesBeforeIndexMasks))
        N.vectorWFirst K.w.P
        (rowsOfSending k sW K.w input K.own₀ heard N.challengesBeforeVectorW) o part i

/-- **What the tie asks of the parts**, beside `OwnSenders` (OwnJob.lean). -/
structure SendersReadInFront (K : KeyParts W₀ Rc X₀ X Wk) (N : OwnTestNumbers) : Prop where
  indexMasks : ∀ x (fr fr' : Front X),
    fr.heard.take N.challengesBeforeIndexMasks = fr'.heard.take N.challengesBeforeIndexMasks →
      K.idx.data x fr = K.idx.data x fr'
  vectorW : ∀ x (fr fr' : Front X),
    fr.heard.take N.challengesBeforeVectorW = fr'.heard.take N.challengesBeforeVectorW →
      K.w.data x fr = K.w.data x fr'
  point : K.send.atPoint = 0

/-- **The public test on the book, for a message of a sending of the kind K1.** spender: the part that carries.
n: the entry's number among those by which it carries. -/
def carriesMessage (Bk : ProverCoinCounts) (spender : Addr) (n : ℕ) (sender : Addr)
    (P : VerifiableInference.Desc.K1.Par) (ride : ℕ → Option K1.Ride) (message : ℕ) : Bool :=
  match (carryE Bk spender)[n]? with
  | some e => e.owner == sender && e.start == K1.startR P ride message &&
      e.count == K1.dueMsg P.codes (shapeAt P message) (ride message)
  | none => false

/-- An address has rows in one chain's table alone: the other two tables. -/
def noRowIn (rows : List (Addr × Due)) (a : Addr) : Prop := rows.any (fun r => r.1 == a) = false

/-- **What the tie asks of the book.** place: the own test's. -/
structure BookAtOwnTest (Bk : ProverCoinCounts) (K : KeyParts W₀ Rc X₀ X Wk) (place : Place) : Prop where
  /-- the test's second part carries the three members' coins from where their senders read them -/
  carriesIndexMasks :
    carriesMessage Bk ⟨place, 1⟩ 0 sIdx K.idx.P K.idx.ride (K.idx.P.sent.size - 1) = true
  carriesVectorW : carriesMessage Bk ⟨place, 1⟩ 1 sW K.w.P K.w.ride 0 = true
  carriesOmega : cutFits Bk ⟨place, 1⟩ 2 ⟨K14.sendPlace 5, 0⟩ (K14.jobOmega ⟨K.send.P, 0⟩) 0 = true
  /-- the senders' rows hold just what the senders take, each in its own chain's table alone -/
  rowIndexMasks : dueAt Bk.first sIdx = K1.dueR K.idx.P K.idx.ride
  rowVectorW : dueAt Bk.first sW = K1.dueR K.w.P K.w.ride
  rowOmega : dueAt Bk.shared ⟨K14.sendPlace 5, 0⟩ =
    (K14.sendingPart (K14.jobOmega ⟨K.send.P, 0⟩)).takes
  indexMasksNotShared : noRowIn Bk.shared sIdx
  indexMasksNotLast : noRowIn Bk.second sIdx
  vectorWNotShared : noRowIn Bk.shared sW
  vectorWNotLast : noRowIn Bk.second sW
  omegaNotFirst : noRowIn Bk.first ⟨K14.sendPlace 5, 0⟩
  omegaNotLast : noRowIn Bk.second ⟨K14.sendPlace 5, 0⟩

/-- **What the tie asks of the shared chain's plan.** -/
structure SharedPlanAtOwnTest (Q : Desc.K14.P14) : Prop where
  fits : K14.sendingsFit Q = true
  length : ellOmegaB ⟨Q, 0⟩ = true
  plan : ∃ layO, K14.Plan2 Q (sentOf Q.S) layO
  shapes : K14.SendShapes Q

/-- **What the tie asks of the statement on entry.** g: the own group's number. -/
structure StatementAtOwnTest (S : Statement) (g : ℕ) (K : KeyParts W₀ Rc X₀ X Wk)
    (N : OwnTestNumbers) : Prop where
  members : ∀ G : Group, S.groups[g]? = some G →
    G.members = #[N.indexMasksFirst + (K.idx.P.sent.size - 1), N.vectorWFirst, N.omegaCopy]
  apart : N.indexMasksFirst + K.idx.P.sent.size ≤ N.vectorWFirst ∧
    N.vectorWFirst + K.w.P.sent.size ≤ N.omegaCopy
  sendsIndexMasks : 0 < K.idx.P.sent.size
  sendsVectorW : 0 < K.w.P.sent.size
  shapeIndexMasks : (S.oracles[N.indexMasksFirst + (K.idx.P.sent.size - 1)]?).map (·.shape) =
    some (shapeAt K.idx.P (K.idx.P.sent.size - 1))
  shapeVectorW : (S.oracles[N.vectorWFirst]?).map (·.shape) = some (shapeAt K.w.P 0)
  shapeOmega : (S.oracles[N.omegaCopy]?).map (·.shape) =
    some (Light.shapeAt (K14.jobOmega ⟨K.send.P, 0⟩) 0)
  codes : S.codes = K.send.P.codes

/-- **What the tie asks of the challenges.** testHeard: what the test's front has heard. heard: the list at which
the words are read. -/
structure HeardAtOwnTest (K : KeyParts W₀ Rc X₀ X Wk) (N : OwnTestNumbers)
    (testHeard heard : List Fmt.Drawn) : Prop where
  beforeIndexMasks : testHeard.take N.challengesBeforeIndexMasks =
    heard.take N.challengesBeforeIndexMasks
  beforeVectorW : testHeard.take N.challengesBeforeVectorW = heard.take N.challengesBeforeVectorW
  point : (testHeard.drop N.challengesOfFirstChain).take 1 =
    (heard.drop N.challengesOfFirstChain).take 1
  pointHeard : heard.drop N.challengesOfFirstChain ≠ []
  pointLength : (Desc.K14.drawn (K14.firstRv (heard.drop N.challengesOfFirstChain))).length =
    K.send.P.par.S.kCol

end ProofFile.Honest.K12.AtKey

end

#print axioms ProofFile.Honest.K12.AtKey.OwnTestNumbers
#print axioms ProofFile.Honest.K12.AtKey.ownCoinsOfSending
#print axioms ProofFile.Honest.K12.AtKey.frontBeforeSending
#print axioms ProofFile.Honest.K12.AtKey.rowsOfSending
#print axioms ProofFile.Honest.K12.AtKey.commonOfInput
#print axioms ProofFile.Honest.K12.AtKey.wordsOfOmegaAtKey
#print axioms ProofFile.Honest.K12.AtKey.wordsAtKeyOwnTest
#print axioms ProofFile.Honest.K12.AtKey.SendersReadInFront
#print axioms ProofFile.Honest.K12.AtKey.carriesMessage
#print axioms ProofFile.Honest.K12.AtKey.noRowIn
#print axioms ProofFile.Honest.K12.AtKey.BookAtOwnTest
#print axioms ProofFile.Honest.K12.AtKey.SharedPlanAtOwnTest
#print axioms ProofFile.Honest.K12.AtKey.StatementAtOwnTest
#print axioms ProofFile.Honest.K12.AtKey.HeardAtOwnTest
