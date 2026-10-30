-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Seated.lean: THE CODE SWITCH AS A MEMBER OF A THREAD
(Honest/Thread/Thr.lean, Honest/Thread/Pays.lean): THE NAMED PREMISES ON THE THREAD's LETTERS, IN
ONE STRUCTURE. Definitions alone. NOTHING IS PROVED IN THIS FILE, and it is none of the library's
goals.

THE THREAD T IS A VARIABLE. Every fact on its letters that a law on this member is to spend is a
field of `K2Seated`.

  `noSeen`          nothing shown: the value of `Seen` at which the first move is called
  `switchSays`      what the switch's part says in its first round, AS A FUNCTION of a run's coins,
                    the input and the challenges in front of the part: the part's own first move, at
                    the coins that the frame lends it (`lendPart`, Honest/Frame.lean)
  `noTable`, `switchTableAt`   the table number j of that message; an empty table where the part
                    refuses or sends fewer
  `K2Seated`        THE PREMISES, in five sorts:
                    THE MEMBER AND ITS HALF: the member number b; its place is the switch's; the
                      half found at that place is the kind's; its rounds and the oracle messages
                      that it states are the kind's at the place's numbers; one message a root; the
                      trees that its second round opens are at hand in front; ITS DECISION, AT TWO
                      ROUNDS AND AS MANY GROUPS OF COLUMNS AS THE PLACE READS TREES, IS: A LETTER
                      `before`, THE KIND's OWN, A LETTER `after`: BOTH WAYS;
                    THE TREES: each tree that the member sends has, as the thread's table, the
                      switch's place and `switchTableAt`; it is fixed by the challenges heard at the
                      member's front border;
                    THE TABLE OF JOINTS: the claim that the closed segment hands on is open in
                      front and means what the composed meaning says (`mgAll`,
                      Johnson/Desc/Sound/MgAll.lean); what the row owes are four items; three of
                      them, the rows' three classes, follow from the composed meaning's;
                    WHAT IS LEFT: a letter `clause`: THE PLACE's OWN SENTENCE on the state in front
                      and behind (`K2KeepsLink`, `K2PlaceHead` or `K2PlaceFinish`,
                      Johnson/Desc/K2/Honest/Keeps.lean): a yes of the member's decision gives it,
                      and the thread's `keeps` follows from it; `before` and `after` leave the mark
                      as it was;
                    THE FORM: the form in front says that the state bears no mark; a state without
                      a mark has the form behind

WHICH DEBT (Honest/Thread/Pays.lean) THE FIELDS ARE MEANT TO SERVE. `Plays`: here · place · half ·
rounds · oracles · roots · opens · table · fixed. `Accepted`: decides. `Behind`: decides · pays ·
keeps · marks · formFront · form. `Exchange`: ITS TWO ENDS ALONE (asks · carry; owes · carried ·
sample · position): nothing of it can be paid from these fields, for want of the witness.

Limits. NOT HERE: the fourth item that the row owes (the pins of the messages sent: the thread's own
letter) · the pins of the kept messages, which the row shuts · THE WITNESS: that the thread's
witness has, at the switch's tenants, the messages of which `switchTableAt` is the code word ·
`formP` at either border · `rides`. `before` and `after` are letters: what the place's block lays in
front of and behind the kind's own (nothing; the opening of a segment; the head's; the finish's two
quiet steps: Johnson/Desc/ProofFile/Lot/K2.lean): they stand in `decides` both ways, so a hollow
letter makes a claim on the member that is false of a member that accepts; so does a hollow `clause`
in `pays`. NOTHING PINS `clause` TO ONE OF THE THREE SENTENCES NAMED ABOVE: it is a letter. The four
owed items need not differ, and `owes` is an inclusion. THE CLOSING FINDS A FOLD's CHALLENGES BY
THEIR NUMBERS AMONG THE CHAIN's ROUNDS, FROM 0 (Honest/K2/Closing.lean): that fits a thread with no
round in front of the chain (`T.front = 0`) alone; `closing` is a letter here. Every premise is a
premise: none is shown at any thread. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Pays
import Johnson.Desc.ProofFile.Honest.K2.Half
import Johnson.Top.H0.Tw.K2C.Kind
import Johnson.Desc.Sound.MgAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc (Block Place Strs Wit)
open VerifiableInference.Desc.First (S Meaning)
open VerifiableInference.Desc.First.K2 (P2 decideWith)
open VerifiableInference.Desc.Sound (MgData mgAll CellsQ MsgT)

variable {W₀ Rc Xi Tr : Type}

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- **Nothing shown**: the value of `Seen` at which `switchSays` calls the part's first move: no
round, and no columns handed. THE BODY HAS TWO ARMS, so that it types at either form of the frame's
record: where the frame has `Seen.bare` ("rounds alone: no columns are handed") it is `Seen.bare
[]`; where the record has the one field rounds it is the bracket of the empty list. A reader cannot
tell from this text which arm is taken: it is to be written plainly once the record has one form.
Nothing hangs on the value: both moves of the switch's part drop this argument (`moveOne`,
`moveTwo`, Honest/K2/Law/SwitchMoves.lean). -/
def noSeen : Seen := by
  first
    | exact Seen.bare []
    | exact ⟨[]⟩

/-- **What the switch's part says in its first round**, of a run's coins, the input and the
challenges in front of the part. chain: the part's chain, from 0. The move is called at `noSeen`:
nothing shown. -/
def switchSays (Bk : ProverCoinCounts) (chain : Nat) (Sd : Sender) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p : SwitchPlace) (k : Coins Bk)
    (w : Local W₀ Rc Xi Tr) (h : List Fmt.Drawn) : Except String Sending :=
  (lendPart Bk (Bk.rowsOf chain) (k.look chain) ⟨p.place, 0⟩
      (switchPart Sd p.sizes p.others p.foldVars p.carries)).bind fun c =>
    match (switchPart Sd p.sizes p.others p.foldVars p.carries).moves with
    | mv :: _ => mv.say c noSeen ⟨switchWit D readers closing p w, h, ()⟩
    | [] => .error "the part has no move"

/-- A table without a word. -/
def noTable : Table := ⟨0, 0, fun _ i => i.elim0⟩

/-- **The table number j of the switch's sending.** THREE ROADS LEAD TO THE TABLE WITHOUT A WORD
(`noTable`): the frame hands the part nothing; the first move refuses, so no rows are laid; the
sending has no table number j. -/
def switchTableAt (Bk : ProverCoinCounts) (chain : Nat) (Sd : Sender) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p : SwitchPlace) (k : Coins Bk)
    (w : Local W₀ Rc Xi Tr) (h : List Fmt.Drawn) (j : Nat) : Table :=
  ((switchSays Bk chain Sd D readers closing p k w h).toOption.bind (·.tables[j]?)).getD noTable

/-- **THE PREMISES.** T, b, blk: the thread, the member's number, the member. Sd, D, readers,
closing, p: the half's letters and the place's public data. q: the place's numbers, as the kind's
block takes them. before: what the place's block lays in front of the kind's own. after: what it
lays behind: of the state at which the kind's decision stands and the state behind its yes. seg: the
segment into which the switch leads; behind the last segment the number of segments. clause: the
place's own sentence on what a yes leaves. iCarry: the
item that the row shuts; iPin, iCarried, iSample, iPosition: the four that it owes. toP, toW: what
was handed to the chain, and the witness, as the composed meaning takes them. Dof, Mg₀: the composed
meaning's data at an input, and the meaning beneath. -/
structure K2Seated {Bk : ProverCoinCounts} {Cl X Pb Pp Tok Xi' : Type} {rows cols nR : ℕ}
    {Xp : OnBytes.Model.Verify.Public}
    (T : Thread Bk S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb) (b : Nat) (blk : Block S Cl)
    (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing)
    (p : SwitchPlace) (q : P2) (before : S → Except String S) (after : S → S → Except String S)
    (clause : S → S → Prop) (seg : Nat)
    (iCarry iPin iCarried iSample iPosition : T.ι) (toP : T.P → Pp)
    (toW : T.Wt → Wit (CellsQ rows cols) Tok MsgT)
    (Dof : Local W₀ Rc Xi Tr → MgData Xi' Pp Tok rows cols nR Xp)
    (Mg₀ : Meaning Pp (Wit (CellsQ rows cols) Tok MsgT)) : Prop where
  /-- THE MEMBER AND ITS HALF -/
  here : T.bs[b]? = some blk
  place : blk.place = p.place
  half : (T.hs.find? fun g => g.place == blk.place) = some (switchHalf Sd D readers closing p)
  rounds : blk.rounds = VerifiableInference.Desc.First.K2.rounds q
  oracles : blk.oracles = [q.sent, []]
  /-- one oracle message a root -/
  roots : q.sent.length = q.roots
  /-- the trees that the second round opens are at hand in front of the member -/
  opens : ∀ r ∈ q.read, r.1 < treesTo T.bs b
  /-- the member's decision: `before`, the kind's own, `after`: both ways -/
  decides : ∀ s rs gs t, rs.length = 2 → gs.length = q.read.length →
    (blk.decide s rs gs = .ok t ↔ ∃ s₁ m, before s = .ok s₁ ∧
      decideWith _root_.Tw.K2.sendByL8 q s₁ rs gs = .ok m ∧ after s₁ m = .ok t)
  /-- THE TREES -/
  table : ∀ j, j < q.roots → ∀ k w h, T.table (.own (treesTo T.bs b + j)) k w h =
    (p.place, switchTableAt Bk T.chain Sd D readers closing p k w h j)
  fixed : ∀ j, j < q.roots → T.fixed (.own (treesTo T.bs b + j)) = T.front + roundsTo T.bs b
  /-- THE TABLE OF JOINTS -/
  later : 1 ≤ seg
  asks : iCarry ∈ T.opened b
  carry : ∀ w a y v, T.means w iCarry a y v →
    (mgAll (Dof w) Mg₀).carry (seg - 1) (toP a.1, a.2) y (toW v)
  owes : ∀ i ∈ (T.row b).owes, i = iPin ∨ i = iCarried ∨ i = iSample ∨ i = iPosition
  carried : ∀ w a y v, (mgAll (Dof w) Mg₀).row seg .carried (toP a.1, a.2) y (toW v) →
    T.means w iCarried a y v
  sample : ∀ w a y v, (mgAll (Dof w) Mg₀).row seg (.sample 0) (toP a.1, a.2) y (toW v) →
    T.means w iSample a y v
  position : ∀ w a y v, (mgAll (Dof w) Mg₀).row seg .position (toP a.1, a.2) y (toW v) →
    T.means w iPosition a y v
  /-- WHAT IS LEFT -/
  pays : ∀ s rs gs t, rs.length = 2 → gs.length = q.read.length → blk.decide s rs gs = .ok t →
    clause s t
  keeps : ∀ s t, clause s t → T.keeps b s t
  marks : (∀ s s₁, before s = .ok s₁ → s₁.failed = s.failed) ∧
    ∀ s₁ m t, after s₁ m = .ok t → t.failed = m.failed
  /-- THE FORM -/
  formFront : ∀ a : T.P × S, T.form b a = true → a.2.failed = none
  form : ∀ a : T.P × S, a.2.failed = none → T.form (b + 1) a = true

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.noSeen
#print axioms ProofFile.Honest.K2.switchSays
#print axioms ProofFile.Honest.K2.noTable
#print axioms ProofFile.Honest.K2.switchTableAt
#print axioms ProofFile.Honest.K2.K2Seated
