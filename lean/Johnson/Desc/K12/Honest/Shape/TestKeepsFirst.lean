-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K12/Honest/Shape/TestKeepsFirst.lean: what a proximity test keeps, at the first chain's
state. One proposition on the state before the test's block and the state after it,
`K12KeepsFirst p s s'`, is defined. It is proved, under one hypothesis on the plan p, wherever the
library's own block `atFinish p` (Johnson/Desc/K12/AtFinish.lean) accepts (`k12KeepsFirst_of_yes`),
and from an accepting step of any block whose accept gives an accept of `atFinish p`
(`k12KeepsFirst_of_step`). General in p, s, s', rounds and columns.
Johnson/Desc/K12/Honest/Shape/TestKeepsAt354.lean, which imports this file, calls
`k12KeepsFirst_of_yes`. The verifier's state alone: no prover, no coin, no frame for an honest side.

Terms. A description (`FileDescription`, Johnson/Desc/Block.lean) has three chains; a chain's flat list
(`Chain.blocksInOrder`) is a list of blocks (`Block`). A block accepts where its `decide` returns `.ok` with
the next state. The state that the first chain carries is `S` (Johnson/Desc/First/State.lean), a
structure of nine fields: the statement `st` (`Statement`, OnBytes/Iop/Ground.lean: codes, oracle
messages, groups), the book of trees `book` (`TreeBook`: the trees, and each oracle message's
place), the count of roots `roots`, and `here`, `out`, `check`, `rowsOwed`, `req` and `failed`.
`out` holds the number of the index masks' message (`indexMasks`), the pile (`pending`) and the
reply (`reply`). A test is marked as failed where `failed` is not `none`. A message's ledger is its
field `ledger` (`Ledger`, OnBytes/Iop/Ground.lean: the message's free mask entries), which may be
`none`. The plan p (`P12`, Johnson/Desc/K12/Frame.lean) holds the numbers of the place of the test.
`atFinish p` is `(proximityTestKind guardedProximityTestParts p).inside enterFinish leaveFinish` (`proximityTestKind`: Frame.lean; `guardedProximityTestParts`:
Johnson/Desc/K12/JoinGuarded.lean). The way in, `enterFinish`, makes of s the structure t inside a test
(`T12`, Johnson/Desc/K12/Join.lean): t has the statement, the book and the count of roots of s, and
`t.g` and `t.mask` are read from `s.here`. The test's own block `proximityTestKind guardedProximityTestParts p` goes from t to t',
and `leaveFinish` writes the statement, the book and the count of roots of t' back into s. s is the
state before the block ("in front"), s' the state after it ("behind"). "The member" is the block in
a chain's list at which the test is placed: blk below. "The sentence" is `K12KeepsFirst`; "the
equation" is its clause `s' = { s with st := t'.st, book := t'.book, roots := t'.roots }`; "the
clause `room`" is its clause `RoomKept s.st s'.st`. "Older" is what s has. "To the letter" means:
the equal value at the same number. "In the letters of" means: stated with the Lean names of. "Not
the first fold's mask" is, in Lean, `t.mask ≠ some o`. The frame for an honest side is
Johnson/Desc/ProofFile/Honest/Frame.lean.

  `k12KeepsFirst_of_step`: where `p.answers = 1`, `SitsAtFinish p blk` and `StepYes ft blk s s'`
    (Johnson/Top/H0/Walk/Reach.lean) hold: `K12KeepsFirst p s s'` holds. For every type of claims,
    every block blk over `S` and every ft
  `k12KeepsFirst_of_yes`: where `p.answers = 1` and `(atFinish p).decide s rs gs` returns `.ok s'`:
    `K12KeepsFirst p s s'` holds
  `K12KeepsFirst p s s'`: a definition: three clauses. First, `s'.failed = none`: no test is marked
    as failed after the block. Second, there are t and t' such that `enterFinish s` returns t,
    `K12Keeps p t t'` holds (Johnson/Desc/K12/Honest/Shape/TestKeeps.lean), and s' is s with the
    statement, the book of trees and the count of roots of t': an equation on the whole state.
    Third, `RoomKept s.st s'.st`. The second clause holds three facts on s: `enterFinish s` returns
    only where the chain is at its finish (`s.here = .fin o`), no count of claims waits
    (`s.noneWaits`) and no test is marked as failed (`enterFinish_ok`,
    Johnson/Desc/K12/SeatLaws.lean)
  `RoomKept A B`: a definition, on two statements: a message that stood in front and was a member of
    no group keeps its ledger, to the letter, and is a member of no group behind. In Lean, with A in
    front and B behind: for every o below `A.oracles.size` that is in the `members` of no group of A
    (`Apart A o`, Johnson/Desc/K12/Law/RoomAcross.lean): `(B.oracles[o]?).bind (·.ledger)` is
    `(A.oracles[o]?).bind (·.ledger)`, and `Apart B o` holds
  `SitsAtFinish p blk`: a definition: the hypothesis on a block blk: at all s, s', rs and gs, if
    `blk.decide s rs gs` returns `.ok s'`, then `(atFinish p).decide s rs gs` returns `.ok s'`
  `sitsAtFinish_alone`: `SitsAtFinish p blk` holds where
    `IM.LaidAlone same blk (atFinish p).retype name a` (Johnson/IMR/SeatForm.lean) and
    `a.kind ≠ KindName.K7` hold. That is: blk is `atFinish p`, carried over to the claims' type
    `ProofFile.Cl` by `Block.retype` (Johnson/Desc/Block.lean), inside `ProofFile.guardMark` and `Block.guarded`
    (`IM.seatedAs`), with no block joined after it, under the given name, at a place a whose kind is
    not K7. For every `same` and every name
  `sitsAtFinish_congr`: `SitsAtFinish` reads only a block's `decide`: from `SitsAtFinish p blk` and
    `blk'.decide = blk.decide`: `SitsAtFinish p blk'`. So it holds as well of the block with another
    test on the plan (`planOk`), which is what `Chain.blocksInOrder` (Johnson/Desc/Block.lean) makes of a
    block outside the links
  `k12KeepsFirst_iff`: `K12KeepsFirst p s s'` holds if and only if
    `K12KeepsAt p enterFinish leaveFinish s s'` (TestKeeps.lean), `s'.failed = none` and
    `RoomKept s.st s'.st` hold
  `K12KeepsFirst.here`, `.out`, `.check`, `.rowsOwed`, `.req`, `.unmarked`: what the sentence gives,
    off the equation: the six other fields of the state stand as they were: where the chain stands;
    the index masks' message, the pile and the reply; the state of the calls; the count that waits;
    the request; and in front no test was marked. In Lean: `s'.here = s.here`, `s'.out = s.out`,
    `s'.check = s.check`, `s'.rowsOwed = s.rowsOwed`, `s'.req = s.req`, and `s.failed = none`, as
    the first clause has it of s'
  `K12KeepsFirst.room`, `.counting`, `.samples`: the clause `room`, by name; the same in the letters
    of the first chain's count of free mask entries (`Law.ledgerAt`,
    Johnson/Top/H0/Walk/FrameLaw.lean; `P1L20.outOfGroupsB`, Johnson/P1L20R/RoomFold.lean), with the
    pile and the reply; every older message's sample rows stay, at the chain's state. In Lean:
    `room` is `RoomKept s.st s'.st` at one o. `counting`: from `Law.ledgerAt s = some l` and
    `P1L20.outOfGroupsB s = true`: `Law.ledgerAt s' = some l`, `P1L20.outOfGroupsB s' = true` and
    `s'.out = s.out`; here `Law.ledgerAt s` is the ledger of the message number `s.out.indexMasks`,
    and `P1L20.outOfGroupsB s` tests that no group of `s.st` has this number in its `members`.
    `samples`: where `s.st` has the message x at o, `s'.st` has at o a message with the `sampleRows`
    of x
  `K12KeepsFirst.rides_past`: an older message that is no member of the group under test and not the
    first fold's mask stands behind the member to the letter, at its place in the book. In Lean:
    there is a t that `enterFinish s` returns such that, from `s.st.groups[t.g]? = some G`,
    `s.st.oracles[o]? = some x`, `o ∉ G.members.toList` and `t.mask ≠ some o`:
    `s'.st.oracles[o]? = some x`, and a place that `s.book` has for o is the place that `s'.book`
    has for o

By what. `k12KeepsFirst_of_yes` cuts the accept of `atFinish p` into what `enterFinish` returns, an
accept of `proximityTestKind guardedProximityTestParts p` and what `leaveFinish` returns, by `Seat.inside_ok`,
`Seat.enterFinish_ok` and `Seat.leaveFinish_ok` (Johnson/Desc/K12/SeatLaws.lean), and calls
`k12_keeps` (TestKeeps.lean), which has the hypothesis `p.early = true`. That the masks come early:
the library's `early_of_decide` (Johnson/Desc/K12/Law/EarlyStep.lean). The clause `room`: the
library's own `k12_room` (Johnson/Desc/K12/Law/RoomAcross.lean) is called. No mark after the block:
`enterFinish` refuses at a mark (`enterFinish_ok`), and the equation leaves that field unchanged.
`k12KeepsFirst_of_step`: `stepYes_decide` (Johnson/Top/H0/Walk/ReachInv.lean) gives an accept of
blk, `SitsAtFinish` one of `atFinish p`. `sitsAtFinish_alone`: `IM.yes_alone`
(Johnson/IMR/SeatForm.lean); `Block.retype` leaves `decide` as it is. `k12KeepsFirst_iff`:
`Seat.leaveFinish_ok`. `counting`: `room`, `out` and `P1L20.outOfGroupsB_iff` (RoomFold.lean).
`samples` and `rides_past`: the field `samples` of `K12Keeps` and `K12Keeps.rides_past`
(TestKeeps.lean).

Hypotheses. Of `k12KeepsFirst_of_step`: ha: `p.answers = 1`: a sample has one answer; hb:
`SitsAtFinish p blk`; h: `StepYes ft blk s s'`: the block's own `step` returns s', at as many rounds
as the block declares and at columns all of which it reads. Of `k12KeepsFirst_of_yes`: ha, and the
accept.

Limits.
- The statement, the book and the count of roots do change: how, is what the seven fields of
  `K12Keeps` and the clause `room` state. What `K12Keeps` leaves free is said in the head of
  TestKeeps.lean.
- `room` and `K12Keeps`' clause on the shape overlap: the shape holds every message's ledger and
  every group's members; no law here draws the one from the other. (In Lean: the field `shape` of
  `K12Keeps`; `OrcSh.ledger` and `GrpSh.members`, Johnson/Desc/Ground/Shape/Core.lean. No lemma of
  this file derives `RoomKept` from `shape`, or `shape` from `RoomKept`.)
- `RoomKept` compares options: where the message number o of A has no ledger, a B that has no
  message number o and a B whose message number o has no ledger meet the equation alike. That the
  message is there after the block is stated by `K12KeepsFirst.samples`, not by this clause.
- One direction only: from an accept to `K12KeepsFirst`. Nothing is stated from `K12KeepsFirst` to
  an accept.
- `SitsAtFinish` is a hypothesis of `k12KeepsFirst_of_step`. It is proved here for the one form of
  `sitsAtFinish_alone`, and `sitsAtFinish_congr` carries it on. A block that never accepts meets it
  vacuously.
- What `Chain.blocksInOrder` makes of a block is said by reading its text: this file applies
  `sitsAtFinish_congr` to nothing.
- That a description's flat list has such a block at any place is not stated here.
- This file gives no state at which `atFinish p` accepts, and no negative test.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.K12.Honest.Shape.TestKeeps
import Johnson.Desc.K12.AtFinish
import Johnson.Desc.K12.Law.RoomAcross
import Johnson.Desc.K12.Law.EarlyStep
import Johnson.IMR.SeatForm
import Johnson.Top.H0.Walk.ReachInv
import Johnson.P1L20R.RoomFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Sh
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (StepYes stepYes_decide)
open H2K.Out (Apart k12_room)

/-- A message that stood in front and was a member of no group keeps its ledger, to the letter, and
is a member of no group behind. A: the statement before the block (in front); B: the one after it
(behind). Where the message has no ledger in A, the equation does not say that B has a message at
that number. -/
def RoomKept (A B : Statement) : Prop :=
  ∀ o, o < A.oracles.size → Apart A o →
    (B.oracles[o]?).bind (·.ledger) = (A.oracles[o]?).bind (·.ledger) ∧ Apart B o

/-- What the proximity test's block keeps, at the first chain's state. s: the state before the
block; s': the state after it. -/
def K12KeepsFirst (p : P12) (s s' : S) : Prop :=
  s'.failed = none ∧ (∃ t t', enterFinish s = .ok t ∧ K12Keeps p t t' ∧
    s' = { s with st := t'.st, book := t'.book, roots := t'.roots }) ∧ RoomKept s.st s'.st

/-- Where `p.answers = 1` and `atFinish p` accepts, `K12KeepsFirst` holds. -/
theorem k12KeepsFirst_of_yes (p : P12) (ha : p.answers = 1) (s s' : S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64))) (h : (atFinish p).decide s rs gs = .ok s') :
    K12KeepsFirst p s s' := by
  obtain ⟨t, t', h1, h2, h3⟩ := (Seat.inside_ok enterFinish _ leaveFinish s s' rs gs).1 h
  obtain rfl := (Seat.leaveFinish_ok s s' t').1 h3
  obtain ⟨o, _, _, hm, rfl⟩ := Seat.enterFinish_ok s t h1
  refine ⟨by simpa using hm, ⟨_, t', h1,
    k12_keeps p (H2K.JointK.early_of_decide p _ t' rs gs h2) ha _ t' rs gs h2, rfl⟩,
    fun q hq hA => k12_room p _ t' rs gs h2 hq hA⟩

/-- The hypothesis on a block blk: where blk accepts, `atFinish p` accepts, with the same state
after it. -/
def SitsAtFinish {Cl : Type} (p : P12) (blk : Block S Cl) : Prop :=
  ∀ s s' rs gs, blk.decide s rs gs = .ok s' → (atFinish p).decide s rs gs = .ok s'

/-- `SitsAtFinish` reads only the block's `decide`. -/
theorem sitsAtFinish_congr {Cl : Type} {p : P12} {blk blk' : Block S Cl}
    (h : SitsAtFinish p blk) (e : blk'.decide = blk.decide) : SitsAtFinish p blk' :=
  fun s s' rs gs hd => h s s' rs gs (e ▸ hd)

/-- **From an accepting step of a block that meets `SitsAtFinish`, `K12KeepsFirst` holds**, where
`p.answers = 1`. -/
theorem k12KeepsFirst_of_step {Cl : Type} (p : P12) (ha : p.answers = 1) (ft : Nat)
    (blk : Block S Cl) (hb : SitsAtFinish p blk) (s s' : S) (h : StepYes ft blk s s') :
    K12KeepsFirst p s s' := by
  obtain ⟨rs, gs, hd⟩ := stepYes_decide h
  exact k12KeepsFirst_of_yes p ha s s' rs gs (hb s s' rs gs hd)

/-- `SitsAtFinish` is proved where the block is `atFinish p`, carried over to the claims' type
`ProofFile.Cl` (`Block.retype`) and placed, with no block joined after it (`IM.LaidAlone`), under a name
at a place whose kind is not K7. -/
theorem sitsAtFinish_alone (p : P12) {same : S → S → Bool} {blk : Block S ProofFile.Cl} {name : String}
    {a : Place} (h : IM.LaidAlone same blk (atFinish p).retype name a)
    (hk : a.kind ≠ KindName.K7) : SitsAtFinish p blk :=
  fun s s' rs gs hd => ((IM.yes_alone h hk s s' rs gs).1 hd).1

/-- `K12KeepsFirst` in terms of `K12KeepsAt`, the general form for a way in and a way out. -/
theorem k12KeepsFirst_iff (p : P12) (s s' : S) : K12KeepsFirst p s s' ↔
    K12KeepsAt p enterFinish leaveFinish s s' ∧ s'.failed = none ∧ RoomKept s.st s'.st := by
  constructor
  · rintro ⟨hm, ⟨t, t', h1, h2, h3⟩, hr⟩
    exact ⟨⟨t, t', h1, h2, (Seat.leaveFinish_ok s s' t').2 h3⟩, hm, hr⟩
  · rintro ⟨⟨t, t', h1, h2, h3⟩, hm, hr⟩
    exact ⟨hm, ⟨t, t', h1, h2, (Seat.leaveFinish_ok s s' t').1 h3⟩, hr⟩

variable {p : P12} {s s' : S}

theorem K12KeepsFirst.here (K : K12KeepsFirst p s s') : s'.here = s.here := by
  obtain ⟨_, ⟨t, t', _, _, rfl⟩, _⟩ := K
  rfl

theorem K12KeepsFirst.out (K : K12KeepsFirst p s s') : s'.out = s.out := by
  obtain ⟨_, ⟨t, t', _, _, rfl⟩, _⟩ := K
  rfl

theorem K12KeepsFirst.check (K : K12KeepsFirst p s s') : s'.check = s.check := by
  obtain ⟨_, ⟨t, t', _, _, rfl⟩, _⟩ := K
  rfl

theorem K12KeepsFirst.rowsOwed (K : K12KeepsFirst p s s') : s'.rowsOwed = s.rowsOwed := by
  obtain ⟨_, ⟨t, t', _, _, rfl⟩, _⟩ := K
  rfl

theorem K12KeepsFirst.req (K : K12KeepsFirst p s s') : s'.req = s.req := by
  obtain ⟨_, ⟨t, t', _, _, rfl⟩, _⟩ := K
  rfl

/-- Before the block no test was marked as failed either. -/
theorem K12KeepsFirst.unmarked (K : K12KeepsFirst p s s') : s.failed = none := by
  obtain ⟨hm, ⟨t, t', _, _, rfl⟩, _⟩ := K
  exact hm

/-- **The ledger of a message that is a member of no group**, and that it stays one. -/
theorem K12KeepsFirst.room (K : K12KeepsFirst p s s') {o : Nat} (ho : o < s.st.oracles.size)
    (hA : Apart s.st o) :
    (s'.st.oracles[o]?).bind (·.ledger) = (s.st.oracles[o]?).bind (·.ledger) ∧ Apart s'.st o :=
  K.2.2 o ho hA

/-- **The same in the letters of the first chain's count of free mask entries**: where the index
masks' message has a ledger and is a member of no group: behind the member its ledger is as it was,
it is a member of no group, and the pile, the reply and that message's number stand. -/
theorem K12KeepsFirst.counting (K : K12KeepsFirst p s s') {l : Ledger}
    (hl : Johnson.Desc.First.Walk.Law.ledgerAt s = some l)
    (hout : P1L20.outOfGroupsB s = true) :
    Johnson.Desc.First.Walk.Law.ledgerAt s' = some l ∧ P1L20.outOfGroupsB s' = true ∧
      s'.out = s.out := by
  have ho : s.out.indexMasks < s.st.oracles.size := by
    by_contra hc
    unfold Johnson.Desc.First.Walk.Law.ledgerAt at hl
    rw [Array.getElem?_eq_none (by omega)] at hl
    cases hl
  obtain ⟨e1, e2⟩ := K.room ho (P1L20.outOfGroupsB_iff.1 hout)
  refine ⟨?_, ?_, K.out⟩
  · unfold Johnson.Desc.First.Walk.Law.ledgerAt at hl ⊢
    rw [K.out, e1]
    exact hl
  · refine P1L20.outOfGroupsB_iff.2 ?_
    rw [K.out]
    exact e2

/-- Every message of `s.st` is there in `s'.st`, with the same sample rows. -/
theorem K12KeepsFirst.samples (K : K12KeepsFirst p s s') {o : Nat} {x : OnBytes.Oracle}
    (hx : s.st.oracles[o]? = some x) :
    ∃ x' : OnBytes.Oracle, s'.st.oracles[o]? = some x' ∧ x'.sampleRows = x.sampleRows := by
  obtain ⟨_, ⟨t, t', h1, h2, rfl⟩, _⟩ := K
  obtain ⟨_, _, _, _, rfl⟩ := Seat.enterFinish_ok s t h1
  exact h2.samples o x hx

/-- **What rides past the member.** t: what the way in makes of the state: t.g is the number of the
group under test, t.mask the first fold's mask. -/
theorem K12KeepsFirst.rides_past (K : K12KeepsFirst p s s') :
    ∃ t, enterFinish s = .ok t ∧ ∀ (G : Group) (o : Nat) (x : OnBytes.Oracle),
      s.st.groups[t.g]? = some G → s.st.oracles[o]? = some x → o ∉ G.members.toList →
      t.mask ≠ some o →
      s'.st.oracles[o]? = some x ∧
        ∀ q, s.book.place[o]? = some q → s'.book.place[o]? = some q := by
  obtain ⟨_, ⟨t, t', h1, h2, rfl⟩, _⟩ := K
  obtain ⟨_, _, _, _, rfl⟩ := Seat.enterFinish_ok s t h1
  exact ⟨_, h1, fun G o x hG hx hno hmask => h2.rides_past hG hx hno hmask⟩

end ProofFile.Honest.Sh

#print axioms ProofFile.Honest.Sh.k12KeepsFirst_of_yes
#print axioms ProofFile.Honest.Sh.sitsAtFinish_congr
#print axioms ProofFile.Honest.Sh.k12KeepsFirst_of_step
#print axioms ProofFile.Honest.Sh.sitsAtFinish_alone
#print axioms ProofFile.Honest.Sh.k12KeepsFirst_iff
#print axioms ProofFile.Honest.Sh.K12KeepsFirst.here
#print axioms ProofFile.Honest.Sh.K12KeepsFirst.out
#print axioms ProofFile.Honest.Sh.K12KeepsFirst.check
#print axioms ProofFile.Honest.Sh.K12KeepsFirst.rowsOwed
#print axioms ProofFile.Honest.Sh.K12KeepsFirst.req
#print axioms ProofFile.Honest.Sh.K12KeepsFirst.unmarked
#print axioms ProofFile.Honest.Sh.K12KeepsFirst.room
#print axioms ProofFile.Honest.Sh.K12KeepsFirst.counting
#print axioms ProofFile.Honest.Sh.K12KeepsFirst.samples
#print axioms ProofFile.Honest.Sh.K12KeepsFirst.rides_past
#print axioms ProofFile.Honest.Sh.RoomKept
#print axioms ProofFile.Honest.Sh.K12KeepsFirst
#print axioms ProofFile.Honest.Sh.SitsAtFinish
