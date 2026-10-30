-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/One.lean: the blocks of a key file's first chain outside its lookups and its
proximity test. Definitions only, all computable; nothing is proved here.

Five places. At each the decision on what a prover sends is a kind's own block, seated on the
chain's state (`ChainState`, Johnson/Desc/Key/State.lean); what is written here is the seat, the
kind's numbers off the plan's public values, and blocks without a round around it.
  "idx.1.send": the sending (`K1.sendOwn`) of the index-mask message; then its number is kept.
  "msg.1.send": the sending of the lookups' own message, with the mask that rides; then, behind
    it, the lines that the verifier program's `Wf.rowsVerify` has around that sending: its tests at
    the start, the message has the number that the parameters say, a new group, the message joins
    it.
  "batt.1.batt": the rows on the table are made of the lookups' claims on the keys, and the
    index-mask message's ledger has handed out just the lookups' entries; then the batching's
    three blocks (`K13.frontB`, `K13.claimCombinationBlock`, `K13.quietB`).
  "w.1.send": the record announces what the rounds say; the sending of W; then `K13.rowsB`: the own
    group, the joinings, the row on W.
  "seal": the chains' end (Johnson/Desc/ChainEnd.lean) at the first chain, with two clauses more.

Main names.
  Pieces: the five places' numbers in the chain, handed in by whoever lays the chain.
  sendingPar, batchWhere: the two kinds' numbers at a place.
  sendingSeat, batchLens: how a kind's record lies in the chain's state.
  openRangesGroup, layPile: the two longer blocks without a round.
  sendIndexMasks, sendOwnMessage, batchTableRows, sendW, firstChainEnd: the five places.
  firstChainEnded: the first chain's part of the file's last test.

Limits. The verifier program asks its tests at the start (`Wf.startCheck`) in front of the own
message's sending; here they stand behind it (`openRangesGroup`); nothing that they read is written
by that sending. A key file's first chain hears no reply: the batching's number "a reply is due" is
false.
The plan must have a batching: where the lookups leave one row, `K13.claimCombinationBlock`'s own test on the plan
refuses, though the test on the plan's entries (`wantsBatching`, Johnson/Desc/Key/Plan/One.lean)
wants no round of a batching there. That `openRangesGroup` and `layPile` do what the verifier
program does at these lines is not proved here. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.State
import Johnson.Desc.Key.TableRows
import Johnson.Desc.K1.Own
import Johnson.Desc.K13.Kind
import Johnson.Desc.ChainEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes OnBytes.Params
open VerifiableInference.Desc.Ground (newGroupP joinP)
open _root_.Desc.Plain (DState GPar)

variable {β Cl : Type}

/-! ## The places' numbers -/

/-- The five places' numbers in the chain. -/
structure Pieces where
  idx : Nat
  msg : Nat
  batt : Nat
  w : Nat
  sealAt : Nat

/-- The ground's two numbers: the plan's answers to a sample; the chain's first tree is 0. -/
def groundParOf (one : OneTime) : GPar := { samples := one.given.plan.samples, firstTree := 0 }

/-- The numbers of a sending at a place of chain 1. what: the name of the message's one part;
groups: for each oracle message of the sending, in order, the groups that it is told to join. No
bit of work is counted at these places (`work := 0`). -/
def sendingPar (one : OneTime) (piece : Nat) (what : String) (msg : Array OracleNotice)
    (groups : List (List Nat)) : K1.Par :=
  { place := ⟨1, none, piece, .K1⟩, codes := one.codes, gp := groundParOf one, work := 0
    parts := [(what, msg)], groups := groups }

/-- The numbers of the batching. sent: the trees that the chain has sent in front of it. -/
def batchWhere (one : OneTime) (N : Pieces) (sent : Nat) : K13.Where :=
  { chain := 1, piece := N.batt, pieceRows := N.w
    rows := sumT (one.ranges.lookups.map (·.parts.length)), lin := one.lin, sent := sent
    reply := false }

/-! ## The seats -/

/-- A block without a round at a given place. -/
def quietAt (name : String) (place : Place) (f : ChainState β → Except String (ChainState β)) :
    Block (ChainState β) Cl :=
  { name := name, place := place, planOk := true, rounds := [], oracles := [], before := []
    decide := fun s _ _ => f s, claims := [], after := [] }

/-- The same statement, book and roots, with another value beside them. -/
def withLoc {L M : Type} (d : DState L) (m : M) : DState M :=
  { st := d.st, book := d.book, roots := d.roots, opened := d.opened, loc := m }

/-- **The seat of a sending.** The kind's block is handed the count of rows that waits and the
statement's record; what it returns is laid back, with the new messages' numbers in `sent`. The
kind's block has no claims and no runs behind a batching; the seat lays none and does not ask it. -/
def sendingSeat (name : String) (P : K1.Par) : Block (ChainState β) Cl :=
  let b : Block (K1.Owing (DState (Array Nat))) Cl := K1.sendOwn P
  { name := name, place := b.place, planOk := b.planOk, rounds := b.rounds, oracles := b.oracles
    before := b.before
    decide := fun s rs gs =>
      (b.decide { owed := s.debt, held := withLoc s.d #[] } rs gs).map fun y =>
        { s with d := withLoc y.held (), owed := y.owed, sent := y.held.loc }
    claims := [], after := [] }

/-- **The seat of the batching.** It is entered once. No reply is heard on this chain. Written back
are the count that waits, what W's sending announces, the numbers sent with W, the claim and the
statement's record; the pile and the index-mask message's number are handed in and not taken
back. -/
def batchLens : K13.Lens (ChainState β) where
  enter := fun s => if s.atEnd then none else some { s with atEnd := true }
  get? := fun s =>
    if s.atEnd then
      some { owed := s.debt, heard := none, indexMasks := s.idx, pile := s.pile, msg := s.msgW
             ids := s.ids, lin := s.lin, d := s.d }
    else none
  set := fun s p => { s with owed := p.owed, msgW := p.msg, ids := p.ids, lin := p.lin, d := p.d }

/-! ## The longer blocks without a round -/

/-- Behind the own message's sending: after the verifier program's `Wf.startCheck` and
`Wf.rowsVerify`. The program asks `Wf.startCheck`'s three tests in front of the sending. -/
def openRangesGroup (one : OneTime) (s : ChainState β) : Except String (ChainState β) := do
  let x := one.ranges
  need "WF: the parameters are admitted" (Wf.admitted s.d.st.codes x (Wf.matrixOf one.lin))
  let o ← named "WF: the index-mask message is not there" s.d.st.oracles[s.idx]?
  need "WF: the index-mask message is sampled and has mask rows alone"
    (o.sampled && o.shape.mainRows == 0)
  need "WF: the own message's answers are the plan's"
    (x.message.shape.answers == one.given.plan.samples)
  let m ← named "WF: the sending has left no number" s.sent[0]?
  need "WF: the own message has the number that the parameters say" (m == x.messageId)
  let g ← named "WF: the group cannot be made"
    (newGroupP s.d x.message.shape.code x.message.shape.maskCode)
  let d ← named "WF: the own message cannot join its group" (joinP g.2 g.1 m false)
  pure { s with d := d, grp := g.1, rider := if x.choice.masksRide then s.sent[1]? else none }

/-- The rows on the table are made of the lookups' claims on the keys. The lookups' own blocks have
taken their entries off the statement's ledgers: it is asked that the index-mask message's ledger
has handed out just as many as the lookups take. keysOf: where these claims lie in the maker's
record. -/
def layPile (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (s : ChainState β) :
    Except String (ChainState β) := do
  need "the rows on the table are laid once" s.pile.isEmpty
  let m := Wf.matrixOf one.lin
  let keys := keysOf s.base
  need "a list of claims on the keys for each lookup" (one.ranges.lookups.length == keys.length)
  let rows ← named "a claim on a part's keys gives no row on the table"
    ((zipT one.ranges.lookups keys).mapM fun x => tableRowsOf m x.1 x.2)
  let o ← named "the index-mask message is not there" s.d.st.oracles[s.idx]?
  let l ← named "the index-mask message has no ledger" o.ledger
  need "the index-mask message's ledger has handed out just the lookups' entries"
    (l.left + Wf.indexMasks one.ranges m ==
      Send.freeMaskEntries o.shape.maskRows (s.d.st.codes.mask.getD o.shape.maskCode default).ell
        o.shape.answers)
  pure { s with pile := rows.flatten }

/-! ## The places -/

/-- "idx.1.send". -/
def sendIndexMasks (one : OneTime) (N : Pieces) (groups : List (List Nat)) :
    Block (ChainState β) Cl :=
  let P := sendingPar one N.idx "the index masks" #[one.indexMasks] groups
  (sendingSeat "K1: the index masks' sending" P).andThen "idx.1.send"
    (quietAt "the index-mask message's number" P.place fun s => do
      let i ← named "the sending has left no number" s.sent[0]?
      pure { s with idx := i })

/-- "msg.1.send". -/
def sendOwnMessage (one : OneTime) (N : Pieces) (groups : List (List Nat)) :
    Block (ChainState β) Cl :=
  let P := sendingPar one N.msg "the lookups' own message and what rides with it"
    (Wf.messageOf one.ranges) groups
  (sendingSeat "K1: the own message's sending" P).andThen "msg.1.send"
    (quietAt "the ranges' group" P.place (openRangesGroup one))

/-- "batt.1.batt". -/
def batchTableRows (keysOf : β → List (List Lkp.Keys)) (one : OneTime) (N : Pieces) (sent : Nat) :
    Block (ChainState β) Cl :=
  let p := batchWhere one N sent
  let place : Place := ⟨1, none, p.piece, .K13⟩
  (((quietAt "the rows on the table" place (layPile keysOf one)).andThen "the rows and the front"
    (K13.frontB batchLens p)).andThen "the rows, the front and the batching"
    (K13.claimCombinationBlock batchLens p)).andThen "batt.1.batt" (K13.quietB batchLens p)

/-- "w.1.send". Nothing where the shape has no message with W. -/
def sendW (one : OneTime) (N : Pieces) (sent : Nat) (groups : List (List Nat)) :
    Option (Block (ChainState β) Cl) :=
  (linMessageW one.lin).map fun msg =>
    let P := sendingPar one N.w "W and what rides with it" msg groups
    (((quietAt "what is announced" P.place fun s => do
        need "K1: the record does not announce what ROUNDS says" (s.msgW == P.sent)
        pure s).andThen "announced and sent"
      (sendingSeat "K1: W's sending" P)).andThen "sent and numbered"
      (quietAt "the numbers sent with W" P.place fun s => pure { s with ids := s.sent })).andThen
      "w.1.send" (K13.rowsB batchLens (batchWhere one N sent))

/-- Two clauses on the statement at the first chain's end, which the verifier program asks at the
last chain's end alone. The own group, whose test is the last chain's, is left out with its
members. -/
def untestedButOwn (s : ChainState β) : List (String × Bool) :=
  let S := s.d.st
  let own := s.lin.map (·.own)
  [("end: a proximity test has begun on every group but the own one",
      S.groups.toList.zipIdx.all fun g => g.1.inRun || own == some g.2),
   ("end: every sampled message but the own group's members is in a tested group",
      S.oracles.toList.zipIdx.all fun x =>
        !x.1.sampled || (own.bind fun g => S.groups[g]?).any (·.members.contains x.2) ||
          x.1.groups.any fun g => (S.groups[g]?).any (·.inRun))]

/-- "seal". inFront: the rounds that the chain's blocks in front declare, read off the very blocks
that are laid. -/
def firstChainEnd (N : Pieces) (inFront : List Fmt.DeclaredRound) : Block (ChainState β) Cl :=
  { ChainEnd.chainEnd 1 N.sealAt true inFront
      (fun s : ChainState β =>
        [("end: no count of rows is owed", s.noneWaits)] ++ untestedButOwn s) with name := "seal" }

/-- The first chain's part of the file's last test: the batching has been entered; the claim, W's
number and the own group are laid. -/
def firstChainEnded (s : ChainState β) : Bool :=
  s.atEnd && s.lin.any fun l => l.own != noId && l.w != noId

end VerifiableInference.Desc.Key
