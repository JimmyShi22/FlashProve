-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Exact.lean: the kind "the code switch" (K2): A STATEMENT, NOT
PROVED HERE: at a side that is seated with the kind's row (`switchRow`, Honest/K2/Sim.lean), the
sentence of the field `exact` of the frame's `Good` (Honest/Side.lean), asked at every state,
whatever columns it has been handed, with the premise on the stand laid as "true". Definitions; one
lemma on the part's text. The statement is none of the library's goals.

THE STATEMENT IS AN IMPLICATION FROM THE PREMISES NAMED HERE (`ExactAsks`). THE IMPLICATION IS
PROVED IN Honest/K2/Law/ExactProof.lean (`switchExact`). ITS PREMISES ARE NOT SHOWN: see the limits.

THIS STATEMENT IS NEVER TO BE QUOTED WITHOUT THE ONE IN Honest/K2/Fresh.lean. At a small model
outside this library (a reckoning, no proof; nothing of it is shown here) the equation below still
held at a sender with the tail of a message's mask row struck, or the fresh mask's tail struck; and,
AT EVERY SEED THAT WAS TRIED BUT ONE WHOSE POINT's LAST COORDINATE IS 0, with the pad of a message
with a mask row struck. These are the other statement's to catch; there the struck pad was run, and
that equation failed.

THREE LAWS STAND BENEATH IT, AND NONE IS SHOWN HERE. TWO ARE ON THE SENDER (`SendSameLaw`; for the
second statement `SendFreshLaw`, Honest/K2/Fresh.lean): Honest/K2/Law/AtCore.lean shows them of the
core's sender, under its own named premises, OVER ANOTHER WRITER's TWO THEOREMS. THE THIRD, on the
closing (`ReturnsLaw`), IS PROVED IN Honest/K2/Law/SegmentAlike.lean (`returnsLaw`): IT STANDS UNDER
A PUBLIC TEST, `closingOk`. THAT THE TEST SAYS YES IS PROVED FOR NO PLACE IN THIS FILE; under the
head, `closing_at_head` (Honest/K2/Law/ClosingAtHead.lean) proves that it says yes at each place of
the plan.

  `distinctMod`, `noticeWithin`   a count at one message and one list of positions: reduced modulo
                    the length of each code that the message names, they are at most as many
                    distinct ones as that code's rows have random tail symbols
  `asksWithin`      of the lists that are asked of a sending's trees, by the tree's number: that
                    count, OF EACH LIST AT THE MESSAGES OF ITS OWN TREE
  `switchBud`       `asksWithin` at the lists that are asked of the part's first round. It reads no
                    challenge
  `senderShows`     what a sending shows: of each tree's table ITS STATED LENGTH AND WIDTH and the
                    columns at the positions asked; the answers; nothing where either function
                    refuses
  `seedsFit`        the elements that the first round drew are just the place's seeds; EVERY WORD OF
                    THEM IS BELOW THE PRIME; no factor is spelt by three words 0: so no factor is 0
                    in the field
  `SendSameLaw`     THE SHARED SENDING's LAW, AS A NAMED PREMISE: where the sending passes the
                    shared sending's public test (`K1.sendFits`, Honest/K1/Coins.lean) and the table
                    that rides has one row: over uniform coins of the sending, `senderShows` has one
                    law AT EVERY TWO DATA, at seeds that fit and lists within the count. General in
                    the data: any two functions (message, row, place) to an element
  `ExactOf`         the sentence of the frame's field `exact` of `Good` WITHOUT A PREMISE ON THE
                    COLUMNS THAT THE STATE HAS BEEN HANDED: asked at every state, whatever its
                    opened columns; at the face of the first and the second chain and at "true" for
                    the premise on the stand. Member by member it reads as `ExactMember`
                    (Honest/Small/Field.lean, of other authors) at these letters: by reading: no
                    equation is stated here
  `ExactAsks`       ALL PREMISES, by name:
                    seated     the side is the frame's own, off a list of blocks, at the place
                    blocks     the simulator's letter is the block's own rounds and oracle messages
                    two        these are two rounds
                    fits       the switch's own sending passes the shared sending's public test
                    seeds      a challenge that the first round can draw holds seeds that fit
                    returns    NO PUBLIC PREMISE: A LAW: AT EVERY INPUT, LIST OF CHALLENGES AND
                               CARRIED COINS the closing returns just where the simulator's public
                               test says yes
                    oneRow     the fresh mask that rides has one mask row: in the very words of
                               `SendSameLaw`'s own hypothesis
                               (`fits` and `oneRow` are spent by `send` alone)
                    send       `SendSameLaw` at the switch's own sending
  `SwitchExact`     THE STATEMENT, AT ALL ITS LETTERS: `ExactAsks` gives `ExactOf` at `switchBud`
  `switchRowsAt_again`   PROVED: THE DATA OF THE PART's SECOND MOVE IS THE DATA OF ITS FIRST, at
                    every state, however short the list of challenges heard: the second move cuts
                    the part's own first challenge off again. So one data serves `senderShows`
  `lotClosingAt`    the closing as the kind's lot lays it (Honest/K2/AtPlan.lean), by name
  `ReturnsLaw`      THE THIRD LAW, AS A STATEMENT (proved elsewhere: above): where the place passes
                    the public test `closingOk`, the field `returns` holds of the lot's closing at
                    `ok := publicOk`

WHY NO PREMISE SAYS THAT WHAT IS SENT FITS THE ROUNDS. The frame refuses a message whose items or
whose tables' stated lengths and widths are not the round's (`Sending.fits`, Honest/Frame.lean).
The part's first move sends no item, its second answers alone and no table (Honest/K2/Part.lean): so
that verdict is a function of what `senderShows` yields (the tables' two numbers; how many answers)
and of the rounds: under `send` it falls alike on both sides, whether it is a yes or a no.

Limits. THE PREMISES ARE NOT SHOWN HERE. UNDER THE LIBRARY's HEAD AND THE OPENED DESCRIPTION, BOTH
HYPOTHESES, all eight hold together at each place of the kind, at the core's sender, the lot's own
closing and the letters at which the kind's lot of rows lays its row, and so the statement's
conclusion is had there (`exactAsks_at_head`, `exactOf_at_head`, Honest/K2/Law/ExactAtHead.lean,
with that file's limits). `SendSameLaw` is not shown here: Honest/K2/Law/AtCore.lean shows it of the
core's sender over another writer's theorem, WHERE EVERY MESSAGE WITH A MAIN ROW IS SAMPLED: a
public test that no premise here names. `returns` is shown of no closing here: of the lot's own it
holds, by `ReturnsLaw`, where `closingOk` says yes. `seeds` is not shown here (`seeds_at_place`,
Honest/K2/Law/SeedsOfDraw.lean, has it at the rounds that the lot of rows hands its simulator, from
two equations on the place's numbers): it is a fact on the kind's own first round at the place's
numbers. WHY THE COUNT GOES BY TREE: a message's symbols are shown at its own tree's list and at no
other, and each message has coins of its own; so counted, it is another writer's count on the shared
sending's rows, both ways (`asksWithin_iff_bud`, Honest/K2/Law/CoreSenderLaw.lean). Where all
messages of a sending lie in one tree it asks of that tree's list what a count at every message of
the sending asks. IT ASKS NO RANGE: no proof of either law spends one. By a reading of the core's
text, no theorem here: each symbol of a column hangs on the position modulo ITS OWN code's length,
the very modulus of the count. That a verifier hears no position at or beyond a tree's length is
typed nowhere here. A list beyond the number of trees is held to nothing; where no trees can be
laid, every list is. Nothing here says what the statement would mean for any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Sim

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc (Block Oracle)

variable {W₀ Rc Xi Tr X S Cl : Type}

/-- How many distinct numbers a list has modulo n. -/
def distinctMod (n : Nat) (l : List Nat) : Nat := ((l.map (· % n)).eraseDups).length

/-- **The count at one message and one list of positions.** -/
def noticeWithin (codes : OnBytes.Codes) (n : OnBytes.OracleNotice) (l : List Nat) : Prop :=
  (n.shape.mainRows ≠ 0 →
    distinctMod (2 ^ (codes.base.getD n.shape.code default).logN) l ≤
      (codes.base.getD n.shape.code default).r) ∧
  (n.shape.maskRows ≠ 0 →
    distinctMod (2 ^ (codes.mask.getD n.shape.maskCode default).logN) l ≤
      (codes.mask.getD n.shape.maskCode default).r)

/-- **The count on the lists that are asked of a sending's trees**, by the tree's number: each list
against the messages of its own tree. -/
def asksWithin (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (asks : List (List Nat)) : Prop :=
  ∀ (j : Nat) (l : List Nat), asks[j]? = some l → ∀ k, k < sent.size →
    ((VerifiableInference.Desc.Own.treesMade codes sent).getD {}).tree[k]? = some j →
    noticeWithin codes (sent.getD k default) l

/-- **The part's count**: of the number of the part in its row, its rounds' challenges, and the
positions that will be read: round, root, positions. -/
def switchBud (p : SwitchPlace) (_ : Nat) (_ : List Fmt.Drawn) (asks : List (List (List Nat))) :
    Prop :=
  asksWithin p.sizes.codes (switchSent p.sizes p.others) (asks.headD [])

/-- **What a sending shows.** seeds: the elements that its first round drew. asks: for each tree the
positions. -/
def senderShows (Sd : Sender) (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) (data : Nat → Nat → Nat → Cb.Gl.E) (seeds : List Fmt.Ext3)
    (asks : List (List Nat)) (c : Cs (sendingDue codes sent fresh)) :
    Option (List ((Nat × Nat) × List (Nat × List UInt64)) × List Cb.Gl.E) :=
  (Sd.tables codes sent fresh data c).toOption.bind fun T =>
    (Sd.answers codes sent fresh data c seeds).toOption.map fun A =>
      (T.zipIdx.map fun t =>
        ((t.1.logLength, t.1.words), ((asks[t.2]?).getD []).map fun x => (x, t.1.col x)), A)

/-- The elements drawn are just the place's seeds; every word of them is below the prime; no factor
is spelt by three words 0. -/
def seedsFit (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (seeds : List Fmt.Ext3) :
    Prop :=
  seeds.length = (sendingPar codes sent).seeds * ((sendingPar codes sent).coordinates + 1) ∧
    (∀ x ∈ seeds, x.1 < VerifiableInference.Desc.fieldPrimeWord ∧ x.2.1 < VerifiableInference.Desc.fieldPrimeWord ∧
      x.2.2 < VerifiableInference.Desc.fieldPrimeWord) ∧
    ∀ s ∈ VerifiableInference.Desc.K1.cutSeeds (sendingPar codes sent).coordinates
        (sendingPar codes sent).seeds (seeds.map OnBytes.E.ofTriple),
      OnBytes.isZeroE s.2 = false

/-- **The shared sending's law, as a named premise.** -/
def SendSameLaw (Sd : Sender) (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice)
    (fresh : Option (Nat × Nat)) : Prop :=
  K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true →
  (∀ x ∈ fresh, (sent.getD x.1 default).shape.maskRows = 1) →
  ∀ (data data' : Nat → Nat → Nat → Cb.Gl.E) (seeds : List Fmt.Ext3) (asks : List (List Nat)),
    seedsFit codes sent seeds → asksWithin codes sent asks →
    (Prob.unif (Cs (sendingDue codes sent fresh))).map
        (senderShows Sd codes sent fresh data seeds asks) =
      (Prob.unif (Cs (sendingDue codes sent fresh))).map
        (senderShows Sd codes sent fresh data' seeds asks)

/-- The sentence of the field `exact` of `Good` without a premise on the columns that the state has
been handed, at "true" for the premise on the stand: it is asked at every state. -/
def ExactOf (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (chain firstTree : Nat)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) : Prop :=
  ∀ u ∈ σ.members, ∀ ca m front ds asks, True → m.seen = front.seen →
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    front.holds chain firstTree (u.rounds.map (·.1)) ds = true →
    u.part.stopAt (Face.own.sees m.st.input) m.loc ds ≠ some .hid →
    (Prob.unif (Cs u.part.takes × CsAll u.part.spends)).map
        (fun c => σ.shows .own u (c.1, c.2, ca) m ds asks) =
      (Prob.unif (Cs u.sim.takes)).map fun c => u.tells .own c m.st.input front ds asks

/-- **All premises.** -/
structure ExactAsks (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (ok : Xi → Bool)
    (rounds : List (Fmt.DeclaredRound × List Oracle)) (bs : List (Block S Cl)) (fs : List (Fall S))
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) : Prop where
  seated : Side.seated bs p.place (switchRow Sd D readers closing p ok rounds) fs = some σ
  blocks : σ.block.rounds.zip σ.block.oracles = rounds
  two : rounds.length = 2
  fits : K1.sendFits (sendingPar p.sizes.codes (switchSent p.sizes p.others))
    (rideOf (switchSent p.sizes p.others) (switchFresh p.sizes p.others p.foldVars)) = true
  seeds : ∀ r ∈ rounds.head?, ∀ d : Fmt.Drawn, drawFit r.1 d = true →
    seedsFit p.sizes.codes (switchSent p.sizes p.others) d.elems
  returns : ∀ (w : Local W₀ Rc Xi Tr) (heard : List Fmt.Drawn) (ca : CsAll p.carries),
    (closing p (D w.x) (readers w) heard (Stretch.carried p.carries ca)).toOption.isSome = ok w.x
  oneRow : ∀ x ∈ switchFresh p.sizes p.others p.foldVars,
    ((switchSent p.sizes p.others).getD x.1 default).shape.maskRows = 1
  send : SendSameLaw Sd p.sizes.codes (switchSent p.sizes p.others)
    (switchFresh p.sizes p.others p.foldVars)

/-- **THE STATEMENT**, meant at all its letters. Not proved here: `switchExact`,
Honest/K2/Law/ExactProof.lean. -/
def SwitchExact (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (ok : Xi → Bool)
    (rounds : List (Fmt.DeclaredRound × List Oracle)) (bs : List (Block S Cl)) (fs : List (Fall S))
    (σ : Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) (chain firstTree : Nat) : Prop :=
  ExactAsks Sd D readers closing p ok rounds bs fs σ → ExactOf σ chain firstTree (switchBud p)

/-! ## One data at both moves -/

/-- **The data of the part's second move is the data of its first.** t: the state at the first move.
t': at the second: the same input; one challenge more has been heard. -/
theorem switchRowsAt_again (Z : VerifiableInference.Desc.K2.Honest.Sizes)
    (carries : List (String × Due)) (c : CsAll carries) (t t' : State SwitchAsk Unit)
    (d : Fmt.Drawn) (hi : t'.input = t.input) (hh : t'.heard = t.heard ++ [d]) :
    switchRowsAt Z carries c t' 1 = switchRowsAt Z carries c t 0 := by
  have h : t'.heard.take (t'.heard.length - 1) = t.heard.take (t.heard.length - 0) := by
    rw [hh]
    simp
  unfold switchRowsAt
  rw [h, hi]

/-! ## The third law -/

/-- The closing as the kind's lot lays it. lay: the item "layout". segs: all segments' public data.
-/
def lotClosingAt (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub) : Closing :=
  fun p D R heard k =>
    (ownLaid D lay p (segs.take p.link)).bind fun _ =>
      closingFor freshTable (segs.take p.link) p.sizes.kept
        (ownBy D R p.addrs
          (fun s m => (((segs[s]?).map (·.ownShapes (s == 0))).getD []).getD m {}) heard)
        heard k

/-- **The third law, as a statement.** Not proved here: `returnsLaw`,
Honest/K2/Law/SegmentAlike.lean. -/
def ReturnsLaw (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List SegmentPub) (p : SwitchPlace) : Prop :=
  closingOk freshTable (segs.take p.link) p = true →
    ∀ (w : Local W₀ Rc Xi Tr) (heard : List Fmt.Drawn) (ca : CsAll p.carries),
      (lotClosingAt lay segs p (D w.x) (readers w) heard
        (Stretch.carried p.carries ca)).toOption.isSome = publicOk D lay p (segs.take p.link) w.x

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.distinctMod
#print axioms ProofFile.Honest.K2.noticeWithin
#print axioms ProofFile.Honest.K2.asksWithin
#print axioms ProofFile.Honest.K2.switchBud
#print axioms ProofFile.Honest.K2.senderShows
#print axioms ProofFile.Honest.K2.seedsFit
#print axioms ProofFile.Honest.K2.SendSameLaw
#print axioms ProofFile.Honest.K2.ExactOf
#print axioms ProofFile.Honest.K2.ExactAsks
#print axioms ProofFile.Honest.K2.SwitchExact
#print axioms ProofFile.Honest.K2.switchRowsAt_again
#print axioms ProofFile.Honest.K2.lotClosingAt
#print axioms ProofFile.Honest.K2.ReturnsLaw
