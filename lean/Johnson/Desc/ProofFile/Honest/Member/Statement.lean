--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Member/Statement.lean: which value stands in the first chain of the
proof file's IOP at the place of a lot's sub-protocol: the statements. Definitions; each statement
is a definition of type Prop. No theorem. The proofs:
Johnson/Desc/ProofFile/Honest/Member/AtLot.lean, and for the four uses Uses.lean.

Why. A kind's writer shows that the kind's own sub-protocol, as the kind's lot supplies it, accepts
the honest prover's messages. What runs is another value: the member of the first chain's flat list
at that place, as `baseOf`, `partsAt` (Johnson/Desc/ProofFile/OnlineDescriptionFromBlockTables.lean), `chainBy` (Frames1.lean)
and the driver (Johnson/Desc/First/Driver/Chain.lean) have wrapped it. A file beside this library,
Johnson/Desc/ProofFile/Honest/Side.lean, takes that member off the list by its place (`Side.seated`)
and speaks of its fields and its step (`Side.fits`; `Good`'s clauses on the member's step, in both
directions).

The library has the wrapped value as a term, with its laws, in Johnson/IMR/SeatForm.lean: `seatedAs
same b name a` (b behind `guardMark`, the place's name and the place written in, behind the guard on
the reply); `seatedWith same b q name a` (the same with a sub-protocol q laid behind b);
`LaidAlone`; `yes_alone`, `yes_alone_K7`, `step_iff`: the wrapping adds two tests to a decision: the
state behind bears no mark of failure, and it holds the reply that stood in front (the second is not
asked at a place of the kind K7). `IM.Joined` (Johnson/IMR/SameSpot.lean) is the form at a segment's
first place: behind b lies the sub-protocol `opened` of the segment's own row of `framesOf`. The
library also says, by index and region by region, which lot's sub-protocol stands where
(`chain_hear`, PureChain.lean; `chain_back`, BackPlace.lean; `chain_close`, CloseSeat.lean;
`joined_at`, SameSpot.lean). These terms and laws are used here, not typed again.
What is added: one statement for every place of a kind, by the place (for every member of the flat
list that stands at the place), for the given sub-protocol of a lot and not for some sub-protocol at
that place, general in the structure `PureSeat`; and, for the form at a segment's first place, the
member's fields and its step as an equivalence, so that an acceptance can be concluded.
Main names:
  `AsFlat x m`: m is x as `Chain.blocksInOrder` (Johnson/Desc/Block.lean) lays it: x itself, or, outside the
    segments, x with one more test on the plan.
  `MemberLaid`: the main statement.
  `AlonePlace`, `MemberAlone`: at `onlineDescription`: places at which nothing is laid behind the lot's
    sub-protocol.
  `MemberFirst`: at `onlineDescription`, at a segment's first place: `IM.Joined`.
  `AloneGives`: what a kind's writer gets where the member is wrapped alone: its place, name,
    rounds, oracle messages and list `before`, and its decision and its step as equivalences.
  `JoinedGives`: the same for `IM.Joined`: four fields (place, rounds, oracle messages, `before`;
    not the name) and the step as an equivalence.
  `JoinedAccepts`: the decision of a member with any q laid behind b: from which acceptances it
    accepts.
  `MemberLast`: the first chain's last sub-protocol, which is of the kind `frame` and has a round.
  `K13AtM3`, `K13AtM4`, `K13AtEnd`, `K7Steps`: four uses.

What a kind's writer supplies: that its lot is in the list; that its sub-protocol is in the lot's
list `Lot.blocks` at the ground of a request of zeros (for one of `Lot.own`: its `Block.retype`);
that its place is of a kind; a member of the flat list at the place (`of_find`, AtLot.lean, takes it
from `List.find?`); whether its place is a segment's first, or which arm of `AlonePlace` it meets.
At kind K9's two places and kind K10's place in a segment's closing it also supplies `IM.HeadIsTwo
Z`, which the library shows only for the release's parameters and only at the hash `OnBytes.secondHashFunction`
(`head_is_two`, Johnson/IMR/CloseSeat.lean).
The member's name is the place's name, not the lot's sub-protocol's, at a segment's first place too:
`MemberLaid` tells which name it is. A lemma on a play at the lot's sub-protocol has to be general
in the name.

What is not covered. That a member stands at the place: a premise (by index the library has it). The
batching of a segment's claims as a function of the gatherer (kind K9's first place in a segment):
no lot's sub-protocol stands there. The other members of the kind `frame`. The two later chains:
their sub-protocols come from no lot. The runs of claims and the runs behind a segment's batching:
`claims_alone`, `after_alone` of SeatForm.lean apply through `AsFlat`; who runs them is the member
at kind K9's first place. The member's test on the plan. At `onlineDescription` the arm "of the kind K7" of
`AloneGives` is never met: kind K7's one place is a segment's first. That `onlineDescription` returns at any
three files.
What is not claimed. Nothing is proved in this file. Nothing on soundness, completeness or hiding.

-/
import Johnson.IMR.CloseSeat
import Johnson.IMR.SameSpot
import Johnson.IMR.SealSeat
import Johnson.Desc.ProofFile.Lot.K13
import Johnson.Desc.ProofFile.Lot.K13At4
import Johnson.Desc.ProofFile.Lot.K13End

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.AtPlace
open VerifiableInference.Desc (Block Chain FileDescription KindName Place)
open VerifiableInference.Desc.First (S)

/-- m is x as `Chain.blocksInOrder` lays it. -/
def AsFlat {σ C : Type} (x m : Block σ C) : Prop :=
  m = x ∨ m = { x with planOk := x.planOk && x.hasNoClaimsAndNothingAfter }

/-- The statement that, where `baseOf`, `partsAt` and `chainBy` have returned and `faultsAt` has
found nothing, every member of the flat list at the place of a lot's sub-protocol b that is of a
kind is b wrapped, under the name of the place's entry p in the list of places: alone, or with a
named member of the frames' list laid behind it, whose role names p's name and the place's segment.
General in the structure T. Not proved here (proved: `member_laid`, AtLot.lean); a lemma's
statement, none of the library's goals. -/
def MemberLaid : Prop :=
  ∀ (Z : Pub) (T : PureSeat) (B : PureBase) (base : List (Block S Cl)) (c : Chain S Cl),
    baseOf Z T = .ok B → faultsAt T B = [] → (partsAt T B).base = .ok base →
    chainBy Z base (partsAt T B).frames (partsAt T B).road = .ok c →
    ∀ L ∈ T.lots, ∀ b ∈ L.blocks B.G₀, b.place.kind ≠ KindName.frame →
    ∀ m ∈ c.blocksInOrder, m.place = b.place →
    ∃ x, AsFlat x m ∧ ∃ p ∈ B.spots, p.place = b.place ∧
      (IM.LaidAlone T.same x b p.name b.place ∨
        ∃ fr ∈ (partsAt T B).frames, ∃ l, fr.1 = FrameRole.behind l p.name ∧
          b.place.link = some l ∧ x = IM.seatedWith T.same b fr.2 p.name b.place)

/-- Places for which it is shown that nothing is laid behind the lot's sub-protocol at `onlineDescription`;
not the set of all such places. Outside the segments; the pieces 2 to 9 of a segment, of another
kind than K9 and K10; under `IM.HeadIsTwo`, the pieces 2 to 15 (kind K10's: 4 to 15). -/
def AlonePlace (Z : Pub) (a : Place) : Prop :=
  a.link = none ∨
    (a.kind ≠ KindName.K9 ∧ a.kind ≠ KindName.K10 ∧ 2 ≤ a.piece ∧ a.piece ≤ 9) ∨
    (IM.HeadIsTwo Z ∧ 2 ≤ a.piece ∧ a.piece ≤ 15 ∧ (a.kind = KindName.K10 → 4 ≤ a.piece))

/-- The statement that at `onlineDescription`, opened as `IM.Open` has it, a member at such a place is the
lot's sub-protocol wrapped, alone, under the member's own name. Not proved here (proved:
`member_alone`, AtLot.lean); a lemma's statement, none of the library's goals. -/
def MemberAlone : Prop :=
  ∀ (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription Inst) (Z : Pub) (Bs : PureBase)
    (base : List (Block S Cl)) (c : Chain S Cl) (A : SharedSeat) (B : SecondSeat),
    IM.Open o pol lay KL F Z Bs base c A B →
    ∀ L ∈ onlineFirstChainBlockTables Z, ∀ b ∈ L.blocks Bs.G₀, b.place.kind ≠ KindName.frame → AlonePlace Z b.place →
    ∀ m ∈ c.blocksInOrder, m.place = b.place →
    ∃ x, AsFlat x m ∧ IM.LaidAlone sameReply x b m.name b.place

/-- The statement that at `onlineDescription` a member at the first place of a segment, where a lot's
sub-protocol b stands, is b wrapped with the sub-protocol `opened` of the segment's own row of
`framesOf` laid behind it: `IM.Joined`, of the member itself. No other form is left, and
`IM.HeadIsTwo` is not asked. Not proved here (proved: `member_first`, AtLot.lean); a lemma's
statement, none of the library's goals. -/
def MemberFirst : Prop :=
  ∀ (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription Inst) (Z : Pub) (Bs : PureBase)
    (base : List (Block S Cl)) (c : Chain S Cl) (A : SharedSeat) (B : SecondSeat),
    IM.Open o pol lay KL F Z Bs base c A B →
    ∀ (l : Nat) (k : KindName), ∀ L ∈ onlineFirstChainBlockTables Z, ∀ b ∈ L.blocks Bs.G₀,
    b.place = ⟨1, some l, 1, k⟩ → k ≠ KindName.frame →
    ∀ m ∈ c.blocksInOrder, m.place = b.place → IM.Joined Z l m b b.place

/-- The statement of what the member has of a sub-protocol that is wrapped alone: five fields, and
its decision and its step: it accepts with a state just where b accepts with it, the state bears no
mark of failure, and the reply is as in front (not asked at a place of the kind K7). Not proved here
(proved: `alone_gives`, AtLot.lean); a lemma's statement, none of the library's goals. -/
def AloneGives : Prop :=
  ∀ (same : S → S → Bool) (x m b : Block S Cl) (name : String) (a : Place), AsFlat x m →
    IM.LaidAlone same x b name a →
    m.place = a ∧ m.name = name ∧ m.rounds = b.rounds ∧ m.oracles = b.oracles ∧
    m.before = b.before ∧
    (∀ (t t' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
      m.decide t rs gs = .ok t' ↔
        b.decide t rs gs = .ok t' ∧ t'.failed = none ∧ (a.kind = KindName.K7 ∨ same t t' = true)) ∧
    ∀ (ft : Nat) (t t' : S) (k : Nat) (rs : List Fmt.RoundView)
      (cols : List VerifiableInference.Desc.OpenedColumn),
      m.step ft t rs cols = .ok (t', k) ↔
        b.step ft t rs cols = .ok (t', k) ∧ t'.failed = none ∧
          (a.kind = KindName.K7 ∨ same t t' = true)

/-- The statement of what the member has of a sub-protocol b behind which the sub-protocol `opened`
of the row f of segment l is laid: four fields are b's or the place's, and its step accepts with a
state t' and k columns just where b's step accepts with some state u and k columns, u bears no mark
of failure, f.opened takes u to t', t' bears no mark and holds u's reply, and t' holds the reply in
front (not asked at a place of the kind K7). Not proved here (proved: `joined_gives`, AtLot.lean); a
lemma's statement, none of the library's goals. -/
def JoinedGives : Prop :=
  ∀ (Z : Pub) (l : Nat) (x m b : Block S Cl) (a : Place), AsFlat x m → IM.Joined Z l x b a →
    ∃ fs f, Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs ∧
      fs[l]? = some f ∧ m.place = a ∧ m.rounds = b.rounds ∧ m.oracles = b.oracles ∧
      m.before = b.before ∧
      ∀ (ft : Nat) (t t' : S) (k : Nat) (rs : List Fmt.RoundView)
        (cols : List VerifiableInference.Desc.OpenedColumn),
        m.step ft t rs cols = .ok (t', k) ↔
          ∃ u, b.step ft t rs cols = .ok (u, k) ∧ u.failed = none ∧ f.opened u = .ok t' ∧
            t'.failed = none ∧ sameReply u t' = true ∧
            (a.kind = KindName.K7 ∨ sameReply t t' = true)

/-- The statement that the decision of a member with q laid behind b accepts where b accepts its
share of the rounds and groups of columns with a state u without a mark of failure, q accepts the
rest from u with a state t' that holds u's reply, and t' holds the reply in front (not asked at a
place of the kind K7). Not proved here (proved: `joined_accepts`, AtLot.lean); a lemma's statement,
none of the library's goals. -/
def JoinedAccepts : Prop :=
  ∀ (same : S → S → Bool) (x m b q : Block S Cl) (name : String) (a : Place), AsFlat x m →
    x = IM.seatedWith same b q name a →
    ∀ (t u t' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))),
      b.decide t (rs.take b.rounds.length) (gs.take b.openings) = .ok u → u.failed = none →
      q.decide u (rs.drop b.rounds.length) (gs.drop b.openings) = .ok t' → same u t' = true →
      (a.kind = KindName.K7 ∨ same t t' = true) → m.decide t rs gs = .ok t'

/-- The statement that at `onlineDescription` every member at the place of the kind `frame` behind the last
segment is the first chain's last sub-protocol as `Chain.blocksInOrder` lays it, and that this last one is
the one sub-protocol of kind K13's third lot, wrapped alone. So `AloneGives` serves it. Not proved
here (proved: `member_last`, AtLot.lean); a lemma's statement, none of the library's goals. -/
def MemberLast : Prop :=
  ∀ (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription Inst) (Z : Pub) (Bs : PureBase)
    (base : List (Block S Cl)) (c : Chain S Cl) (A : SharedSeat) (B : SecondSeat),
    IM.Open o pol lay KL F Z Bs base c A B →
    ∀ m ∈ c.blocksInOrder, m.place = ⟨1, none, 5, .frame⟩ →
    AsFlat c.last m ∧
      IM.LaidAlone sameReply c.last
        (VerifiableInference.Desc.ChainEnd.chainEnd 1 5 true
          (VerifiableInference.Desc.K13.inFrontOf Z)
          VerifiableInference.Desc.First.endAsks : Block S Unit).retype
        c.last.name ⟨1, none, 5, .frame⟩

/-- The statement that at `onlineDescription` a member at the place "M:3", the members' batching, accepts
with a state wherever kind K13's sub-protocol there (its three parts as one) accepts with it from a
state without a mark of failure. Not proved here (proved: `k13_at_m3`, Uses.lean); a lemma's
statement, none of the library's goals. -/
def K13AtM3 : Prop :=
  ∀ (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription Inst) (Z : Pub) (Bs : PureBase)
    (base : List (Block S Cl)) (c : Chain S Cl) (A : SharedSeat) (B : SecondSeat),
    IM.Open o pol lay KL F Z Bs base c A B →
    ∀ m ∈ c.blocksInOrder, m.place = ⟨1, none, 3, .K13⟩ →
    ∀ (t t' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))), t.failed = none →
      (VerifiableInference.Desc.K13.atM3 (Cl := Unit)
        (VerifiableInference.Desc.K13.whereOf Z)).decide t rs gs = .ok t' →
      m.decide t rs gs = .ok t'

/-- The statement that at `onlineDescription` the lot of the place "M:4" has W's commitment w, and a member
at that place accepts two rounds with a state wherever the lot's sub-protocol there (w and kind
K13's part behind it, as one) accepts them with it from a state without a mark of failure. Not
proved here (proved: `k13_at_m4`, Uses.lean); a lemma's statement, none of the library's goals. -/
def K13AtM4 : Prop :=
  ∀ (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription Inst) (Z : Pub) (Bs : PureBase)
    (base : List (Block S Cl)) (c : Chain S Cl) (A : SharedSeat) (B : SecondSeat),
    IM.Open o pol lay KL F Z Bs base c A B →
    ∃ P' : VerifiableInference.Desc.K1.Par,
      VerifiableInference.Desc.K13.wBlock Z = some (VerifiableInference.Desc.K1.sendAtS P') ∧
      ∀ m ∈ c.blocksInOrder, m.place = ⟨1, none, 4, .K1⟩ →
      ∀ (t t' : S) (r₁ r₂ : Fmt.RoundView) (gs : List (List (Nat × List UInt64))), t.failed = none →
        (VerifiableInference.Desc.K13.atM4 (Cl := Unit) (VerifiableInference.Desc.K13.whereOf Z)
          (VerifiableInference.Desc.K1.sendAtS P')).decide t [r₁, r₂] gs = .ok t' →
        m.decide t [r₁, r₂] gs = .ok t'

/-- The statement that at `onlineDescription` a member at the first chain's last place accepts with a state
wherever the one sub-protocol of kind K13's third lot accepts with it from a state without a mark of
failure. Not proved here (proved: `k13_at_end`, Uses.lean); a lemma's statement, none of the
library's goals. -/
def K13AtEnd : Prop :=
  ∀ (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription Inst) (Z : Pub) (Bs : PureBase)
    (base : List (Block S Cl)) (c : Chain S Cl) (A : SharedSeat) (B : SecondSeat),
    IM.Open o pol lay KL F Z Bs base c A B →
    ∀ m ∈ c.blocksInOrder, m.place = ⟨1, none, 5, .frame⟩ →
    ∀ (t t' : S) (rs : List Fmt.RoundView) (gs : List (List (Nat × List UInt64))), t.failed = none →
      (VerifiableInference.Desc.ChainEnd.chainEnd 1 5 true
        (VerifiableInference.Desc.K13.inFrontOf Z)
        VerifiableInference.Desc.First.endAsks : Block S Unit).decide t rs gs = .ok t' →
      m.decide t rs gs = .ok t'

/-- The statement that at `onlineDescription` the step of a member at the first place of a segment, where
that place is of the kind K7 and the segment's row of `framesOf` hands the state on as it is,
accepts just where the step of the lot's sub-protocol there accepts with a state without a mark of
failure. The premise on the row is what `IM.k7_sits` (Johnson/IMR/FirstSeats.lean) concludes, only
for the release's parameters, only at the hash `OnBytes.secondHashFunction`, and for segment 24 alone. Not
proved here (proved: `k7_steps`, Uses.lean); a lemma's statement, none of the library's goals. -/
def K7Steps : Prop :=
  ∀ (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (F : FileDescription Inst) (Z : Pub) (Bs : PureBase)
    (base : List (Block S Cl)) (c : Chain S Cl) (A : SharedSeat) (B : SecondSeat),
    IM.Open o pol lay KL F Z Bs base c A B →
    ∀ (l : Nat), (∀ fs f,
      Johnson.Desc.First.Walk.Seat.framesOf Z.p.built.links Z.first Z.p.X = .ok fs →
      fs[l]? = some f → f.opened = fun s => .ok s) →
    ∀ L ∈ onlineFirstChainBlockTables Z, ∀ b ∈ L.blocks Bs.G₀, b.place = ⟨1, some l, 1, .K7⟩ →
    ∀ m ∈ c.blocksInOrder, m.place = b.place →
    ∀ (ft : Nat) (t t' : S) (k : Nat) (rs : List Fmt.RoundView)
      (cols : List VerifiableInference.Desc.OpenedColumn),
      m.step ft t rs cols = .ok (t', k) ↔ b.step ft t rs cols = .ok (t', k) ∧ t'.failed = none

end ProofFile.Honest.AtPlace
