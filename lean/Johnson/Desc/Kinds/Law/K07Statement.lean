-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K07Statement.lean: THE NEXT TOKEN's LAW, AS ONE CLOSED PROPOSITION: a proposal
for the row K07_law of the list of laws owed, whose plain line is: "the next token: the token that
the last test compares with the asked one is the token of which the head's claims speak".
A definition and nothing else. Proved in K07Proof.lean.

THE TWO TEXTS. The next token's block (ReplyKind.lean): `Reply.decide` lays the one seat;
`Reply.fin` is its part of the last test. The output head's block (HeadFrame.lean): every letter of
its forms comes out of `Head.given p L s`; among them the class `Token`, whose `y` is the token of
which its claims speak: win (T - 1) = y (HeadCells.lean). THE TWO BLOCKS SHARE THE SEAT BY THEIR
TYPES: `Head.Seat S` extends `Reply.Seat S`.
-/
import Johnson.Desc.Kinds.HeadFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

/-- **THE NEXT TOKEN's LAW.** No chance in it. L: the head's seat, whose part `toSeat` is the next
token's; it gives back what was laid. p: the head's public parameters; the next token's block has
the one parameter V, AND IT IS THE HEAD's: p.sizes.V.
FIRST: the next token's block lays the seat once: it was empty in front, and behind it holds a token
below V.
SECOND: sHead: any record at which the head takes its letters (at the hearing, and again at each run
of claims: `decideBy` and `lettersAt` both call `given`); sEnd: the last record. If both seats hold
the same, the head's letters are there (g), and the last test's part says yes at sEnd for the
client's token `asked`: then THE HEAD's y IS `asked`; it is below V; and it is 0 where the last
position is not checked.
WHAT IT DOES NOT SAY. That no block between sHead and sEnd touches the seat: the premise on the two
seats; it is for the law of the fold over blocks. That T, r, e here are the head's: whoever lays the
two blocks side by side hands both the same numbers. What the head's claims say of y: Lemma 1, (c).
That `asked` is what the client asked: it is a letter of the last test.
HOW THE TWO BLOCKS ARE SEATED. The law is over ONE seat L. That the two blocks share it is true of
the kinds' texts, AND IT IS HOW THEY RIDE IN THE FOLD [by reading: Desc/ProofFile/Lot/K6K7.lean:
k7Core, k6Hear]: the next token's block is seated at out.reply (Stored/ReplySeatAt.lean: seatAt),
the head's seat takes that seat by name (Stored/HeadSeatAt.lean: toSeat), and it gives back what
was laid AT EVERY RECORD (seatAt_law). A yes of the seated block (Reply.blockAt) is a yes of the
kind's decision (Law/ReplyMeets.lean: reply_meets); in the fold it rides behind the entry of the
head's link: there from the record behind the entry's yes (joined_meets): FIRST speaks of it there;
SECOND at the head's seat. THAT THE REPLY LAID AT s' STILL STANDS AT sHead IS SAID BY NEITHER
HALF: "the token that was HEARD is the head's y" wants besides that no block between touches
out.reply (Law/K07Means.lean: Moved). Between sHead and sEnd it is the premise said above. -/
def K07LawStatement : Prop :=
  ∀ (S : Type) (L : Seat S), (∀ s x, L.reply (L.setReply s x) = some x) →
    ∀ (p : Par) (T r e asked : Nat),
      (∀ (s s' : S) (rs : List Fmt.RoundView), Reply.decide p.sizes.V L.toSeat s rs = some s' →
        L.reply s = none ∧ ∃ n, n < p.sizes.V ∧ Reply.token L.toSeat s' = some n) ∧
      (∀ (sHead sEnd : S) (g : Given), L.reply sHead = L.reply sEnd →
        given p L sHead = .ok g →
        Reply.fin p.sizes.V T r e asked L.toSeat sEnd = true →
        g.token.y = asked ∧ asked < p.sizes.V ∧ (e < T → asked = 0))

end VerifiableInference.Desc.Kinds.Head.Law
