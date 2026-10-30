-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Reply/ReplyView.lean: the round REPLY of a proof file's first chain, on the program's
side: the plain scalars that the first call of a link receives are what the first of the rounds
still to come holds. Statements and proofs.

What it is for. `FirstParts` (OnBytes/Tie/Pv/Keeps/KeepsFirst.lean) has the calls of
`ReqFrame.first` as successes at their own contexts: where the link has plain scalars,
`Blk.recvEs` yields a list, and `Blk.closeEmpty "REPLY"` closes the round. On a view these two
calls take one round off the rounds that are still to come, and the list is what that round holds
(`round_view`, OnBytes/Tie/Pv/Psc/Run/ViewRounds.lean).

Main names:
  `closeEmpty_close`: a success of `Blk.closeEmpty` is a success of `Blk.close` at "nothing".
  `reply_view`: for a link with plain scalars: there is a round rv with: the rounds to come before
    the scalars are received are rv and then those behind REPLY; rv holds just the scalars, as
    many as the link's shape says; no message is open behind it.
  `reply_sent`: the field elements among rv's items are the scalars.
  `noReply_view`: for a link without plain scalars: no scalar is received and no round is taken.
Limits: one direction: from the calls' success. rv is the first of what is still to come at c4: it
is a WHOLE round of the view only if no message is open at c4, which is neither asked nor shown
here. That what is to come at c4 is a tail of the file's view's rounds, which round rv is by number,
and that the plan's entry there has the name REPLY are not said. Nothing is said on what the scalars
mean.
-/
import OnBytes.Tie.Pv.Keeps.KeepsFirst
import OnBytes.Tie.Pv.Psc.Run.ViewRounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Reply
open OnBytes OnBytes.Model OnBytes.L5 OnBytes.Model.Road OnBytes.PscRun

/-- A success of closeEmpty is a success of close at "nothing". -/
theorem closeEmpty_close {name : String} {c c' : Ctx} (h : Blk.closeEmpty name c = .ok ((), c')) :
    ∃ d, (Blk.close name .nothing).Yields c d c' := by
  have h1 : (Blk.closeEmpty name).Yields c () c' := (Blk.yields_iff _ _ _ _).2 h
  unfold Blk.closeEmpty at h1
  obtain ⟨d, c1, a1, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 h1
  obtain ⟨-, e⟩ := (Blk.yields_pure _ _ _ _).1 a2
  exact ⟨d, e ▸ a1⟩

variable {f : ReqFrame} {cEnd c : Ctx} {r : ReqFrame × Array Nat} {c' : Ctx}
  {L : Params.ReqLink} {G : ReqGroup} {g : ReqFrame} {plain : List E} {kept ids : Array Nat}
  {mask : Nat} {j : ReqFrame} {c4 c5 c6 c7 : Ctx}

/-- The round REPLY: the first of the rounds still to come; it holds just the scalars received. -/
theorem reply_view (P : FirstParts f cEnd c r c' L G g plain kept ids mask j c4 c5 c6 c7)
    (hp : (L.plain != 0) = true) :
    ∃ rv : Fmt.RoundView, c4.ch.pending = rv :: c6.ch.pending ∧ Holds rv plain ∧
      plain.length = L.plain ∧ PscRun.Clean c6 := by
  have h1 : (Blk.recvEs L.plain).Yields c4 plain c5 := (Blk.yields_iff _ _ _ _).2 P.heard
  obtain ⟨d, h2⟩ := closeEmpty_close (P.reply hp)
  obtain ⟨rv, a1, a2, -, a4⟩ := round_view P.v4 h1 h2
  exact ⟨rv, a1, a2, (recvEs_view P.v4 h1).1, a4⟩

/-- The field elements among that round's items are the scalars. -/
theorem reply_sent (P : FirstParts f cEnd c r c' L G g plain kept ids mask j c4 c5 c6 c7)
    (hp : (L.plain != 0) = true) :
    ∃ rv : Fmt.RoundView, c4.ch.pending = rv :: c6.ch.pending ∧ sentOf rv = plain := by
  obtain ⟨rv, a1, a2, -, -⟩ := reply_view P hp
  exact ⟨rv, a1, holds_sent a2⟩

/-- A link without plain scalars: nothing is received, no round is taken. -/
theorem noReply_view (P : FirstParts f cEnd c r c' L G g plain kept ids mask j c4 c5 c6 c7)
    (hp : ¬(L.plain != 0) = true) : plain = [] ∧ c6.ch.pending = c4.ch.pending := by
  have h1 : (Blk.recvEs L.plain).Yields c4 plain c5 := (Blk.yields_iff _ _ _ _).2 P.heard
  obtain ⟨a1, a2, -⟩ := recvEs_view P.v4 h1
  have e0 : L.plain = 0 := by
    by_contra hn
    exact hp (by simpa using hn)
  have e1 : plain = [] := List.eq_nil_of_length_eq_zero (a1.trans e0)
  rw [P.noReply hp]
  rcases a2 with ⟨-, e2⟩ | ⟨rv, t, gs, b1, b2, b3⟩
  · exact ⟨e1, e2⟩
  · subst e1
    have e3 : rv.vals = gs := by simpa using b2
    refine ⟨rfl, ?_⟩
    rw [b3, b1, ← e3]

#print axioms reply_view
#print axioms reply_sent
#print axioms noReply_view

end OnBytes.Tie.Pv.Reply
