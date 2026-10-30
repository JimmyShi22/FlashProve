-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K07Means.lean: A SENTENCE MEANT FOR THE ROW K07_means (of means_at_each_seat: "the head's keys at the heard reply are the keys at the witness's token"), AS ONE
CLOSED PROPOSITION IN OUR OWN LETTERS, WITH ITS PROOF.
THE SENTENCE ON THE KEYS is LookCallsAt W tab s y c (Law/ReplyPins.lean): every place of every call's key table of the head's lookup is a row of that call's table, at the public record's sizes and policy, the record's public
request, A TOKEN y and cells c. The token enters the keys at the last position alone (win (T - 1) = y).
  K07MeansStatement | k07Means   AT THE HEAD's SEAT (out.reply): sHead: a record at which the head takes its letters; sEnd: the last record; both hold one reply; the last test's part says yes at sEnd for the token "asked": THEN the
                sentence on the keys AT THE TOKEN THAT THE RECORD HAS HEARD is the sentence AT "asked"; asked < V; asked = 0 where the last position is not checked. No chance in it. From Law/K07Proof.lean's k07Law (its second half).
  Moved · k07MeansFromStep   THE WHOLE WAY FROM THE BLOCK AS IT RIDES: where the fold's own call Block.step of Reply.blockOf W l goes on to s' (rowReply): UNDER THE NAMED PREMISE Moved s' sHead (the token at K7's own seat
                behind the step is the token at out.reply at sHead; the request's words are the same): the sentence at the heard token at sHead gives the sentence at "asked" AT THE RECORD IN FRONT OF K7's STEP.
WHAT LACKS, AND WHOSE IT IS. (1) "THE WITNESS's TOKEN": here it is the letter "asked" of the last test: that it is the token of the integer model's witness (or of the statement) is said nowhere in our letters: the integer model's
Meaning (TieRow | tieRow | means_of_fifteen: Goal/Meaning/) is not imported here: NO JOIN TO tieRow IS TYPED; whether this is the clause that means_of_fifteen takes is not held. (2) Moved is a premise: Law/K07MeansHeard.lean's
moved_of_heard gives it where S.heard and the request's words are the same at the two records: that they are the same is shown in neither file; the place that opens the link owes that equation (Law/K07MeansHeard.lean's limit). (3) "both hold one reply" from sHead to sEnd: the fold's law (our blocks leave out.reply: Law/HeardAt.lean). (4) that the
sentence on the keys gives the integer model's clause: K03_means | K06_means, not this row. (5) tab, c: letters, tied to nothing.
Nothing on soundness.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K07Proof
import Johnson.Desc.Kinds.Law.ETies
import Johnson.Desc.Kinds.Law.ReplyPins

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc.First (S)

/-- **THE HEAD's KEYS AT THE HEARD REPLY ARE THE KEYS AT THE ASKED TOKEN.** -/
def K07MeansStatement : Prop :=
  ∀ (W : OnBytes.Model.Verify.Public) (iU3 work : Nat) (tab : Nat → Nat) (c : NCells)
    (sHead sEnd : S) (g : Given) (T r e asked : Nat),
    (seatAt W.hS iU3).reply sHead = (seatAt W.hS iU3).reply sEnd →
    given (parOf W.hS work) (seatAt W.hS iU3) sHead = .ok g →
    Reply.fin W.hS.V T r e asked (seatAt W.hS iU3).toSeat sEnd = true →
    (∃ y, Reply.token (seatAt W.hS iU3).toSeat sHead = some y ∧ LookCallsAt W tab sHead y c) →
    LookCallsAt W tab sHead asked c ∧ asked < W.hS.V ∧ (e < T → asked = 0)

theorem k07Means : K07MeansStatement := by
  intro W iU3 work tab c sHead sEnd g T r e asked hrep hg hfin ⟨y, hy, hlook⟩
  obtain ⟨h1, h2, h3⟩ := (k07Law S (seatAt W.hS iU3) (fun _ _ => rfl) (parOf W.hS work) T r e
    asked).2 sHead sEnd g hrep hg hfin
  have h4 := (given_letters hg).2.2.2
  rw [hy] at h4
  have h5 : y = asked := (Option.some.inj h4).trans h1
  subst h5
  exact ⟨hlook, h2, h3⟩

/-- THE NAMED PREMISE: one token at the two records' seats, and the same request's words. -/
def Moved (W : OnBytes.Model.Verify.Public) (iU3 : Nat) (s' sHead : S) : Prop :=
  Reply.token Reply.seatAt s' = Reply.token (seatAt W.hS iU3).toSeat sHead ∧ sHead.req = s'.req

/-- The sentence reads of the record its request's words alone. -/
theorem lookCalls_req (W : OnBytes.Model.Verify.Public) (tab : Nat → Nat) (s t : S) (y : Nat)
    (c : NCells) (h : t.req = s.req) (hl : LookCallsAt W tab s y c) : LookCallsAt W tab t y c := by
  have e : requestOf t = requestOf s := by
    unfold requestOf S.tokv S.rowR S.rowE S.reqT
    rw [h]
  unfold LookCallsAt at hl ⊢
  rw [e]
  exact hl

/-- **From the block as it rides**, under Moved. -/
theorem k07MeansFromStep (W : OnBytes.Model.Verify.Public) (l firstTree iU3 work : Nat)
    (tab : Nat → Nat) (c : NCells) (s s' sHead sEnd : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (n : Nat) (g : Given) (T r e asked : Nat)
    (hstep : (Reply.blockOf W l).step firstTree s rs cols = .ok (s', n))
    (hm : Moved W iU3 s' sHead)
    (hrep : (seatAt W.hS iU3).reply sHead = (seatAt W.hS iU3).reply sEnd)
    (hg : given (parOf W.hS work) (seatAt W.hS iU3) sHead = .ok g)
    (hfin : Reply.fin W.hS.V T r e asked (seatAt W.hS iU3).toSeat sEnd = true)
    (hlook : ∃ y, Reply.token (seatAt W.hS iU3).toSeat sHead = some y ∧
      LookCallsAt W tab sHead y c) :
    Reply.token Reply.seatAt s' = some asked ∧ K7In W tab s c asked ∧ asked < W.hS.V ∧
      (e < T → asked = 0) := by
  obtain ⟨a1, a2, a3⟩ := k07Means W iU3 work tab c sHead sEnd g T r e asked hrep hg hfin hlook
  obtain ⟨_, _, y, hy, _, hrow⟩ := Came.rowReply W l firstTree s tab c rs cols s' n hstep
  have h4 := (given_letters hg).2.2.2
  have h1 := ((k07Law S (seatAt W.hS iU3) (fun _ _ => rfl) (parOf W.hS work) T r e asked).2 sHead
    sEnd g hrep hg hfin).1
  have hya : y = asked := by
    have e1 := hm.1
    rw [hy, h4] at e1
    exact (Option.some.inj e1).trans h1
  subst hya
  exact ⟨hy, hrow ⟨y, hy, lookCalls_req W tab sHead s' y c hm.2.symm a1⟩, a2, a3⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k07Means
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k07MeansFromStep
