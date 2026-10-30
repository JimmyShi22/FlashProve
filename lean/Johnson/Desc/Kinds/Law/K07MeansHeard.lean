-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/K07MeansHeard.lean: A RIDER TO Law/K07Means.lean: ITS NAMED PREMISE Moved
(the token at the next token's own seat behind K7's step is the token at
out.reply where the head takes its letters) IS HAD OF THE ONE READING S.heard
(Johnson/Desc/First/StateHeard.lean: out.reply at every record): so what is owed between
K7's step and the head's record has this form: EVERY BLOCK BETWEEN LEAVES S.heard (Sound/FoldHeard.lean: Block.Leaves; FoldLeaves carries it over a fold).
S.heard is out.reply at every record: heard_where_given's proof is rfl, and its premise is idle.
  heard_front_none     IN FRONT of a yes of the seated next token's block: S.heard s = none (for the first arm of RepFact, Desc/Sound/LeadsQ.lean: K7's OWN TEXT refuses where something was heard already).     heard_behind_some    behind it: a token of the vocabulary.
  heard_behind_reply   behind a yes of the seated next token's block: S.heard s' is what that block's own seat holds.
  heard_where_given    where the head's letters are read (given returns): S.heard sHead is out.reply: what the head's seat holds.
  moved_of_heard       S.heard sHead = S.heard s' and the request's words the same ⇒ Moved.
  k07MeansFromHeard    Law/K07Means.lean's k07MeansFromStep with these two equations in Moved's place.
EVERY LETTER UNDER "THERE IS": heard_behind_some's x: pinned by S.heard s' = some x; none in the other tops. UNDER "FOR ALL" IN k07MeansFromHeard: as in k07MeansFromStep: tab, c: letters, tied to nothing · l, firstTree, cols, n: read by the step alone · work: by given alone.
WHAT IT IS NOT. THAT THE BLOCKS BETWEEN LEAVE S.heard AND THE REQUEST's WORDS: NOT SHOWN HERE: ours do (Law/HeardName.lean: K6's block; K7's LAYS it); that the place which OPENS the link (K2.headOpenQ) leaves it is not shown here either: it lays a record literal, which StateHeard.lean's laws do not cover; of the
flat list's entries from 339 on IM.later_leaves (IMR/TokAtReach.lean) has it, under the scope and an
opening at the second hash function. All other lacks of Law/K07Means.lean's head stand: "the
witness's token" is the last test's letter "asked"; no join to tieRow. Nothing on soundness.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.K07Means
import Johnson.Desc.First.StateHeard

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc.First (S)

/-- Behind a yes of the seated next token's block the one reading is what that block's seat holds. -/
theorem heard_behind_reply (l V : Nat) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : (Reply.blockAt l V).decide s rs gs = .ok s') :
    S.heard s' = Reply.seatAt.reply s' := by
  obtain ⟨o, x, _, hop, _, _, rfl⟩ := Came.reply_record l V hd
  simp [S.heard, Reply.seatAt, hop]

/-- **IN FRONT OF A YES OF THE SEATED NEXT TOKEN's BLOCK NOTHING WAS HEARD**: the block's own text refuses where something was ("heard once"), and outside the entered, unopened head's link. -/
theorem heard_front_none (l V : Nat) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : (Reply.blockAt l V).decide s rs gs = .ok s') :
    S.heard s = none := by
  obtain ⟨o, x, ho, hop, hn, _, _⟩ := Came.reply_record l V hd
  simp [S.heard, ho, hop, hn]

/-- And behind it a token of the vocabulary is heard. -/
theorem heard_behind_some (l V : Nat) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : (Reply.blockAt l V).decide s rs gs = .ok s') :
    ∃ x, S.heard s' = some x ∧ OnBytes.Desc.Reply.isToken V x = true := by
  obtain ⟨o, x, _, hop, _, ht, rfl⟩ := Came.reply_record l V hd
  exact ⟨x, by simp [S.heard, hop], ht⟩

/-- Where the head's letters are read the one reading is out.reply. -/
theorem heard_where_given (h : OnBytes.Model.Head.Shape) (iU3 : Nat) (p : Par) {s : S} {g : Given}
    (hg : given p (seatAt h iU3) s = .ok g) : S.heard s = (seatAt h iU3).reply s := by
  have _ := hg
  rfl

/-- **Moved, of the one reading.** -/
theorem moved_of_heard (W : OnBytes.Model.Verify.Public) (l iU3 work : Nat) {s s' sHead : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} {g : Given}
    (hd : (Reply.blockOf W l).decide s rs gs = .ok s')
    (hg : given (parOf W.hS work) (seatAt W.hS iU3) sHead = .ok g)
    (hh : S.heard sHead = S.heard s') (hr : sHead.req = s'.req) : Moved W iU3 s' sHead := by
  refine ⟨?_, hr⟩
  have e1 : S.heard s' = Reply.seatAt.reply s' := heard_behind_reply l W.hS.V hd
  have e2 := heard_where_given W.hS iU3 (parOf W.hS work) hg
  unfold Reply.token
  rw [← e1, ← hh, e2]

/-- **From the block as it rides**, under the one reading's equation. -/
theorem k07MeansFromHeard (W : OnBytes.Model.Verify.Public) (l firstTree iU3 work : Nat)
    (tab : Nat → Nat) (c : NCells) (s s' sHead sEnd : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn)
    (n : Nat) (g : Given) (T r e asked : Nat)
    (hstep : (Reply.blockOf W l).step firstTree s rs cols = .ok (s', n))
    (hh : S.heard sHead = S.heard s') (hr : sHead.req = s'.req)
    (hrep : (seatAt W.hS iU3).reply sHead = (seatAt W.hS iU3).reply sEnd)
    (hg : given (parOf W.hS work) (seatAt W.hS iU3) sHead = .ok g)
    (hfin : Reply.fin W.hS.V T r e asked (seatAt W.hS iU3).toSeat sEnd = true)
    (hlook : ∃ y, Reply.token (seatAt W.hS iU3).toSeat sHead = some y ∧
      LookCallsAt W tab sHead y c) :
    Reply.token Reply.seatAt s' = some asked ∧ K7In W tab s c asked ∧ asked < W.hS.V ∧
      (e < T → asked = 0) := by
  obtain ⟨gs, hd⟩ := Came.step_decide firstTree (Reply.blockOf W l) s rs cols s' n hstep
  exact k07MeansFromStep W l firstTree iU3 work tab c s s' sHead sEnd rs cols n g T r e asked hstep
    (moved_of_heard W l iU3 work hd hg hh hr) hrep hg hfin hlook

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.heard_front_none
#print axioms VerifiableInference.Desc.Kinds.Head.Law.heard_behind_some
#print axioms VerifiableInference.Desc.Kinds.Head.Law.moved_of_heard
#print axioms VerifiableInference.Desc.Kinds.Head.Law.k07MeansFromHeard
