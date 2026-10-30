--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/Walk/FrameCarryReads.lean: WHAT THE CODE SWITCH's FRONT READS OF THE VERIFIER's STATE
AT A LINK (`K2.frontAt`, Johnson/Top/H0/K2Hears/Long.lean), AGAINST WHAT AN ACCEPTING "cleared"
TURNS (`ClearedRec`, FrameGives.lean). The carried word's sentence, as it is filled
(Johnson/Top/H0/K2Caller/CarryK2.lean: `carryRow`), begins "there is a front fx with
`K2.frontAt p t = some fx`": so where the front is refused the sentence is false, and where the
front is another the sentence is another.

What is said.
  `frontAt_link`: at a place that stands at a link the front is `firstFront s.st s.check.frame`: IT
    READS THE WALK's COPY OF THE CALLS' STATE (s.check), not the live one (s.live).
  `frontAt_none_zero`: **where that copy stands at link 0 the front is refused.**
  `frontAt_some`: where it answers: a first message is due in that copy; the copy's link is not 0;
    THE FRONT's TARGET IS THAT OF THE GROUP OF THE COPY's OWN LINK, and the front's frame stands at
    that link.
  `frontAt_cleared`: behind an accepting "cleared" the front is `firstFront t.st s.live.frame`: the
    frame of the link's own copy in front.
  `frontAt_live`: where no link is open the two copies are one: reading the live copy turns nothing
    at the switch's own border.
  `firstBehind_next`, `switch_next`: **behind an accepting switch at a link the walk's copy says "a
    later message or the close is due"**, not "a first message".
  `frontAt_none_next`, `frontAt_none_behind_switch`: **so the front is refused at the state behind
    the link's own switch, and at every later state whose walk's copy is still that one.**

Limits. Nothing here names the carried word's sentence itself: its file is not in this file's
ground. THAT NO SUB-PROTOCOL INSIDE A LINK TURNS THE WALK's COPY (they write through `S.putLive`,
which writes the link's own where a link is open) IS READ OFF THE STATE's TEXT: NOT SHOWN HERE ALONG
A RUN. No soundness statement.

-/
import Johnson.Top.H0.K2Hears.Long
import Johnson.Top.H0.Walk.FrameTiedRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (P2 frontAt)
open _root_.Tw.K2 (firstFront Front)

/-- At a link the front reads the statement and the walk's copy's frame. -/
theorem frontAt_link {p : P2} (hp : p.stands = .link) (s : S) :
    frontAt p s = (firstFront s.st s.check.frame).toOption := by
  unfold frontAt
  rw [hp]

/-- **Where the walk's copy stands at link 0 the front is refused.** -/
theorem frontAt_none_zero {p : P2} (hp : p.stands = .link) {s : S}
    (h0 : s.check.frame.link = 0) : frontAt p s = none := by
  rw [frontAt_link hp]
  unfold firstFront
  split
  · rfl
  · rw [h0]
    rfl

/-- Where the front answers. -/
theorem frontAt_some {p : P2} (hp : p.stands = .link) {s : S} {fx : Front}
    (h : frontAt p s = some fx) :
    s.check.frame.next = .first ∧ s.check.frame.link ≠ 0 ∧ fx.f.link = s.check.frame.link ∧
      (s.check.frame.groups[s.check.frame.link]?).map (·.target) = some fx.T := by
  rw [frontAt_link hp] at h
  unfold firstFront at h
  split at h
  · cases h
  · rename_i h1
    split at h
    · cases h
    · rename_i h2
      split at h
      · rename_i L G hL hG
        dsimp only at h
        split at h
        · cases h
        · rename_i S' g hg
          obtain rfl : _ = fx := Option.some.inj h
          refine ⟨by simpa using h1, by simpa using h2, rfl, ?_⟩
          rw [hG]
          rfl
      · cases h
      · cases h

/-- Behind an accepting "cleared": the frame of the link's own copy in front. -/
theorem frontAt_cleared {p : P2} (hp : p.stands = .link) {L : LinkPub}
    {left : S → Option WsForkOut} {lay : WsLay} {lin : Params.LinShape} {s t : S}
    (h : ClearedRec L left lay lin s t) :
    frontAt p t = (firstFront t.st s.live.frame).toOption := by
  rw [frontAt_link hp, h.2.1]

/-- Where no link is open the two copies are one. -/
theorem frontAt_live {p : P2} (hp : p.stands = .link) {s : S} (hl : s.link? = none) :
    frontAt p s = (firstFront s.st s.live.frame).toOption := by
  rw [frontAt_link hp]
  unfold S.live
  rw [hl]

/-- What stands behind a later link's switch: no first message is due any more. -/
theorem firstBehind_next {S0 S' : Statement} {x : Front} {sw : Switched}
    {plain : List E} {f : ReqFrame} {mine : Array Nat}
    (h : _root_.Tw.K2.firstBehind S0 x sw plain = .ok (S', f, mine)) : f.next = .laterOrClose := by
  unfold _root_.Tw.K2.firstBehind at h
  dsimp only at h
  repeat' split at h
  all_goals first | (cases h; done) | skip
  cases h
  rfl

/-- **Behind an accepting switch at a link.** -/
theorem switch_next {snd : _root_.Tw.K2.SendFn} {p : P2} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hp : p.stands = .link)
    (h : VerifiableInference.Desc.First.K2.decideWith snd p s rs gs = .ok s') :
    s'.check.frame.next = .laterOrClose := by
  obtain ⟨r₁, r₂, x, w, roots, S', f, mine, -, hl⟩ :=
    VerifiableInference.Desc.First.K2.link_inv hp h
  rw [hl.hOut]
  exact firstBehind_next hl.hBehind

/-- Where the walk's copy says that no first message is due the front is refused. -/
theorem frontAt_none_next {p : P2} (hp : p.stands = .link) {s : S}
    (h : s.check.frame.next = .laterOrClose) : frontAt p s = none := by
  cases hf : frontAt p s with
  | none => rfl
  | some fx =>
    have h1 := (frontAt_some hp hf).1
    rw [h] at h1
    cases h1

/-- **The front is refused at every state whose walk's copy is the one that the link's own switch
left.** q: any place that stands at a link (the next link's switch's). -/
theorem frontAt_none_behind_switch {snd : _root_.Tw.K2.SendFn} {p q : P2} {s s' u : S}
    {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))} (hp : p.stands = .link)
    (hq : q.stands = .link)
    (h : VerifiableInference.Desc.First.K2.decideWith snd p s rs gs = .ok s')
    (hu : u.check = s'.check) : frontAt q u = none :=
  frontAt_none_next hq (by rw [hu]; exact switch_next hp h)

end Johnson.Desc.First.Walk.Tied

#print axioms Johnson.Desc.First.Walk.Tied.switch_next
#print axioms Johnson.Desc.First.Walk.Tied.frontAt_none_next
#print axioms Johnson.Desc.First.Walk.Tied.frontAt_none_behind_switch
#print axioms Johnson.Desc.First.Walk.Tied.frontAt_link
#print axioms Johnson.Desc.First.Walk.Tied.frontAt_none_zero
#print axioms Johnson.Desc.First.Walk.Tied.frontAt_some
#print axioms Johnson.Desc.First.Walk.Tied.frontAt_cleared
#print axioms Johnson.Desc.First.Walk.Tied.frontAt_live
