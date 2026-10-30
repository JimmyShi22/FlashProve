-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameOpened.lean: what "opened" leaves of the record, AT EVERY ROW of the
frame's value framesOf, whichever sort of link: one lemma over all four arms (framesOf_arms,
FrameRows.lean), for whoever meets the step as "f.opened" of a row.

  OpenedKeeps m u    u.st = m.st, and the like of book, roots, rowsOwed, failed, req: what
                     OpenedLeaves (FrameGives.lean) and the head's row's identity have in common
  opened_keeps       framesOf ... = .ok fs, fs[l]? = some f, f.opened m = .ok u: OpenedKeeps m u
  opened_leaves      where the link's record is not the head's (kind 2): OpenedLeaves m u, whole
                     (with u.check = m.check and u.live = m.check)
  opened_at_link     there too: a yes only where m.check.frame.link = l

No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameRows
import Johnson.Top.H0.Walk.FrameTiedRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf framesOf_arms)

/-- What every row's "opened" leaves, the head's among them. -/
def OpenedKeeps (m u : S) : Prop :=
  u.st = m.st ∧ u.book = m.book ∧ u.roots = m.roots ∧ u.rowsOwed = m.rowsOwed ∧
    u.failed = m.failed ∧ u.req = m.req

theorem keeps_of_leaves {m u : S} (h : OpenedLeaves m u) : OpenedKeeps m u :=
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- Where the link's record is not the head's: OpenedLeaves, whole. -/
theorem opened_leaves {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} {f : LinkFrame} {l : Nat} (h : framesOf built first W = .ok fs)
    (hf : fs[l]? = some f) {X : Stages.LinkH} (hX : built[l]? = some X) (hk : X.kind ≠ 2)
    {m u : S} (hy : f.opened m = .ok u) : OpenedLeaves m u := by
  rcases framesOf_arms h hf with ⟨X', hX', hk', _⟩ | ⟨_, _, _, Q, _, _, _, _, _, e, _⟩ |
    ⟨_, _, _, Q, _, _, _, _, _, e, _⟩ | ⟨_, _, _, Q, _, _, _, _, _, e, _⟩
  · rw [hX] at hX'
    obtain rfl : X = X' := Option.some.inj hX'
    exact absurd hk' hk
  · rw [e] at hy
    exact (openedZeroGives Q _ _ m u hy).2.2.1
  · rw [e] at hy
    exact (openedAttGives Q m u hy).2.2.1
  · rw [e] at hy
    exact (openedLayGives Q m u hy).2.2.1

/-- Where the link's record is not the head's: "opened" says yes only where the chain's own state of
the calls stands at link l. -/
theorem opened_at_link {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} {f : LinkFrame} {l : Nat} (h : framesOf built first W = .ok fs)
    (hf : fs[l]? = some f) {X : Stages.LinkH} (hX : built[l]? = some X) (hk : X.kind ≠ 2)
    {m u : S} (hy : f.opened m = .ok u) : m.check.frame.link = l := by
  rcases framesOf_arms h hf with ⟨X', hX', hk', _⟩ | ⟨h0, _, _, Q, _, _, _, _, _, e, _⟩ |
    ⟨_, _, _, Q, _, _, _, eQ, _, e, _⟩ | ⟨_, _, _, Q, _, _, _, eQ, _, e, _⟩
  · rw [hX] at hX'
    obtain rfl : X = X' := Option.some.inj hX'
    exact absurd hk' hk
  · rw [e] at hy
    rw [h0]
    exact (Law.openLayZero_ok hy).2.2.1
  · rw [e] at hy
    have h4 := (Law.openAtt_ok hy).2.2.2.1
    rw [eQ] at h4
    exact h4
  · rw [e] at hy
    have h4 := (Law.openLay_ok hy).2.2.2.1
    rw [eQ] at h4
    exact h4

/-- **At every row.** -/
theorem opened_keeps {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} {f : LinkFrame} {l : Nat} (h : framesOf built first W = .ok fs)
    (hf : fs[l]? = some f) {m u : S} (hy : f.opened m = .ok u) : OpenedKeeps m u := by
  rcases framesOf_arms h hf with ⟨X', _, _, e⟩ | ⟨_, _, _, Q, _, _, _, _, _, e, _⟩ |
    ⟨_, _, _, Q, _, _, _, _, _, e, _⟩ | ⟨_, _, _, Q, _, _, _, _, _, e, _⟩
  · subst e
    obtain rfl : m = u := Except.ok.inj hy
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [e] at hy
    exact keeps_of_leaves (openedZeroGives Q _ _ m u hy).2.2.1
  · rw [e] at hy
    exact keeps_of_leaves (openedAttGives Q m u hy).2.2.1
  · rw [e] at hy
    exact keeps_of_leaves (openedLayGives Q m u hy).2.2.1

#print axioms opened_leaves
#print axioms opened_at_link
#print axioms opened_keeps

end Johnson.Desc.First.Walk.Tied
