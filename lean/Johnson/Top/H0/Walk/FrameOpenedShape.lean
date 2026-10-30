-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/FrameOpenedShape.lean: BEHIND "link l: opened", at every row of the frame's
value but the head's: where the chain stands, which link is open, and that the count of rows that
wait is as it was: what the table's test on the stand (shapeAt, Johnson/Desc/First/Borders.lean)
reads.

  opened_shape      the open link's number is l; rowsOwed is as it was; the stand is "in a link", of
                    the sort that the kind in the link's planned entry names (0: layers; 1:
                    attention)

No soundness statement.

-/
import Johnson.Top.H0.Walk.FrameOpened

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S ModelPart Stand standOf)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf framesOf_arms)

theorem opened_shape {built : Array Stages.LinkH} {first : Params.First} {W : Verify.Public}
    {fs : List LinkFrame} {f : LinkFrame} {l : Nat} (h : framesOf built first W = .ok fs)
    (hf : fs[l]? = some f) {X : Stages.LinkH} (hX : built[l]? = some X) (hk : X.kind ≠ 2)
    {m u : S} (hy : f.opened m = .ok u) :
    (∃ L, u.link? = some L ∧ L.link = l) ∧ u.rowsOwed = m.rowsOwed ∧
      ((X.kind = 0 ∧ standOf u = Stand.link ModelPart.layers) ∨
        (X.kind = 1 ∧ standOf u = Stand.link ModelPart.attention)) := by
  rcases framesOf_arms h hf with
    ⟨X', hX', hk', _⟩ | ⟨h0, X', _, Q, hX', hk', _, eQ, _, e1, _⟩ |
    ⟨_, X', _, Q, hX', hk', _, eQ, _, e1, _⟩ | ⟨_, X', _, Q, hX', hk', _, eQ, _, e1, _⟩
  · obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
    exact absurd hk' hk
  · subst h0
    obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
    rw [e1] at hy
    obtain ⟨g1, g2, g3, _⟩ := openedZeroGives Q _ _ m u hy
    exact ⟨g2, g3.2.2.2.2.2.1, Or.inl ⟨hk', g1⟩⟩
  · obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
    rw [e1] at hy
    obtain ⟨g1, g2, g3, _⟩ := openedAttGives Q m u hy
    rw [eQ] at g2
    exact ⟨g2, g3.2.2.2.2.2.1, Or.inr ⟨hk', g1⟩⟩
  · obtain rfl : X = X' := Option.some.inj (hX.symm.trans hX')
    rw [e1] at hy
    obtain ⟨g1, g2, g3, _⟩ := openedLayGives Q m u hy
    rw [eQ] at g2
    exact ⟨g2, g3.2.2.2.2.2.1, Or.inl ⟨hk', g1⟩⟩

#print axioms opened_shape

end Johnson.Desc.First.Walk.Tied
