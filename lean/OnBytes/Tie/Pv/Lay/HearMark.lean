-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/HearMark.lean: the mark of a failed test on values, along the stages that the
verifier's routines for a layers' sub-proof have heard (OnBytes/Tie/Pv/Lay/HearL.lean): if no mark
stands behind the stages, none stood before them, nor between them.

A failed test on values does not end a routine: it is marked in the context (`Blk.check`,
OnBytes/Iop/Ground.lean), and the file is refused at the end. So a statement that wants a test's
outcome in the midst of a routine has to carry "no mark" back from the end.

Main names:
  `keeps_mark`: a call that neither reads nor turns the mark (`Slides`,
    OnBytes/Tie/Pv/Lay/Slides.lean) leaves it as it was.
  `parts_mark`: so does a whole masked sumcheck's hearing.
  `heardL_mark`: if the stages were heard from c to c' and no mark stands at c', none stands at c.
  `heardL_mark_split`: the same at the context between two lists of stages.

Limits: one direction. That a test held is not said here: only that no mark stood.
-/
import OnBytes.Tie.Pv.Lay.HearL
import OnBytes.Tie.Pv.Lay.Slides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay
open OnBytes OnBytes.Model OnBytes.Model.Road
open OnBytes.Psc (Weight hearMany hearOne)

/-- A call that neither reads nor turns the mark leaves it as it was. -/
theorem keeps_mark {α : Type} {b : Blk α} (h : Slides b) {c c' : Ctx} {a : α}
    (hy : b.Yields c a c') : c'.failed = c.failed := by
  obtain ⟨c0, _, e⟩ := h c c.notes c.failed a c' hy
  rw [e]
  rfl

theorem requireRows_mark {rows : Nat} {c c' : Ctx} (hy : (Blk.requireRows rows).Yields c () c') :
    c'.failed = c.failed := by
  rw [Blk.yields_iff] at hy
  unfold Blk.requireRows at hy
  split at hy
  · split at hy
    · rw [← (Prod.mk.inj (Except.ok.inj hy)).2]
    · cases hy
  · cases hy

/-- A whole masked sumcheck's hearing. -/
theorem parts_mark {c c1 c' : Ctx} {riders : List E} {mu eps : E} {ws : List Weight}
    {rs : List (List E × E)} {dY : Nat} {sentY : List E} {beta : E} {v : List E}
    (a : Parts c c1 c' riders mu eps ws rs dY sentY beta v) : c'.failed = c.failed := by
  obtain ⟨c2, c3, c4, c5, h0, h1, h2, h3, h4, h5⟩ := a
  rw [keeps_mark (slides_closeEmpty _) h5, keeps_mark (slides_recvEs _) h4,
    keeps_mark (slides_hearOne _ _ _ _) h3, keeps_mark (slides_hearMany _) h2,
    keeps_mark (slides_hearOne _ _ _ _) h1, keeps_mark (slides_recvEs _) h0]

/-- No mark behind the stages: none before them. -/
theorem heardL_mark : ∀ (l : List StageL) (c c' : Ctx), HeardL l c c' → c'.failed = none →
    c.failed = none
  | [], c, c', h, h' => by
    rw [show c' = c from h] at h'
    exact h'
  | .sum _ _ _ _ :: l, c, c', h, h' => by
    obtain ⟨c1, c2, h1, h2⟩ := h
    rw [← parts_mark h1]
    exact heardL_mark l c2 c' h2 h'
  | .bat _ _ _ :: l, c, c', h, h' => by
    obtain ⟨c1, c2, c3, h1, h2, h3, h4⟩ := h
    rw [← keeps_mark (slides_recvEs _) h1, ← keeps_mark (slides_closeOne _ _ _) h2,
      ← requireRows_mark h3]
    exact heardL_mark l c3 c' h4 h'
  | .point _ _ :: l, c, c', h, h' => by
    obtain ⟨c1, h1, h2⟩ := h
    rw [← keeps_mark (slides_close _ _ _) h1]
    exact heardL_mark l c1 c' h2 h'
  | .line _ :: l, c, c', h, h' => by
    obtain ⟨c1, h1, h2⟩ := h
    rw [← keeps_mark (slides_closeOne _ _ _) h1]
    exact heardL_mark l c1 c' h2 h'
  | .idle :: l, c, c', h, h' => by
    obtain ⟨c1, h1, h2⟩ := h
    exact h1.mark (heardL_mark l c1 c' h2 h')

/-- The same at the context between two lists of stages. -/
theorem heardL_mark_split (l l' : List StageL) (c c1 c' : Ctx) (h : HeardL l c c1)
    (h' : HeardL l' c1 c') (hm : c'.failed = none) : c1.failed = none ∧ c.failed = none :=
  ⟨heardL_mark l' c1 c' h' hm, heardL_mark l c c1 h (heardL_mark l' c1 c' h' hm)⟩

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.keeps_mark
#print axioms OnBytes.Tie.Pv.Lay.parts_mark
#print axioms OnBytes.Tie.Pv.Lay.heardL_mark
#print axioms OnBytes.Tie.Pv.Lay.heardL_mark_split
