-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/TieK/RunAt.lean: the context from which the program runs a block on a view, as a term.

"The program" is the Lean program verify-on-bytes. It decides a chain by one run of the chain's
block on the view that the strict reader has returned (Blk.runOn, OnBytes/Iop/Ground.lean). A
statement that begins "if the check says yes, the block has run" says little as long as the context
from which it ran stands under "there is": one accepted file would make it true of every other. This
file names that context as a function of what the block starts from and of the view.

Main definitions: startCtx (the context), RanAt (what a run on a view that gave a value has done).
Main theorem: runOn_at.
RanAt lists: the codes' message lengths are powers of two; the block, run from startCtx s v, has
succeeded with the value and has left a context; no named test is marked as failed there; every
entry of the plan is used up and the last round's question on its rows is answered; no round, no
item and no opened column of the view is left over.
The context that is left stands under "there is" in runOn_at. A block is a function, so it is the
one context that the block gives from startCtx s v.

It claims nothing on soundness. The program does not import this file.
-/
import OnBytes.Iop.GroundLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK

/-- The context from which Blk.runOn runs a block: a run on a view (not dry), the plan's entries,
the view's rounds and opened columns, the statement and the book of trees of the start; no
intermediate values are kept; no named test is marked. -/
def startCtx (s : Start) (v : Fmt.View) : Ctx :=
  { ch := { dry := false, entries := s.entries, samples := s.samples, firstTree := s.firstTree,
            left := v.rounds, opened := v.opened },
    st := s.st, book := s.book, keepNotes := false }

theorem startCtx_view (s : Start) (v : Fmt.View) : (startCtx s v).ch.dry = false := rfl

theorem startCtx_clean (s : Start) (v : Fmt.View) : (startCtx s v).failed = none := rfl

/-- What a run of the block b on the view v, started from s, has done if it gave the value a and
left the context c'. -/
structure RanAt {α : Type} (b : Blk α) (s : Start) (v : Fmt.View) (a : α) (c' : Ctx) : Prop where
  codes : s.st.codes.lengthsOk = true
  run : b.Yields (startCtx s v) a c'
  clean : c'.failed = none
  plan_used : (c'.ch.entries.isEmpty && c'.ch.settled) = true
  view_used : (c'.ch.cur.isNone && c'.ch.opened.isEmpty && c'.ch.left.isEmpty) = true

/-- **A run on a whole view that gives a value**, with the context from which it started named. -/
theorem runOn_at {α : Type} {b : Blk α} {s : Start} {v : Fmt.View} {a : α}
    (h : b.runOn s v = .ok a) : ∃ c', RanAt b s v a c' := by
  unfold Blk.runOn at h
  split at h
  · cases h
  · rename_i a' c' hr
    split at h
    · cases h
    · rename_i hf
      split at h
      · cases h
      · rename_i hplan
        split at h
        · rename_i hview
          have ea : a' = a := Except.ok.inj h
          unfold Blk.runNamed at hr
          split at hr
          · rename_i hcodes
            refine ⟨c', hcodes, (Blk.yields_iff _ _ _ _).2 (by rw [← ea]; exact hr), hf, ?_, hview⟩
            cases hP : (c'.ch.entries.isEmpty && c'.ch.settled) with
            | true => rfl
            | false =>
              rw [hP] at hplan
              exact absurd rfl hplan
          · cases hr
        · cases h

end OnBytes.TieK
