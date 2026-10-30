-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/CutSame.lean: the proof of the statement `OwedCutSame`
(Johnson/Desc/K13/Law/OwedCutSame.lean): of a row whose mask entries all lie within their tables,
kind K13's reader with the mask entries cut to the table (`maskCut`,
Johnson/Desc/K13/Law/ReaderByBook.lean) and the plain reader (`witOf`,
Johnson/Desc/K13/Law/Eval.lean) say the same. Two theorems.
Main names:
  `formVal_cut`: the row's mask form has one value at the two readers of mask entries: it reads the
    entries that the row names and no other, and there the cut gives the words' own entry.
  `cutSame`: **the statement**: the two witnesses have one matrix, so the rows' left sides are one.
Who spends it: the joints at which other files' sentence at the uncut reader meets "all rows on
the table are true" at ours.

What is not claimed. That any row's entries lie within their tables. Nothing on soundness.

-/
import Johnson.Desc.K13.Law.OwedCutSame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Means (Words tableSize)

/-- The mask form of entries that lie within their tables has one value at the two readers. -/
theorem formVal_cut (st : Statement) (m : Words GE) (f : MaskForm)
    (h : ∀ t ∈ f, t.1.index < tableSize st t.1.oracle .mask) :
    formVal ρg (maskCut st m) f = formVal ρg (maskOf m) f := by
  unfold formVal
  refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
  show ρg.val t.2 *
      (if t.1.index < tableSize st t.1.oracle .mask then m t.1.oracle .mask t.1.index else 0) =
    ρg.val t.2 * m t.1.oracle .mask t.1.index
  rw [if_pos (h t ht)]

/-- **The cut reader and the plain one say the same of a row whose mask entries lie within their
tables.** -/
theorem cutSame : OwedCutSame := by
  intro st m nR k mat r h
  have e : lhs ρg (⟨mat, maskCut st m⟩ : Wit GE nR k) r = lhs ρg (witOf mat m) r := by
    unfold lhs
    show _ + formVal ρg (maskCut st m) r.masks = _ + formVal ρg (maskOf m) r.masks
    rw [formVal_cut st m r.masks h]
    rfl
  unfold Holds
  rw [e]

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.formVal_cut
#print axioms VerifiableInference.Desc.K13.Law.cutSame
