-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/WoRowSameFirst.lean: THE FIRST GROUP's SENTENCE ON THE ROW OF THE WEIGHTS' OPENING
(`Plan4KF.WoRowF`, Johnson/Road/K4/CloseK5First.lean) IS THE LATER GROUPS' (`Plan4K.WoRow`,
Johnson/Road/K4/CloseK5.lean) AT THE LETTERS THAT THE FIRST GROUP's VALUE SHARES WITH A LATER
GROUP's. The two texts part in the plan alone: the first group's has one slot number more (f7 + 1:
`Plan4LF.planF`, ValueSlotsFirst.lean); the sentence reads the entry of the index-mask message (c7,
which is at v7) and the committed matrix: neither reads f7. Three theorems, by steps at a plan that
is a letter. No draw, no count.

  `Plan4.ixAt_f7`: the message's entry at c7 reads no slot number f7.
  `Plan4.Wn_f7`: nor does the committed matrix off a tuple.
  `Plan4KF.woRowF_iff`: `QK.WoRowF par o m ↔ QK.toPlan4K.WoRow par o m`.

OBJECT: none of its own. USER: none here; meant: whoever has the later groups' sentence at the
shared letters and owes the first group's filling's letter wo. LETTERS: QK, par, o, m: free.

Limits. K04_law IS NOT PROVED BY THIS. It says that two sentences are one; it pays neither.

-/
import Johnson.Road.K4.CloseK5First
import Johnson.Road.K4.CloseK5

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par)
open Inst.Model (Scl)

/-- The message's entry at c7 reads no slot number f7. -/
theorem Plan4.ixAt_f7 {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (Q : Plan4 E M X)
    (n : ℕ) (m : M) :
    ({ Q with f7 := n } : Plan4 E M X).full.msg m ({ Q with f7 := n } : Plan4 E M X).full.c7 =
      Q.full.msg m Q.full.c7 := rfl

/-- Nor does the committed matrix off a tuple. -/
theorem Plan4.Wn_f7 {E : Type} [Field E] [Fintype E] [scl : Scl] {M X : Type} (Q : Plan4 E M X)
    (n : ℕ) (m : M) :
    ({ Q with f7 := n } : Plan4 E M X).full.Wn (({ Q with f7 := n } : Plan4 E M X).full.msg m) =
      Q.full.Wn (Q.full.msg m) := by
  funext r c
  show ({ Q with f7 := n } : Plan4 E M X).Wn (({ Q with f7 := n } : Plan4 E M X).msg m) r c =
    Q.Wn (Q.msg m) r c
  unfold Plan4.Wn
  by_cases h : r < Q.hW ∧ c < 2 ^ Q.kW
  · have h' : r < ({ Q with f7 := n } : Plan4 E M X).hW ∧
        c < 2 ^ ({ Q with f7 := n } : Plan4 E M X).kW := h
    rw [dif_pos h', dif_pos h]
    rfl
  · have h' : ¬ (r < ({ Q with f7 := n } : Plan4 E M X).hW ∧
        c < 2 ^ ({ Q with f7 := n } : Plan4 E M X).kW) := h
    rw [dif_neg h', dif_neg h]

/-- **The two sentences on the row are one.** -/
theorem Plan4KF.woRowF_iff [scl : Scl] {Mm T : Type} (QK : Plan4KF Mm T) (par : Par) (o : Own)
    (m : Mm) : QK.WoRowF par o m ↔ QK.toPlan4K.WoRow par o m := by
  have e1 : QK.toLF.planF.fullF.msg m QK.toLF.planF.fullF.c7 =
      QK.toPlan4K.toL.plan.full.msg m QK.toPlan4K.toL.plan.full.c7 :=
    Plan4.ixAt_f7 QK.toPlan4K.toL.plan (QK.toPlan4K.toL.slots.f7 + 1) m
  have e2 : QK.toLF.planF.fullF.Wn (QK.toLF.planF.fullF.msg m) =
      QK.toPlan4K.toL.plan.full.Wn (QK.toPlan4K.toL.plan.full.msg m) :=
    Plan4.Wn_f7 QK.toPlan4K.toL.plan (QK.toPlan4K.toL.slots.f7 + 1) m
  unfold Plan4KF.WoRowF Plan4K.WoRow
  rw [e1, e2]

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4.ixAt_f7
#print axioms OnBytes.Road.K4.Plan4.Wn_f7
#print axioms OnBytes.Road.K4.Plan4KF.woRowF_iff
