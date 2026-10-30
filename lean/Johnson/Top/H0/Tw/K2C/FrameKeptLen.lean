-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/FrameKeptLen.lean: code switching (the kind K2): THE FRAME AT A FRONT HAS
ONE KEPT PLACE FOR EACH KEPT SHAPE OF THE TARGET: from "the frame is there" alone. Three theorems.
No sub-protocol imports this file.
Why. `frame_kept_rows` (Johnson/Top/H0/Tw/K2C/PositionCount.lean) has the kept places' main rows,
place by place, under the public test on the target and `KeptOld`. Whoever wants their NUMBER
alone needs neither: `switchFrame` (OnBytes/Iop/Cs.lean) lays one kept place for each member of
`switchKept old`, behind its own guard "as many new oracle messages as kept members"; and
`frameAt` (Johnson/Top/H0/K2Hands/FrameOfFront.lean) hands it, for the new messages, the numbers 1
to `x.T.kept.size` of what the sending returns, which has room for them by the make of
`switchNotices`.
  `ids_size`: the sending returns 1 + the target's kept shapes + the others' numbers.
  `anew_size`: so the stretch that `frameAt` hands on has just `x.T.kept.size` members.
  `frame_kept_len`: **`frameAt x = some W → W.kept.length = x.T.kept.size`.**
Limits. A count alone: nothing on which message a kept place names. No probability: no soundness
follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.H0.K2Hands.FrameOfFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open _root_.Tw.K2 (switchNotices)

/-- The sending returns one number for the target, one for each kept shape, one for each other. -/
theorem ids_size (x : _root_.Tw.K2.Front) :
    (idsOf x).size = 1 + x.T.kept.size + x.others.size := by
  unfold idsOf switchNotices
  simp
  omega

/-- The stretch that `frameAt` hands on for the new messages. -/
theorem anew_size (x : _root_.Tw.K2.Front) :
    ((idsOf x).extract 1 (1 + x.T.kept.size)).size = x.T.kept.size := by
  rw [Array.size_extract, ids_size]
  omega

/-- **The frame at a front has one kept place for each kept shape of the target.** -/
theorem frame_kept_len {x : _root_.Tw.K2.Front} {W : SwitchFrame} (hW : frameAt x = some W) :
    W.kept.length = x.T.kept.size := by
  unfold frameAt switchFrame at hW
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hW
  obtain ⟨_, _, _, _, _, _, _, hg, rfl⟩ := hW
  simp [guard] at hg
  simp only [List.length_map, List.length_range]
  rw [← hg, ids_size]
  omega

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.ids_size
#print axioms VerifiableInference.Desc.First.K2.anew_size
#print axioms VerifiableInference.Desc.First.K2.frame_kept_len
