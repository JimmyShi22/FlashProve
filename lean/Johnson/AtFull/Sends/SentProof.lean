-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Sends/SentProof.lean: at the proof file's 95 written sendings of the full size
(`proofSends0`, `proofSends1`, `proofSends2`, Johnson/G/SendsWritten.lean): the tags of their
labels, as three written lists; and: the `mapM` of `Johnson.G.OfPlan.sentAt` returns, at every name
and every offset.

  `tags_proofSends0`, `tags_proofSends1`, `tags_proofSends2`: BY THE KERNEL, behind the laws of
    Johnson/Unfolds/ on `String.splitOn` and `String.toNat?`, which `sendTag` calls.
  **`sent_proofSends0`**, **`sent_proofSends1`**, **`sent_proofSends2`**: by
    `Johnson.Unfolds.sent_of`; that the oracle messages can be placed in trees: BY THE KERNEL.
  Negative tests: `tag_none` (BY THE KERNEL): a label whose link's number is no number has no tag;
    `sent_no`: so `sentAt` refuses a sending with that label.

Limits. The full size alone. IT SPEAKS OF THE WRITTEN SENDINGS: that these are what `sendsOf`
(Johnson/G/Sends.lean) makes of any public files is not said here. WHICH trees `sentAt` returns is
not said: only that it returns. Nothing on soundness. On hiding nothing.

-/
import Johnson.Unfolds.SliceFoldl
import Johnson.Unfolds.SplitOn
import Johnson.Unfolds.SentLaw
import Johnson.G.SendsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Sends
open Johnson.G.OfPlan (SendTag TestTag sendTag)
open Johnson.Unfolds (sent_of)

/-- The 82 sendings of `proofSends0`. -/
theorem tags_proofSends0 :
    (Johnson.G.proofSends0.sends.map (·.label)).map sendTag =
      [some (.link 0 0), some (.link 0 1), some (.link 0 2), some (.link 1 0), some (.link 1 1),
       some (.link 1 2), some (.link 2 0), some (.link 2 1), some (.link 2 2), some (.link 3 0),
       some (.link 3 1), some (.link 3 2), some (.link 4 0), some (.link 4 1), some (.link 4 2),
       some (.link 5 0), some (.link 5 1), some (.link 5 2), some (.link 6 0), some (.link 6 1),
       some (.link 6 2), some (.link 7 0), some (.link 7 1), some (.link 7 2), some (.link 8 0),
       some (.link 8 1), some (.link 8 2), some (.link 9 0), some (.link 9 1), some (.link 9 2),
       some (.link 10 0), some (.link 10 1), some (.link 10 2), some (.link 11 0),
       some (.link 11 1), some (.link 11 2), some (.link 12 0), some (.link 12 1),
       some (.link 12 2), some (.link 13 0), some (.link 13 1), some (.link 13 2),
       some (.link 14 0), some (.link 14 1), some (.link 14 2), some (.link 15 0),
       some (.link 15 1), some (.link 15 2), some (.link 16 0), some (.link 16 1),
       some (.link 16 2), some (.link 17 0), some (.link 17 1), some (.link 17 2),
       some (.link 18 0), some (.link 18 1), some (.link 18 2), some (.link 19 0),
       some (.link 19 1), some (.link 19 2), some (.link 20 0), some (.link 20 1),
       some (.link 20 2), some (.link 21 0), some (.link 21 1), some (.link 21 2),
       some (.link 22 0), some (.link 22 1), some (.link 22 2), some (.link 23 0),
       some (.link 23 1), some (.link 23 2), some (.link 24 0), some (.link 24 1),
       some (.link 24 2), some (.link 25 0), some (.stage .last 1), some (.stage .last 2),
       some (.stage .last 3), some (.stage .last 4), some (.stage .last 5), some .w] := by
  unfold sendTag
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- The 9 sendings of `proofSends1`. -/
theorem tags_proofSends1 :
    (Johnson.G.proofSends1.sends.map (·.label)).map sendTag =
      [some .foldedRow, some .omega, some (.stage .folded 1), some (.stage .folded 2),
       some (.stage .folded 3), some (.stage .folded 4), some (.stage .omega 1),
       some (.stage .omega 2), some (.stage .omega 3)] := by
  unfold sendTag
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- The 4 sendings of `proofSends2`. -/
theorem tags_proofSends2 :
    (Johnson.G.proofSends2.sends.map (·.label)).map sendTag =
      [some (.stage .own 1), some (.stage .own 2), some (.stage .own 3), some (.stage .own 4)] := by
  unfold sendTag
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- The `mapM` of `sentAt` returns at `proofSends0`'s sendings, at every name and offset. -/
theorem sent_proofSends0 (at_ : String) (off : Nat) :
    (Johnson.G.proofSends0.sends.mapM
      (Johnson.G.OfPlan.sentAt at_ Johnson.G.proofSends0.codes off)).isOk = true :=
  sent_of at_ off _ _ tags_proofSends0 (by decide) (by decide +kernel)

/-- The `mapM` of `sentAt` returns at `proofSends1`'s sendings, at every name and offset. -/
theorem sent_proofSends1 (at_ : String) (off : Nat) :
    (Johnson.G.proofSends1.sends.mapM
      (Johnson.G.OfPlan.sentAt at_ Johnson.G.proofSends1.codes off)).isOk = true :=
  sent_of at_ off _ _ tags_proofSends1 (by decide) (by decide +kernel)

/-- The `mapM` of `sentAt` returns at `proofSends2`'s sendings, at every name and offset. -/
theorem sent_proofSends2 (at_ : String) (off : Nat) :
    (Johnson.G.proofSends2.sends.mapM
      (Johnson.G.OfPlan.sentAt at_ Johnson.G.proofSends2.codes off)).isOk = true :=
  sent_of at_ off _ _ tags_proofSends2 (by decide) (by decide +kernel)

/-- A negative test: a label whose link's number is no number has no tag. -/
theorem tag_none : sendTag "link x, moment 1" = none := by
  unfold sendTag
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- So `sentAt` refuses a sending with that label. -/
theorem sent_no (at_ : String) (codes : OnBytes.Codes) (off : Nat) (x : Johnson.G.Sending) :
    (Johnson.G.OfPlan.sentAt at_ codes off { x with label := "link x, moment 1" }).isOk = false :=
  Johnson.Unfolds.sentAt_no tag_none

end Johnson.AtFull.Sends

#print axioms Johnson.AtFull.Sends.tags_proofSends0
#print axioms Johnson.AtFull.Sends.tags_proofSends1
#print axioms Johnson.AtFull.Sends.tags_proofSends2
#print axioms Johnson.AtFull.Sends.sent_proofSends0
#print axioms Johnson.AtFull.Sends.sent_proofSends1
#print axioms Johnson.AtFull.Sends.sent_proofSends2
#print axioms Johnson.AtFull.Sends.tag_none
#print axioms Johnson.AtFull.Sends.sent_no
