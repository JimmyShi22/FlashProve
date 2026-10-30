-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/KeyBack/SentKey.lean: at the key file's 19 written sendings of the full size
(`keySends0`, `keySends1`, `keySends2`, Johnson/G/SendsWritten.lean): the tags of their labels, as
three written lists; and: the `mapM` of `Johnson.G.OfPlan.sentAt` returns, at every name and every
offset.

  `tags_keySends0`, `tags_keySends1`, `tags_keySends2`: BY THE KERNEL, behind the laws of
    Johnson/Unfolds/ on `String.splitOn` and `String.toNat?`, which `sendTag` calls.
  **`sent_keySends0`**, **`sent_keySends1`**, **`sent_keySends2`**: by `Johnson.Unfolds.sent_of`;
    that the oracle messages can be placed in trees: BY THE KERNEL.

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

namespace Johnson.AtFull.KeyBack
open Johnson.G.OfPlan (SendTag TestTag sendTag)
open Johnson.Unfolds (sent_of)

/-- The 6 sendings of `keySends0`. -/
theorem tags_keySends0 :
    (Johnson.G.keySends0.sends.map (·.label)).map sendTag =
      [some .indexMask, some .multiplicities, some (.stage .ranges 1), some (.stage .ranges 2),
       some (.stage .ranges 3), some .w] := by
  unfold sendTag
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- The 9 sendings of `keySends1`. -/
theorem tags_keySends1 :
    (Johnson.G.keySends1.sends.map (·.label)).map sendTag =
      [some .foldedRow, some .omega, some (.stage .folded 1), some (.stage .folded 2),
       some (.stage .folded 3), some (.stage .folded 4), some (.stage .omega 1),
       some (.stage .omega 2), some (.stage .omega 3)] := by
  unfold sendTag
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- The 4 sendings of `keySends2`. -/
theorem tags_keySends2 :
    (Johnson.G.keySends2.sends.map (·.label)).map sendTag =
      [some (.stage .own 1), some (.stage .own 2), some (.stage .own 3), some (.stage .own 4)] := by
  unfold sendTag
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq,
    Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- The `mapM` of `sentAt` returns at `keySends0`'s sendings, at every name and offset. -/
theorem sent_keySends0 (at_ : String) (off : Nat) :
    (Johnson.G.keySends0.sends.mapM
      (Johnson.G.OfPlan.sentAt at_ Johnson.G.keySends0.codes off)).isOk = true :=
  sent_of at_ off _ _ tags_keySends0 (by decide) (by decide +kernel)

/-- The `mapM` of `sentAt` returns at `keySends1`'s sendings, at every name and offset. -/
theorem sent_keySends1 (at_ : String) (off : Nat) :
    (Johnson.G.keySends1.sends.mapM
      (Johnson.G.OfPlan.sentAt at_ Johnson.G.keySends1.codes off)).isOk = true :=
  sent_of at_ off _ _ tags_keySends1 (by decide) (by decide +kernel)

/-- The `mapM` of `sentAt` returns at `keySends2`'s sendings, at every name and offset. -/
theorem sent_keySends2 (at_ : String) (off : Nat) :
    (Johnson.G.keySends2.sends.mapM
      (Johnson.G.OfPlan.sentAt at_ Johnson.G.keySends2.codes off)).isOk = true :=
  sent_of at_ off _ _ tags_keySends2 (by decide) (by decide +kernel)

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.tags_keySends0
#print axioms Johnson.AtFull.KeyBack.tags_keySends1
#print axioms Johnson.AtFull.KeyBack.tags_keySends2
#print axioms Johnson.AtFull.KeyBack.sent_keySends0
#print axioms Johnson.AtFull.KeyBack.sent_keySends1
#print axioms Johnson.AtFull.KeyBack.sent_keySends2
