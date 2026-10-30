-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/KeyBack/LabelsKey.lean: `VerifiableInference.Desc.Key.groupsAtLabel` (over
`stageOfLabel`; Johnson/Desc/Key/Source.lean) at the labels of the key file's 19 written sendings of
the full size (Johnson/G/SendsWritten.lean): three written lists.

  **`groups_keySends0`**, **`groups_keySends1`**, **`groups_keySends2`**: BY THE KERNEL, behind the
    laws of Johnson/Unfolds/ on `String.splitOn` and `String.toNat?`, which `stageOfLabel` calls.
  Negative test, BY THE KERNEL: `groups_keySends2_no`: the second chain's groups are not the list
    with its last number bent.

Limits. The full size alone. IT SPEAKS OF THE WRITTEN SENDINGS: that these are what `sendsOf`
(Johnson/G/Sends.lean) makes of any public files is not said here. At a label whose last piece is no
numeral `stageOfLabel` answers 0: a default, no refusal. Nothing on soundness. On hiding nothing.

-/
import Johnson.Unfolds.SliceFoldl
import Johnson.Unfolds.SplitOn
import Johnson.G.SendsWritten
import Johnson.Desc.Key.Source

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open VerifiableInference.Desc.Key (stageOfLabel groupsAtLabel)

/-- The groups at the labels of `keySends0`'s 6 sendings. -/
theorem groups_keySends0 :
    (Johnson.G.keySends0.sends.map (·.label)).map groupsAtLabel =
      [[[300]], [[100]], [[101]], [[102]], [[103]], [[300]]] := by
  unfold groupsAtLabel stageOfLabel
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq]
  decide +kernel

/-- The groups at the labels of `keySends1`'s 9 sendings. -/
theorem groups_keySends1 :
    (Johnson.G.keySends1.sends.map (·.label)).map groupsAtLabel =
      [[[200]], [[250, 300], [250, 200]], [[201]], [[202]], [[203]], [[204]], [[251]], [[252]],
       [[253]]] := by
  unfold groupsAtLabel stageOfLabel
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq]
  decide +kernel

/-- The groups at the labels of `keySends2`'s 4 sendings. -/
theorem groups_keySends2 :
    (Johnson.G.keySends2.sends.map (·.label)).map groupsAtLabel =
      [[[301]], [[302]], [[303]], [[304]]] := by
  unfold groupsAtLabel stageOfLabel
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq]
  decide +kernel

/-- A negative test: the second chain's groups are no other list. -/
theorem groups_keySends2_no :
    (Johnson.G.keySends2.sends.map (·.label)).map groupsAtLabel ≠
      [[[301]], [[302]], [[303]], [[305]]] := by
  unfold groupsAtLabel stageOfLabel
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.toNat?_eq]
  decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.groups_keySends0
#print axioms Johnson.AtFull.KeyBack.groups_keySends1
#print axioms Johnson.AtFull.KeyBack.groups_keySends2
#print axioms Johnson.AtFull.KeyBack.groups_keySends2_no
