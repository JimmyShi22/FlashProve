-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/Tw/K2C/RowsDebts.lean: code switching (the kind K2): TWO EQUATIONS ON THE TABLE's
NUMBERS: at the numbers closed over the sub-protocols (`Numbers.atBlocks`,
Johnson/Desc/First/NumbersAtBlocks.lean), `rowsAt m` at the classes "carried" and "position" is
the pair of numbers that two structures of debts ask: `K2.SwitchDebts`
(Johnson/Top/H0/Tw/K2C/HandsCore.lean: its fields carried, position) and `K2.LinkDebts`
(Johnson/Top/H0/Tw/K2C/HandsLink.lean: the same two, with t for d). Two theorems. No sub-protocol
imports this file.
Why. The code-switching step's terms that end in `IM.Hands` took the two equations as premises on
a letter N. At the numbers that count they follow from five facts.
  `keptSamples_len`: where each kept oracle message has just one stored OOD claim
  (`sampleRows.size = 1`), `keptSamples x W` is the number of the frame's kept places.
  `rows_debts`: **the two equations**, in the letters of the two structures: by
  `atBlocks_carried`, `atBlocks_position` (Johnson/Desc/First/RowsAtBlocks.lean) and
  `frame_kept_len` (Johnson/Top/H0/Tw/K2C/FrameKeptLen.lean).
What it does not say. WHAT A CODE-SWITCHING STEP ADDS TO THE CLAIMS STILL OPEN: no accepting run,
no verifier and no probability stand in either statement: both sides are formulas on numbers. What
an accepting run adds is `yes_row_classes` (Johnson/Top/H0/Tw/K2C/RowsClasses.lean).
Limits. STILL OWED, BY NAME: **hone** (each kept oracle message has just one stored OOD claim): A
CLAUSE ON THE VERIFIER's STATE. The field is laid by `Send.admit` (OnBytes/Iop/Send.lean) behind
the test "as many rows as the message's shape has answers"; so on an honest run hone holds ONLY
WHERE THE PARAMETER FILE SAYS "answers 1". The stored file says so (`lines32`,
Ladder/Stored.lean), and the goals' scope holds that line fixed: `InScope` (Ladder.lean) asks the
file to be `policyFile v`, in which eight numbers alone are free (`FreeLines`), this one not among
them. The format's range check admits 1 to 4 (by reading): at 2 to 4 hone fails at
every code-switching step that keeps a message, and "one row a kept copy" in `carriedRows`
(Johnson/Desc/First/RowsAtPlan.lean) with it. None of the table's fixed tests on the state gives
hone. Toward it lies `SampleGood` (Johnson/Top/H0/K2Hears/SampleGood.lean), which this kind's
accepting runs keep; it is silent on a message without a stored claim: that a kept message has one
is shown in none of the files named here · hlen and hf (what is left of hpos:
Johnson/Top/H0/Tw/K2C/PossAtK2.lean): two facts on public data · hT: its named payer
`K2.target_of_plan` (Johnson/Top/H0/Tw/K2C/PositionAtPlan.lean) takes two facts on the state and
does not reach the last code-switching step (the finish). At m = 0 nothing is said. No example at
the release's values is shown. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.


-/
import Johnson.Top.H0.Tw.K2C.RowsClasses
import Johnson.Top.H0.Tw.K2C.PositionCount
import Johnson.Top.H0.Tw.K2C.FrameKeptLen
import Johnson.Desc.First.RowsAtBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)

/-- With one stored OOD claim a kept oracle message, the sum is the number of kept places. -/
theorem keptSamples_len {x : _root_.Tw.K2.Front} {W : SwitchFrame}
    (hone : ∀ k ∈ W.kept, (x.st.oracles.getD k.old default).sampleRows.size = 1) :
    keptSamples x W = W.kept.length := by
  unfold keptSamples
  rw [List.map_congr_left hone]
  simp

/-- **The table's `rowsAt` at the two classes is the pair of numbers that the two debts ask.** -/
theorem rows_debts {St Cl : Type} {N₀ : Numbers} {sh : Params.ReqShape} {links : List ModelPart}
    {bs : List (Block St Cl)} {m d : Nat} {x : _root_.Tw.K2.Front} {W : SwitchFrame}
    (hm : m ≠ 0) (hW : K2.frameAt x = some W)
    (hT : x.T = ((reqGroups sh).getD m {}).target) (hpos : possAt bs links.length m = d)
    (hlen : (N₀.keptOf (m - 1)).length = x.T.kept.size)
    (hone : ∀ k ∈ W.kept, (x.st.oracles.getD k.old default).sampleRows.size = 1) :
    (Numbers.atBlocks N₀ sh links bs).rowsAt m .carried = (0, 1 + K2.keptSamples x W) ∧
      (Numbers.atBlocks N₀ sh links bs).rowsAt m .position =
        (1 + K2.keptSamples x W, d * (1 + K2.targetRows x.T + 2)) := by
  have e : K2.keptSamples x W = (N₀.keptOf (m - 1)).length := by
    rw [keptSamples_len hone, frame_kept_len hW, hlen]
  refine ⟨by rw [atBlocks_carried N₀ sh links bs hm, e], ?_⟩
  rw [atBlocks_position N₀ sh links bs hm, e, hpos]
  unfold positionRows targetRows
  rw [hT]

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.keptSamples_len
#print axioms VerifiableInference.Desc.First.K2.rows_debts
