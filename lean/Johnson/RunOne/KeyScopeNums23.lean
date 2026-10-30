-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyScopeNums23.lean: THEOREMS, BY THE KERNEL, AT THE WRITTEN CONSTANT. **The second chain's frame at the written data holds the trees 6 · 7 · 8 at the depths of the codes of o_u · o_omega · o_sp.** The like of holds0 | holds1 | holds5 (Johnson/RunOne/KeyScopeNums.lean), three seats further, at the tables' fr₂.
OBJECT: (fr₂ Johnson.G.writtenKFull).all. USER: none yet (meant: other files' premises holdsB (fr₂ D) 6 | 7 | 8: holdsB's body, unfolded). No letter.
  any_pairs₂       a test on the second frame's trees that reads number and depth alone, off the list of pairs (the frames of the three chains share one list)
  holds6 | holds7 | holds8 · three controls: at «+ 1»: false
What is not claimed. That any description's data are the written data. Nothing on soundness.

-/
import Johnson.RunOne.KeyScopeNums

set_option autoImplicit false

namespace Johnson.RunOne.KeyLetters

open OnBytes OnBytes.Maker
open VerifiableInference.Desc.Sound (allOf)
open Johnson.RunOne.KeyRows23 (fr₂)
open Johnson.Pack (aOf)
open Johnson.Top.H (csKey shU shO shSp)
open Johnson.G (writtenKFull)

theorem any_pairs₂ (D : WholeD) (g : ℕ × ℕ → Bool) :
    ((fr₂ D).all.any fun t => g (t.no, t.a)) = ((allOf D).map fun t => (t.no, t.a)).any g := by
  show (allOf D).any _ = _
  rw [List.any_map]
  rfl

theorem holds6 : ((fr₂ writtenKFull).all.any fun t => t.no == 6 && decide (aOf csKey shU ≤ t.a)) = true :=
  (any_pairs₂ writtenKFull fun p => p.1 == 6 && decide (aOf csKey shU ≤ p.2)).trans (by rw [trees_written]; decide +kernel)
theorem holds7 : ((fr₂ writtenKFull).all.any fun t => t.no == 7 && decide (aOf csKey shO ≤ t.a)) = true :=
  (any_pairs₂ writtenKFull fun p => p.1 == 7 && decide (aOf csKey shO ≤ p.2)).trans (by rw [trees_written]; decide +kernel)
theorem holds8 : ((fr₂ writtenKFull).all.any fun t => t.no == 8 && decide (aOf csKey shSp ≤ t.a)) = true :=
  (any_pairs₂ writtenKFull fun p => p.1 == 8 && decide (aOf csKey shSp ≤ p.2)).trans (by rw [trees_written]; decide +kernel)

theorem holds6_no : ((fr₂ writtenKFull).all.any fun t => t.no == 6 && decide (aOf csKey shU + 1 ≤ t.a)) = false :=
  (any_pairs₂ writtenKFull fun p => p.1 == 6 && decide (aOf csKey shU + 1 ≤ p.2)).trans (by rw [trees_written]; decide +kernel)
theorem holds7_no : ((fr₂ writtenKFull).all.any fun t => t.no == 7 && decide (aOf csKey shO + 1 ≤ t.a)) = false :=
  (any_pairs₂ writtenKFull fun p => p.1 == 7 && decide (aOf csKey shO + 1 ≤ p.2)).trans (by rw [trees_written]; decide +kernel)
theorem holds8_no : ((fr₂ writtenKFull).all.any fun t => t.no == 8 && decide (aOf csKey shSp + 1 ≤ t.a)) = false :=
  (any_pairs₂ writtenKFull fun p => p.1 == 8 && decide (aOf csKey shSp + 1 ≤ p.2)).trans (by rw [trees_written]; decide +kernel)

end Johnson.RunOne.KeyLetters

#print axioms Johnson.RunOne.KeyLetters.any_pairs₂
#print axioms Johnson.RunOne.KeyLetters.holds6
#print axioms Johnson.RunOne.KeyLetters.holds7
#print axioms Johnson.RunOne.KeyLetters.holds8
#print axioms Johnson.RunOne.KeyLetters.holds6_no
#print axioms Johnson.RunOne.KeyLetters.holds7_no
#print axioms Johnson.RunOne.KeyLetters.holds8_no
