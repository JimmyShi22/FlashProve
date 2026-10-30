-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/IndexLotAtHead.lean: the proof of the statement of
Johnson/Desc/ProofFile/Honest/K11/Plays/IndexLotAtHeadStatement.lean, to the letter. A lemma; none
of the library's goals. A joining: no new argument.

How. The lot's row and place: `indexTakes_head` (Honest/K4/Law/W/IndexTakes.lean, another group of
authors'; this library may not hold it) and `indexRows_at_head` (IndexKeyWritten.lean of this
folder): 12 % 1 and 12 / 1. The job's numbers and rides are rewritten by the two equations;
`atIndexKey_at_head` with `atIndexKey_gives` (there) hands the six facts at them; `indexLotAgrees`
(IndexLotKey.lean of this folder) at message 4 and entry 12: its three premises and the test's
letters are these facts.

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.IndexLotAtHeadStatement
import Johnson.Desc.ProofFile.Honest.K11.Plays.IndexLotKey
import Johnson.Desc.ProofFile.Honest.K11.Plays.IndexKeyWritten
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IndexTakes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11

/-- **Under the head the lot of the second join and the opening's message 4 answer alike.** -/
theorem indexLotAgreesAtHead : IndexLotAgreesAtHead := by
  intro Z D r Zp Np cF x Bs base h O Bk W₀ Rc Tr X ch claims weights W Y wit J own₀ sf hP hR hE k w
    hd hd' mask row place y y' h1 h2
  have g := atIndexKey_at_head h O
  rw [← hP, ← hR] at g
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := atIndexKey_gives g
  rw [ProofFile.Honest.K4.W.indexTakes_head h, indexRows_at_head h] at h1
  refine indexLotAgrees Bk W₀ Rc ProofFile.Inst Tr X ch IM.k11Place (_root_.K11.parOf Zp Bs.G₀) claims
    weights (ProofFile.Honest.K4.Lot.k4IndexNum Zp) W Y wit J own₀ 4 12 sf g1 g2 ?_ ?_ k w hd hd' mask row
    place y y' ?_ h2
  · rw [g3, g4]
    decide
  · rw [g5, g6]
    exact hE
  · rw [g3]
    exact h1

end ProofFile.Honest.K11

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.indexLotAgreesAtHead
