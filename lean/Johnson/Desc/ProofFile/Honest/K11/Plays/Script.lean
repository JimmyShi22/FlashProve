-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/Script.lean: the proof of `TiesOfScript`
(Honest/K11/Plays/ScriptStatement.lean), to the letter. A lemma; none of the library's goals.

How. The two letters of `MergeTiesAt`'s "there is": cells := `weightCells`; idx := the witness's
index-mask message, entry by entry. Then clause by clause: the first and the fifth by the choice of
the cells (a row below m0 lies below nR); the second is maskTie; the third indexTie; the fourth
`K11ClaimTrue`; the sixth matTie; the seventh by the choice of idx.

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.ScriptStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11

/-- **The field ties, from the kind's premise on the Script and that the claim is true.** -/
theorem tiesOfScript : TiesOfScript := by
  intro Bk W₀ Rc Xi Tr X Pb Pp Tok Xi' rows cols nR Xp T Said b P weights coins toP toW Dof seg hQ
    hm hC blk k s m E ds y cols' s' a claim x0 b9 a9 hT hS hblk ha hcl hx hb9 ha9 ds'
  refine ⟨weightCells nR (weights m.st.input.w₀),
    fun c' => ((Dof m.st.input).rw13 (toP (T.seat k y.2 s').1, s')
      (toW (T.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask ⟨s'.out.indexMasks, c'⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, fun _ => rfl⟩
  · intro r c hr _
    unfold weightCells
    rw [if_pos (Nat.lt_of_lt_of_le hr hm)]
  · exact hQ.maskTie blk k s m E ds y cols' s' a a9 hT hS hblk ha ha9 ds'
  · exact hQ.indexTie blk k s m E ds y cols' s' hT hS hblk ds'
  · exact hC blk k s m E ds y cols' s' a claim x0 b9 hT hS hblk ha hcl hx hb9 ds'
  · intro j hj C
    unfold weightCells
    rw [if_neg (Nat.not_lt.2 hj)]
  · intro i C hCk
    unfold weightCells
    rw [if_pos i.2]
    exact hQ.matTie blk k s m E ds y cols' s' hT hS hblk ds' i C hCk

end ProofFile.Honest.K11

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.tiesOfScript
