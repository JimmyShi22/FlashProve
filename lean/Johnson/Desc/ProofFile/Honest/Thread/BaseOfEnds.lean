-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/BaseOfEnds.lean: WHICH COLUMNS THE FIELD `opened` BEGINS WITH
IN THE LAST CHAIN. The run hands the last chain the columns of the two earlier chains.
`BaseOfEnds F` says which these are: a `base` that is made of two lists of columns, at which the
description's own folds over the two earlier chains return on the rounds that the state has seen,
with nothing left over. It reads the rounds seen and the instance, and neither the field nor any
table.

  `BaseOfEnds`   the letter `B` of `SaidField` at the last chain
  `baseOfEnds_kept`   it is carried over a sub-protocol's rounds, with no premise

What these are. A definition and a conditional lemma on our own definitions. None is one of the
library's goals.

Limits.
  * That `BaseOfEnds F` holds at the last chain's start is `hB` of `door_field`
    (Honest/Thread/FromThreadsField.lean), and it is not shown here.
  * It says that the folds return. It does not say that the state they return is the one at which
    the last chain began: that is the thread's letter `begun`.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.SaidField
import Johnson.Desc.ProofFile.Honest.Law.Causal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc

variable {W₀ Rc Xi Tr X : Type} {Bk : ProverCoinCounts} (F : FileDescription Xi)

/-- **The columns of the two earlier chains, off what the state has seen.** `r₁`, `r₂`: the two
chains' rounds, at the head of the rounds seen. `c₁`, `c₂`: the columns that their folds read. A
definition: a filling of the letter `B` of `SaidField`. -/
def BaseOfEnds (_ : Coins Bk) (m : Mid (Local W₀ Rc Xi Tr) X) (base : List OpenedColumn) : Prop :=
  ∃ r₁ r₂ rest c₁ c₂ e₁ e₂, m.seen = r₁ ++ (r₂ ++ rest) ∧ base = c₁ ++ c₂ ∧
    r₁.length = (F.first.blocksInOrder.flatMap (·.rounds)).length ∧
    c₁.length = owed 0 F.first.blocksInOrder r₁ ∧
    r₂.length = (F.shared.blocksInOrder.flatMap (·.rounds)).length ∧
    c₂.length = owed 0 F.shared.blocksInOrder r₂ ∧
    foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub m.st.input.x)) r₁ c₁ = .ok (e₁, [], []) ∧
    foldBlocks 0 F.shared.blocksInOrder (F.start₂ (F.pub m.st.input.x)) r₂ c₂ = .ok (e₂, [], [])

/-- **It is carried over a sub-protocol's rounds**: they lie behind what was seen, and the input
stays. -/
theorem baseOfEnds_kept {S Cl V Pb : Type} (T : Thread Bk S Cl V (Local W₀ Rc Xi Tr) X Pb)
    (b : Nat) : BaseKept T (BaseOfEnds F) b := by
  intro blk _ k m E ds y cols base hM hB
  obtain ⟨⟨l, -, hy⟩, -⟩ := hM
  obtain ⟨hi, -, hs⟩ := play_mid _ _ _ _ _ hy
  obtain ⟨tail, ht⟩ : ∃ t, y.2.seen = m.seen ++ t := ⟨_, hs⟩
  obtain ⟨r₁, r₂, rest, c₁, c₂, e₁, e₂, h0, h1, h2, h3, h4, h5, h6, h7⟩ := hB
  refine ⟨r₁, r₂, rest ++ tail, c₁, c₂, e₁, e₂, ?_, h1, h2, h3, h4, h5, ?_, ?_⟩
  · show y.2.seen = _
    rw [ht, h0]
    simp only [List.append_assoc]
  · show foldBlocks 0 F.first.blocksInOrder (F.start₁ (F.pub y.2.st.input.x)) r₁ c₁ = _
    rw [hi]
    exact h6
  · show foldBlocks 0 F.shared.blocksInOrder (F.start₂ (F.pub y.2.st.input.x)) r₂ c₂ = _
    rw [hi]
    exact h7

end ProofFile.Honest

#print axioms ProofFile.Honest.BaseOfEnds
#print axioms ProofFile.Honest.baseOfEnds_kept
