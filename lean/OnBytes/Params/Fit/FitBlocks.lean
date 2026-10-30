-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/Fit/FitBlocks.lean: what the property Small of an entry (FitCalc.lean in this folder)
gives: the blocks of a hash chain's answer that the round can ask are far fewer than 2 ^ 48; and the
property goes over to the entry with its words reduced modulo 2 ^ 64 (normE, ReadNorm.lean).

Main names:
  small_words: Small e → Fmt.wordsAtMost e k < 2 ^ 47, for every kind k.
  small_blocks: Small e → e.logN ≤ 64 ∧ Fmt.blocksFor (Fmt.wordsAtMost e .sealed) + 1 < 2 ^ 48.
  small_norm: Small e → Small (normE e).
  small_plan: if all entries of a plan are Small, so are those of the reduced plan (normP).
Limits: arithmetic alone. That an entry of any plan is Small is not said here.
The program does not import this file.

-/
import OnBytes.Params.Fit.FitCalc
import OnBytes.Params.Fit.ReadNorm
import Fmt.Rules6Round

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Params

theorem small_words {e : Fmt.Entry} (h : Small e) (k : Fmt.Kind) :
    Fmt.wordsAtMost e k < 2 ^ 47 := by
  obtain ⟨_, _, _, h2, h3, h4, h5⟩ := h
  unfold Fmt.wordsAtMost
  have a2 : e.poss ≤ 1099511627776 := h2
  have a3 : e.drawE ≤ 1099511627776 := h3
  have a4 : e.drawNZ ≤ 1099511627776 := h4
  have a5 : e.trits ≤ 35184372088832 := h5
  have g : (2 : Nat) ^ 47 = 140737488355328 := by norm_num
  rw [g]
  split <;> omega

theorem small_blocks {e : Fmt.Entry} (h : Small e) :
    e.logN ≤ 64 ∧ Fmt.blocksFor (Fmt.wordsAtMost e .sealed) + 1 < 2 ^ 48 := by
  refine ⟨h.2.2.1, ?_⟩
  have w := small_words h .sealed
  unfold Fmt.blocksFor
  have g : (2 : Nat) ^ 47 = 140737488355328 := by norm_num
  have g' : (2 : Nat) ^ 48 = 281474976710656 := by norm_num
  rw [g] at w
  rw [g']
  omega

theorem small_norm {e : Fmt.Entry} (h : Small e) : Small (normE e) :=
  ⟨h.1, (Nat.mod_le _ _).trans h.2.1, (Nat.mod_le _ _).trans h.2.2.1,
    (Nat.mod_le _ _).trans h.2.2.2.1, (Nat.mod_le _ _).trans h.2.2.2.2.1,
    (Nat.mod_le _ _).trans h.2.2.2.2.2.1, (Nat.mod_le _ _).trans h.2.2.2.2.2.2⟩

theorem small_plan {P : Fmt.Plan} (h : ∀ e ∈ P.entries, Small e) :
    ∀ e ∈ (normP P).entries, Small e := by
  intro e he
  obtain ⟨e0, h0, rfl⟩ := List.mem_map.1 he
  exact small_norm (h e0 h0)

end OnBytes.Params

#print axioms OnBytes.Params.small_blocks
#print axioms OnBytes.Params.small_plan
