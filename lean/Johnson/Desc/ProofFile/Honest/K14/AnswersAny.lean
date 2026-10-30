-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/AnswersAny.lean: kind K14: THE OOD ANSWERS OF A SENDING DO NOT
HANG ON THE WORDS IN FRONT. One statement with its proof.

answersAt (Johnson/Desc/K14/Honest/SendMoves.lean) takes the words in front of a sending as an
argument, and reads them grown by the sending's own messages. Each answer is the left side of a
sample constraint of one new message, which is a sum over that message's two tables alone
(Honest/K14/SendingsAnswers.lean: sampleValue_single); there the grown words are the new message's
(Johnson/Prover/Send/Held.lean: held_new).

Main name:
  answersAt_any       answersAt Q T r w V = answersAt Q T r w' V. No premise

What it is for: the thread's witness has a letter at the numbers of messages that are not this
kind's (Honest/K14/Thread2.lean: witAll); the premises on what the two sendings show stand at other
words in front (Honest/K14/Exchange2.lean).

What is not claimed. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.SendingsAnswers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes (Statement)
open OnBytes.Means (Words)
open OnBytes.Slice (GE stSent)
open VerifiableInference.Desc (K1.Par)
open Johnson.Prover.Send (Rows answers held_new)
open Desc.K14.Honest (answersAt)

/-- **The OOD answers of a sending do not hang on the words in front**: each is a sum over its own
message's two tables. -/
theorem answersAt_any (Q : K1.Par) (T : Statement) (r : Fmt.RoundView) (w w' : Words GE)
    (V : Nat → Rows) : answersAt Q T r w V = answersAt Q T r w' V := by
  unfold answersAt answers
  refine congrArg (List.map Fmt.ItemValue.answer) ?_
  refine List.flatMap_congr fun k hk => ?_
  have hk' : k < Q.sent.size := List.mem_range.1 (List.mem_filter.1 hk).1
  refine List.map_congr_left fun i _ => ?_
  have h2 := stSent_at Q T k hk'
  have l2 : T.oracles.size + k < (stSent T Q.sent).oracles.size := by
    by_contra h
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt h)] at h2
    cases h2
  refine congrArg OnBytes.Slice.ofE ?_
  rw [sampleValue_single _ _ _ l2, sampleValue_single _ _ _ l2]
  have e : ∀ part j, Johnson.Prover.Send.held w T.oracles.size Q V (T.oracles.size + k) part j =
      Johnson.Prover.Send.held w' T.oracles.size Q V (T.oracles.size + k) part j := fun part j => by
    rw [held_new w _ Q V k hk', held_new w' _ Q V k hk']
  simp only [e]

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.answersAt_any
