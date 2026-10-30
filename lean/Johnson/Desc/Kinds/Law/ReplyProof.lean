-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReplyProof.lean: THE NEXT TOKEN's LEMMA, PROVED: `ReplyLemmaStatement` of
Johnson/Desc/Kinds/HeadLaw.lean. By unfolding the block's text (ReplyKind.lean) and the part that it
calls (Johnson/Desc/Reply/ReplyStep.lean). No chance in it; no premise beyond the statement's own.
-/
import Johnson.Desc.Kinds.HeadLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Desc.Reply (readReply isToken tokOf replyGate reqForm)

/-- A token's number is below V. -/
theorem tokOf_lt {V : Nat} {h : E} (ht : isToken V h = true) : tokOf h < V := by
  unfold isToken at ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  exact ht.2

/-- **The next token's lemma.** -/
theorem replyLemma : ReplyLemmaStatement := by
  intro S L hL V T r e asked
  refine ⟨?_, ?_⟩
  · intro s s' rs h
    unfold Reply.decide at h
    match rs, h with
    | [], h => simp [Reply.decideE, Except.toOption] at h
    | _ :: _ :: _, h => simp [Reply.decideE, Except.toOption] at h
    | [r0], h =>
      simp only [Reply.decideE] at h
      split at h
      · simp [Except.toOption] at h
      · rename_i hs
        split at h
        · simp [Except.toOption] at h
        · rename_i x hx
          split at h
          · rename_i ht
            simp only [Except.toOption, Option.some.injEq] at h
            subst h
            refine ⟨?_, tokOf x, tokOf_lt ht, ?_⟩
            · cases hr : L.reply s with
              | none => rfl
              | some v => simp [hr] at hs
            · simp [Reply.token, hL]
          · simp [Except.toOption] at h
  · intro sHead sEnd hEq hfin
    unfold Reply.fin at hfin
    simp only [Bool.and_eq_true] at hfin
    obtain ⟨hg, hq⟩ := hfin
    cases hr : L.reply sEnd with
    | none => simp [replyGate, hr] at hg
    | some x =>
      simp only [replyGate, hr, Bool.and_eq_true, beq_iff_eq] at hg
      obtain ⟨ht, hy⟩ := hg
      refine ⟨?_, ?_, ?_⟩
      · simp [Reply.token, hEq, hr, hy]
      · rw [← hy]; exact tokOf_lt ht
      · intro hlt
        unfold reqForm at hq
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hq
        rcases hq.2 with h1 | h1
        · omega
        · exact h1

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.replyLemma
