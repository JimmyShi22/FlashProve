-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K07Proof.lean: THE NEXT TOKEN's LAW, PROVED: `K07LawStatement`. From the next
token's lemma (ReplyProof.lean) and one fact on the head's text: the token among the letters that
`given` returns is the one that is read at the seat (`given_token`).
-/
import Johnson.Desc.Kinds.Law.K07Statement
import Johnson.Desc.Kinds.Law.ReplyProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

/-- The head's y is read at the next token's seat, and nowhere else. -/
theorem given_token {S : Type} {p : Par} {L : Seat S} {s : S} {g : Given}
    (h : given p L s = .ok g) : Reply.token L.toSeat s = some g.token.y := by
  unfold given at h
  cases hz : L.lookup s with
  | none => simp [hz, named, bind, Except.bind] at h
  | some z =>
    cases hy : Reply.token L.toSeat s with
    | none => simp [hz, hy, named, bind, Except.bind] at h
    | some y0 =>
      simp only [hz, hy, named, need, bind, Except.bind, pure, Except.pure] at h
      split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst h
        rfl

/-- **The next token's law.** -/
theorem k07Law : K07LawStatement := by
  intro S L hL p T r e asked
  obtain ⟨h1, h2⟩ := replyLemma S L.toSeat hL p.sizes.V T r e asked
  refine ⟨h1, ?_⟩
  intro sHead sEnd g hEq hg hfin
  obtain ⟨ht, hlt, h0⟩ := h2 sHead sEnd hEq hfin
  refine ⟨?_, hlt, h0⟩
  have := given_token hg
  rw [ht] at this
  exact (Option.some.inj this).symm

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.k07Law
