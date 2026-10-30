-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ETies.lean: THE OUTPUT HEAD's LETTERS y AND e (AND r, THE TOKENS, THE SIZES, THE POLICY) ARE THE
RECORD's (two ties on e). `given_letters`, generic in the seat:
where HeadFrame.lean's `given` returns the letters g, g's sizes and policy are the parameters', g's
request is what the seat reads of the record, and g's token is the one read at the next token's seat.
`ties_at`: AT THE FIRST CHAIN's RECORD, the seat of Johnson/Stored/HeadSeatAt.lean: (i) y IS tokOf OF
THE ELEMENT THAT LIES IN S.out.reply; (ii) e IS S.rowE, r IS S.rowR, tok i IS S.tokv's entry i: the
request file's own words, as State.lean reads them of S.req: the very `fun s => s.rowE` that the next
token's variant (ReplyForm.lean: kindForm) is handed; and T = 2 ^ h.lt, V = h.V of the public numbers.
By unfolding. No Mathlib. OVER HeadFrame.lean, HeadSeatAt.lean AND
State.lean.
WHAT IT DOES NOT SAY: that S.req holds the request file's words (the record's start); that
S.reqT = T (the request's test); who laid S.out.reply (H:2's quiet half: other files').
-/
import Johnson.Stored.HeadSeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc.First (S)

/-- What the letters in front of the hearing are. -/
theorem given_letters {S : Type} {p : Par} {L : Seat S} {s : S} {g : Given}
    (h : given p L s = .ok g) :
    g.sizes = p.sizes ∧ g.policy = p.policy ∧ g.request = L.request s ∧
      Reply.token L.toSeat s = some g.token.y := by
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
        exact ⟨rfl, rfl, rfl, rfl⟩

/-- **The two ties, at the first chain's record.** -/
theorem ties_at (h : OnBytes.Model.Head.Shape) (iU3 work : Nat) (s : S) (g : Given)
    (hg : given (parOf h work) (seatAt h iU3) s = .ok g) :
    (∃ x, s.out.reply = some x ∧ g.token.y = OnBytes.Desc.Reply.tokOf x) ∧
      g.request.e = s.rowE ∧ g.request.r = s.rowR ∧ (∀ i, g.request.tok i = s.tokv.getD i 0) ∧
      g.sizes = sizesOf h ∧ (letI := g.sizes; Norm.T = 2 ^ h.lt ∧ V = h.V) := by
  obtain ⟨h1, _, h3, h4⟩ := given_letters hg
  have h3' : g.request = requestOf s := h3
  have h1' : g.sizes = sizesOf h := h1
  refine ⟨?_, congrArg (fun q => @Request.e q) h3', congrArg (fun q => @Request.r q) h3',
    fun i => congrArg (fun q => @Request.tok q i) h3', h1', ?_⟩
  · have h4' : (s.out.reply).map OnBytes.Desc.Reply.tokOf = some g.token.y := h4
    cases hr : s.out.reply with
    | none => rw [hr] at h4'; simp at h4'
    | some x =>
      rw [hr] at h4'
      simp only [Option.map_some, Option.some.injEq] at h4'
      exact ⟨x, rfl, h4'.symm⟩
  · rw [h1']
    exact ⟨rfl, rfl⟩

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.ties_at
