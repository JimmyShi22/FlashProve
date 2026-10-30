-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReplyFormProof.lean.
WHAT IT DOES NOT SHOW. IT SPEAKS OF A MODEL OF THREE STEPS (decide ; rest ; last), NOT OF
FileDescription.run AND NOT OF verify(): owed before it speaks of a fold: that the fold, cut at this
block's place, is such a rest; hrest; hlast at the fold's own last test, at the same T and e.
That the other blocks of a fold leave the seat and e: a premise
(hrest): left to each kind's files. The refusals' NAMES differ: where the variant refuses at the
round, the text that rides refuses at the end. Nothing on soundness.
WHAT IT IS. THE NEXT TOKEN's VARIANT (ReplyForm.lean): THE WHOLE DECISION's VERDICT IS THE SAME WITH
EITHER TEXT. Proved; core Lean alone.
WHAT IT SAYS. The whole decision, as far as the next token goes, is: the block's decide at its
round; then whatever the other blocks do (rest: ANY function that may refuse, and that leaves the
seat and the request's e as they are); then the last test's part (Reply.fin) at the client's token.
With decideForm in decideE's place the outcome is the same: the same record where one says yes, a
refusal where the other refuses. And: a yes of decideForm gives "e = T or the token is 0" at once.

-/
import Johnson.Desc.Kinds.ReplyForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Reply

open OnBytes.Desc.Reply (isToken tokOf replyGate reqForm)

variable {S : Type}

/-- The last test's yes holds the new test's. -/
theorem form_of_fin {V T r e asked : Nat} {L : Seat S} {s : S}
    (h : fin V T r e asked L s = true) : (e == T || token L s == some 0) = true := by
  unfold fin at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hg, hf⟩ := h
  unfold reqForm at hf
  rw [Bool.and_eq_true, Bool.or_eq_true] at hf
  rw [Bool.or_eq_true]
  rcases hf.2 with h1 | h1
  · exact Or.inl h1
  · refine Or.inr ?_
    unfold replyGate at hg
    unfold token
    cases hr : L.reply s with
    | none => rw [hr] at hg; exact absurd hg (by simp)
    | some x =>
      rw [hr] at hg
      simp only [Bool.and_eq_true, beq_iff_eq] at hg h1
      simp [hg.2, h1]

/-- A yes of the variant: the text that rides says yes with the same record, and the new test
holds. -/
theorem decideForm_ok {V T : Nat} {L : Seat S} {e : S → Nat} {s s' : S} {rs : List Fmt.RoundView}
    (h : decideForm V T L e s rs = .ok s') :
    decideE V L s rs = .ok s' ∧ (e s' = T ∨ token L s' = some 0) := by
  unfold decideForm at h
  cases hd : decideE V L s rs with
  | error x => rw [hd] at h; exact absurd h (by simp [Except.bind])
  | ok a =>
    rw [hd] at h
    simp only [Except.bind] at h
    by_cases hc : (e a == T || token L a == some 0) = true
    · rw [if_pos hc] at h
      injection h with h
      subst h
      rw [Bool.or_eq_true] at hc
      exact ⟨rfl, hc.imp (by simp) (by simp)⟩
    · rw [if_neg hc] at h
      exact absurd h (by simp)

/-- The last test as a step. -/
def finStep (V T r asked : Nat) (L : Seat S) (e : S → Nat) (s : S) : Except String S :=
  if fin V T r (e s) asked L s then .ok s else .error "the last test"

/-- **THE VERDICT IS THE SAME, AGAINST ANY LAST TEST** whose yes holds the new test's (hlast): so
also against a fold in which "0 where e < T" is asked elsewhere than in Reply.fin. -/
theorem sameVerdictAny (V T : Nat) (L : Seat S) (e : S → Nat) (rest last : S → Except String S)
    (hrest : ∀ a b, rest a = .ok b → L.reply b = L.reply a ∧ e b = e a)
    (hlast : ∀ b b', last b = .ok b' → (e b == T || token L b == some 0) = true) (s : S)
    (rs : List Fmt.RoundView) :
    (((decideForm V T L e s rs).bind rest).bind last).toOption =
      (((decideE V L s rs).bind rest).bind last).toOption := by
  unfold decideForm
  cases hd : decideE V L s rs with
  | error x => rfl
  | ok a =>
    simp only [Except.bind]
    by_cases hc : (e a == T || token L a == some 0) = true
    · rw [if_pos hc]
    · rw [if_neg hc]
      cases hr : rest a with
      | error x => rfl
      | ok b =>
        obtain ⟨h1, h2⟩ := hrest a b hr
        cases hl : last b with
        | error x =>
          show none = (last b).toOption
          rw [hl]
          rfl
        | ok b' =>
          exfalso
          apply hc
          have := hlast b b' hl
          unfold token at this ⊢
          rw [h1, h2] at this
          exact this

/-- **THE WHOLE DECISION's VERDICT IS THE SAME**, where the last test is Reply.fin. -/
theorem sameVerdict (V T r asked : Nat) (L : Seat S) (e : S → Nat) (rest : S → Except String S)
    (hrest : ∀ a b, rest a = .ok b → L.reply b = L.reply a ∧ e b = e a) (s : S)
    (rs : List Fmt.RoundView) :
    (((decideForm V T L e s rs).bind rest).bind (finStep V T r asked L e)).toOption =
      (((decideE V L s rs).bind rest).bind (finStep V T r asked L e)).toOption :=
  sameVerdictAny V T L e rest _ hrest (fun b b' h => by
    unfold finStep at h
    by_cases hf : fin V T r (e b) asked L b = true
    · exact form_of_fin hf
    · rw [if_neg hf] at h
      exact absurd h (by simp)) s rs

end VerifiableInference.Desc.Kinds.Reply
