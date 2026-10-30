-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/Plays/AtPureOpens.lean: what the maker `onlineProverFromPublicFiles` lays where it
returns, at any filling: the proof of the statement `AtPureOpens` of
Honest/K11/Plays/HalfAtFillStatement.lean, to the letter, with one helper (`of_due`: a value that
`due?` hands out was there). Lemmas; none of the library's goals.

How. The maker's text is opened call by call; where it returns, the three fields are laid so.

The two lemmas name no filling. They stand apart from the lemmas at written fillings
(HalfAtFill.lean of this folder), so that a file that names no filling need not stand over those. A
form of HalfAtFill.lean that declares these two names itself cannot be imported beside this file.

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.Plays.HalfAtFillStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K11

/-- A value that `due?` hands out was there. -/
theorem of_due {α : Type} {what : String} {x : Option α} {a : α} (h : due? what x = .ok a) :
    x = some a := by
  cases x with
  | none => cases h
  | some b => exact congrArg some (Except.ok.inj h)

/-- **What the maker lays where it returns.** -/
theorem atPureOpens : AtPureOpens := by
  intro W₀ Rc Tr X₀ X o pol lay KL P A h
  unfold onlineProverFromPublicFiles at h
  simp only [Except.bind] at h
  repeat' split at h
  all_goals first
    | (cases h; exact ⟨by assumption, of_due (by assumption), rfl⟩)
    | cases h

end ProofFile.Honest.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.of_due
#print axioms ProofFile.Honest.K11.atPureOpens
