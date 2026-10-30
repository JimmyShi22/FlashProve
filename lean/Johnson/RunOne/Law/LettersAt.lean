-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/LettersAt.lean: LETTERS FOR
THE LINKS' ROWS THAT ARE BLIND AND READ LOW BY THEIR MAKE: a decoder, a condition and riding items
that are typed at (what is handed to the chain, a statement) are pulled back to the riding part's
type TK P (RideKeyD.lean) along pullK: the last part, and the statement made of the codes and the
bare messages (stm, JoinKeyD.lean). So pulled back they meet Blind; and LowDec where they read the
oracles below c.

Main names:
  pullK x: (what was handed to the chain, the statement of the riding part).
  pullK_stK: at the riding part of a record: the record's codes and its messages without their
    ledgers.
  blind_pull: Blind, by the make.
  lowDec_pull: LowDec, from the like of the letters that are pulled back.

Object: none of a description's text: a law on letters.
User: none yet: whoever fills dec, cond and Oth of fk_link_priced (LinkPriced.lean).
Letters: P, M, Wp, the frame Fr; dec', cond', Oth'.

Limits. Nothing on whether such letters have a member. Nothing on soundness.

-/
import Johnson.RunOne.Law.JoinKeyD

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.LettersAt
open OnBytes OnBytes.Params
open VerifiableInference.Desc.Key (FirstState)
open Johnson.RunOne.Law.RideKeyD
open Johnson.RunOne.Law.JoinKeyD

variable {Fr : VerifiableInference.Desc.Sound.Frame} {P M Wp : Type}

/-- What was handed to the chain, and the statement made of the riding part. -/
def pullK (x : TK P) : P × Statement := (x.2.2.2.2, stm x)

/-- At the riding part of a record. -/
theorem pullK_stK (p₀ : P) (i : ℕ) (s : FirstState) :
    pullK (stK p₀ i s) = (p₀, { codes := s.d.st.codes, oracles := s.d.st.oracles.map bareO }) :=
  rfl

variable (dec' : (P × Statement) × Fr.E.Str → Option M)
  (cond' : (P × Statement) × Fr.E.Str → Prop) (Oth' : P × Statement → M × Wp → Prop)

/-- **Pulled back, the letters are blind to the lists of rows and claims.** -/
theorem blind_pull :
    Blind (fun a : TK P × Fr.E.Str => dec' (pullK a.1, a.2)) (fun a => cond' (pullK a.1, a.2))
      fun x w => Oth' (pullK x) w := by
  intro x x' y h1 h2 h3
  have e : pullK x = pullK x' := by
    unfold pullK stm
    rw [h1, h2, h3]
  refine ⟨?_, ?_, fun w => ?_⟩
  · show dec' (pullK x, y) = dec' (pullK x', y)
    rw [e]
  · show cond' (pullK x, y) ↔ cond' (pullK x', y)
    rw [e]
  · show Oth' (pullK x) w ↔ Oth' (pullK x') w
    rw [e]

/-- **Pulled back, they read of the oracles what they read before.** -/
theorem lowDec_pull {c : ℕ}
    (h : ∀ (x : P × Statement) (y y' : Fr.E.Str), y.1 = y'.1 →
      (∀ q : OnBytes.Maker.PosL Fr.all, (Fr.all.get q.1).no < c → y.2 q = y'.2 q) →
      dec' (x, y) = dec' (x, y') ∧ (cond' (x, y) ↔ cond' (x, y'))) :
    LowDec (fun a : TK P × Fr.E.Str => dec' (pullK a.1, a.2)) (fun a => cond' (pullK a.1, a.2)) c :=
  fun x y y' h1 h2 => h (pullK x) y y' h1 h2

end Johnson.RunOne.Law.LettersAt

#print axioms Johnson.RunOne.Law.LettersAt.pullK_stK
#print axioms Johnson.RunOne.Law.LettersAt.blind_pull
#print axioms Johnson.RunOne.Law.LettersAt.lowDec_pull
