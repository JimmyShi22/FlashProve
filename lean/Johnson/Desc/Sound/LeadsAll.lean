-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/LeadsAll.lean: THE TOKEN ALONG THE STEPS, WITHOUT ASKING THAT A REPLY IS HEARD.
Two theorems. Rules on relations; no protocol occurs here.

What is said. Johnson/Desc/Sound/LeadsE.lean's `steps_token` takes "t is heard at the last
statement" as a premise and yields a witness at the first statement whose token is t. The witness
that its proof builds does not hang on t. `steps_token_all`: along n + 1 steps every witness at the
last statement gives ONE witness at the first such that, if no reply is heard at the first
statement, its token is EVERY reply that the last statement's record holds (there is at most one).
Nobody has to show that a reply is heard at the chain's end; who knows one (the last test's yes)
spends it. `steps_token` follows from it by one application. `steps_on`: along the steps the promise
behind the last one holds.

Silly members. At rep := fun _ => none the second half says nothing, and `TokStep` asks that every
extractor leaves the token. At a rep that is "some" from the start the second half is idle: the
premise "none at the first statement" fails.

Limits: those of LeadsE.lean. Nothing on soundness, completeness or hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.LeadsE

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open _root_.Iop.Reduction (steps)

variable {W A Tok : Type} (on : ℕ → A → Prop) (R : ℕ → A → W → Prop) (E : ℕ → A → A → W → W)
  (tok : W → Tok) (rep : A → Option Tok)

/-- **ONE WITNESS THROUGH THE CHAIN, AND ITS TOKEN, WHATEVER IS HEARD AT THE END.** -/
theorem steps_token_all : ∀ (n i : ℕ) (a c : A), steps (QT on R E tok rep) i n a c →
    ∀ w, R (i + 1 + n) c w →
      ∃ w₀, R i a w₀ ∧ (rep a = none → ∀ t, rep c = some t → tok w₀ = t)
  | 0, i, a, c, h, w, hw => ⟨E i a c w, h.1.2 w hw, fun ha t e => h.2.lays ha t e w⟩
  | n + 1, i, a, c, ⟨b, hb, hc⟩, w, hw => by
    have e' : i + 1 + (n + 1) = i + 1 + 1 + n := by omega
    obtain ⟨w₁, h₁, ht⟩ := steps_token_all n (i + 1) b c hc w (e' ▸ hw)
    refine ⟨E i a b w₁, hb.1.2 w₁ h₁, fun ha t e => ?_⟩
    cases hr : rep b with
    | none => rw [hb.2.keeps hr w₁]; exact ht hr t e
    | some t' =>
      have : rep c = some t' := steps_stays on R E tok rep n (i + 1) b c t' hc hr
      have ett : t' = t := Option.some.inj (this.symm.trans e)
      rw [hb.2.lays ha t' hr w₁, ett]

/-- Along n + 1 steps the promise behind the last one holds. -/
theorem steps_on : ∀ (n i : ℕ) (a c : A), steps (QT on R E tok rep) i n a c → on (i + 1 + n) c
  | 0, _, _, _, h => h.1.1
  | n + 1, i, _, c, ⟨b, _, hc⟩ => by
    have e' : i + 1 + (n + 1) = i + 1 + 1 + n := by omega
    exact e' ▸ steps_on n (i + 1) b c hc

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.steps_token_all
#print axioms VerifiableInference.Desc.Sound.steps_on
