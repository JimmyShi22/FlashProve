-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/PhiMore.lean: HOW SEVERAL KINDS SHARE THE FREE FIELD OF THE ONE φ
(Johnson/Desc/First/Link/Law/PhiAll.lean: `phiAll u ψ`, field `more`). Two small theorems.

`more_is`: the field `more` of `phiAll u ψ s` is `ψ s`: so a kind reads what it has laid into ψ by
a projection of φ. `rests_pair`: two letters that rest under the writings behind the draw rest
together: so `Rests` is to be proved of each kind's own ψ alone, and the one φ takes the pair.

Limits. Tools. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.PhiAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.PhiAll
open OnBytes.Model
open VerifiableInference.Desc.First (S)

variable {β γ : Type}

theorem more_is (u : HTailF2) (ψ : S → β) (s : S) : (phiAll u ψ s).more = ψ s := rfl

/-- Two letters that rest, rest together. -/
theorem rests_pair (u : HTailF2) {ψ₁ : S → β} {ψ₂ : S → γ} (h₁ : Rests u ψ₁) (h₂ : Rests u ψ₂) :
    Rests u fun s => (ψ₁ s, ψ₂ s) where
  fork := fun s F => by rw [h₁.fork, h₂.fork]
  set := fun s a => by rw [h₁.set, h₂.set]
  tl := fun s tl tl' h hb => by rw [h₁.tl s tl tl' h hb, h₂.tl s tl tl' h hb]
  wrote := fun s a G s' h => by rw [h₁.wrote s a G s' h, h₂.wrote s a G s' h]
  head := fun s a G h => by rw [h₁.head s a G h, h₂.head s a G h]

end VerifiableInference.Desc.PhiAll

#print axioms VerifiableInference.Desc.PhiAll.more_is
#print axioms VerifiableInference.Desc.PhiAll.rests_pair
