-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/RuleOwnProofs.lean: the proofs of the statements of
Johnson/Desc/Sound/RuleOwn.lean. Theorems and the lemmas that they need.

Limits: those of that file.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.RuleOwn
import Johnson.Desc.Sound.RuleErrProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound

theorem ownOfRule : OwnOfRule := by
  intro S Cl W ι D C F p on on' means In Out comp dec rule ceil k f hc hm hb hpin hprom hlaw
  refine goodInOfRule S Cl W C F p on on' (relAt means In) (relAt means Out)
    (fun a => rule a (dec a)) ceil k f (fun a g ha => hc a (dec a) g ha) hm hb hprom ?_
  intro a τ b w ha hn hout hw
  have e := hpin a τ b w ha hout hw
  exact hlaw a τ b w ha (by rw [e]; exact hn) hout hw

end VerifiableInference.Desc.Sound
