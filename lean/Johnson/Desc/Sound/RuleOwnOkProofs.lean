-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/RuleOwnOkProofs.lean: the proofs of the statements of
Johnson/Desc/Sound/RuleOwnOk.lean. Theorems and the lemmas that they need.

Limits: those of that file.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.RuleOwnOk
import Johnson.Desc.Sound.RuleOwnProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound

theorem ownOfRuleOk : OwnOfRuleOk := by
  intro S Cl W ι D C F p on on' means In Out comp dec rule ceil k f ok hc hm hb hpin hview hprom
    hlaw
  exact ownOfRule S Cl W ι D C F p on on' means In Out comp dec rule ceil k f hc hm hb hpin
    (fun a τ b ha hn hout => hprom a τ b ha (hview a τ b ha hout) hn hout)
    (fun a τ b w ha hn hout hw => hlaw a τ b w ha (hview a τ b ha hout) hn hout hw)

end VerifiableInference.Desc.Sound
