-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/SharedRuleClosed.lean: the statements of Johnson/Desc/Sound/SharedRule.lean that
lean on `FoldIsRow`, with its proof (Johnson/Desc/Sound/FoldIsRowProof.lean) laid in.

Limits: those of Johnson/Desc/Sound/SharedRule.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SharedRuleProofs
import Johnson.Desc.Sound.FoldIsRowProof

namespace VerifiableInference.Desc.Sound

theorem chainLink : ChainLink := chainLink_of foldIsRow
theorem chainLinkAt : ChainLinkAt := chainLinkAt_of chainLink
theorem slotOne : SlotOne := slotOne_of foldIsRow
theorem chainLinkBack : ChainLinkBack := chainLinkBack_of chainLink
theorem chainLinkActs : ChainLinkActs := chainLinkActs_of chainLinkBack

end VerifiableInference.Desc.Sound
