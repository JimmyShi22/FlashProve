-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K11/ClaimIsOfK3.lean: the proof of `HeadClaimIsOfK3`
(Honest/K11/ClaimIsOfK3Statement.lean), to the letter. A lemma; none of the library's goals.

How: one term, which the lookups' authors wrote out for us: `headClaimIsOfKeysBare`
(ThreeTiesBare.lean of this folder) at keys := `headKeysOfK3 cF`; its fourth premise is
`head_keys_tie` (Honest/K3/Law/Thread/HeadCallsTie.lean) at the ground Bs.G₀: there the number of
rounds ahead is written out; it is `roundsAhead` by unfolding.

Limits. Those of the statement. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K11.ClaimIsOfK3Statement
import Johnson.Desc.ProofFile.Honest.K11.ThreeTiesBare

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K11
open ProofFile.Honest.K3.Law.AtThr (headKeysOfK3 head_keys_tie)

/-- **`HeadClaimIs` at the bare list, with no tie left among its premises.** -/
theorem headClaimIsOfK3 : HeadClaimIsOfK3 := by
  intro Z D r Zp Np cF xP Bs link claims h hB hcl
  exact headClaimIsOfKeysBare (headKeysOfK3 cF) Z D r Zp Np cF xP Bs link claims h hB hcl
    (head_keys_tie h Bs.G₀)

end ProofFile.Honest.K11

-- The line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K11.headClaimIsOfK3
