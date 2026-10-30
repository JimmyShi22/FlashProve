-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K3/Term/NoLookupInTheLaterChains.lean: the kind "lookup" (K3): where the
maker of the proof file's description (`onlineDescription`) returns F: no member of F's shared chain, and none of
its second chain, stands at a place of the kind K3. No definition, two theorems; nothing is evaluated.

  `noLookupInTheSharedChain`   by `no_other_kind` (Johnson/Desc/K14/Law/SharedKinds.lean): the shared
                               chain's members bear four kinds, none of them K3
  `noLookupInTheSecondChain`   by `second_kinds` (Johnson/Desc/ProofFile/Law/LaterKinds.lean) at
                               `IM.seat_open` (Johnson/IMR/SeatOpen.lean): the second chain's bear three

Hypotheses that remain. hF: that `onlineDescription` returns F. No test on the plan is asked.

Limits. On places' kinds alone.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.IMR.SeatOpen
import Johnson.Desc.K14.Law.SharedKinds
import Johnson.Desc.ProofFile.Law.LaterKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Term
open VerifiableInference.Desc (KindName FileDescription)

variable {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}

/-- No member of the shared chain stands at a place of the kind K3. Conditional: `onlineDescription` returns F.
-/
theorem noLookupInTheSharedChain (hF : onlineDescription o pol lay KL = .ok F) :
    ∀ b ∈ F.shared.blocksInOrder, b.place.kind ≠ KindName.K3 :=
  Desc.K14.Law.no_other_kind hF KindName.K3 (by unfold Desc.K14.Law.SharedKind; decide)

/-- Nor does a member of the second chain. Conditional: `onlineDescription` returns F. -/
theorem noLookupInTheSecondChain (hF : onlineDescription o pol lay KL = .ok F) :
    ∀ b ∈ F.second.blocksInOrder, b.place.kind ≠ KindName.K3 := by
  obtain ⟨Zq, Bs, base, c, A, B, O⟩ := IM.seat_open hF
  have hd := O.desc
  subst hd
  intro b hb e
  have hk := ProofFile.Law.second_kinds O.second b hb
  rw [e] at hk
  rcases hk with hk | hk | hk <;> cases hk

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.noLookupInTheSharedChain
#print axioms ProofFile.Honest.K3.Term.noLookupInTheSecondChain
