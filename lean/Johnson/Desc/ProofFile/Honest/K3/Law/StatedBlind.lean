-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/StatedBlind.lean: the sub-protocol which the lookups' lot
states decides without reading a sealed digest. So what Honest/K3/Law/Stated.lean shows of its
`decide` can be carried to its `Block.step` by `step_yes` (Honest/K3/Law/StepYes.lean). Theorems.

Terms. Honest/K3/GLOSSARY.md ("decision", "lot", "step", "sub-protocol").

What is shown.
  `blind_of_decidesFrom`: a sub-protocol of which `DecidesFrom` (Stated.lean) holds decides without
    reading a sealed digest.
  `theStated_blind`: so does the lot's sub-protocol at every address.

Hypotheses that remain. `h`: `DecidesFrom` (in the first); `theStated` returns the sub-protocol at
the address (in the second).

Users. This file is imported by Honest/K3/Law/StatedMember.lean.

Limits. Nothing is said on whether the decision accepts.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Stated
import Johnson.Desc.ProofFile.Honest.K3.Law.StepYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes.Model (Aff)
open VerifiableInference.Desc (Block Place noDigest)
open VerifiableInference.Desc.K3 (theStated Readers)
open ProofFile.Honest.K3.NoDigest (decideVia_noDigest)

local notation "FS" => VerifiableInference.Desc.First.S

theorem blind_of_decidesFrom {Cl : Type} {claim : Aff → Cl} {X : OnBytes.Model.Verify.Public}
    {a : Place} {b : Block FS Cl} {q : Bool} (h : DecidesFrom claim X a b q) : DecidesBlind b := by
  obtain ⟨i, digits, p, _, _, _, _, h⟩ := h
  intro s rs gs
  rcases h with ⟨_, h⟩ | ⟨_, f, _, h⟩
  · rw [h, h, decideVia_noDigest]
  · rw [h, h, ← List.map_take, decideVia_noDigest]

/-- **The lot's sub-protocol decides without reading a sealed digest.**
Conditional on there being a sub-protocol at the address. -/
theorem theStated_blind {Cl : Type} (claim : Aff → Cl) (readers : Nat → Option (Readers FS))
    (X : OnBytes.Model.Verify.Public) (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape)
    (a : Place) (b : Block FS Cl) (h : theStated claim readers X codes shape a = some b) :
    DecidesBlind b :=
  blind_of_decidesFrom (theStated_decides claim readers X codes shape a b h)

#print axioms ProofFile.Honest.K3.Law.blind_of_decidesFrom
#print axioms ProofFile.Honest.K3.Law.theStated_blind

end ProofFile.Honest.K3.Law
