-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/Spell/SaltOfReturns.lean: where the first two steps of the library's planner return at
public files in scope, the plan's salt there has 40 bytes: `Bind.Cpp.SaltAt Z`
(Johnson/Bind/Cpp/Defs.lean). Two statements with short proofs, general in Z. No definition: no goal
is stated.
Why. `SaltAt Z` is a premise of the leaf's equation (Leaf.lean). In scope it says that the plan's
seat holds a plan (`Bind.Cpp.saltAt_iff`, Johnson/Bind/Cpp/SaltAt.lean). Whoever shows of stored
public files that `publicOfO` and the key's maker `madeAt` return there has it by these two
statements.
  `planLaid_of_returns`: where `publicOfO OnBytes.secondHashFunction` returns X₀ and `Key.madeAt X₀ Z.lay
    fixedDigest` returns m, the plan's seat `thePlanLaid (asDescriptionFiles Z)` holds the plan made of m's. It
    is the first step in the proof of `thePlan_of_made` (Johnson/Goal/Description/PlanKey.lean),
    stated by itself; through `plannedAtO_of_madeAt` (the same file).
  **`saltAt_of_returns`**: so, in scope, `SaltAt Z`.
Limits. THE TWO RETURNS ARE PREMISES: they are shown at no public files here. Nothing on any
committer, on any program, on soundness, on a binding of the commitment (the opening form,
`BindsWith`), on correctness of extraction, on completeness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Bind.Cpp.SaltAt
import Johnson.Goal.Description.PlanKey

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Bind.Spell
open VerifierAndGoals FlashProve Bind.Cpp
open VerifiableInference.PlanWritten (publicOfO plannedAtO)
open VerifiableInference.Desc.Key

/-- Where the planner's first two steps return, the plan's seat holds a plan. -/
theorem planLaid_of_returns {Z : PublicFiles} {X₀ : OnBytes.Model.Verify.Public}
    {m : Johnson.G.OfPlan.Made}
    (hX : publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : madeAt X₀ Z.lay fixedDigest = .ok m) :
    thePlanLaid (asDescriptionFiles Z) = .ok (VerifiableInference.OnPublicFiles.bigReq m.p) := by
  show (plannedAtO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) fixedConfigurationDigest).map
    VerifiableInference.OnPublicFiles.bigReq = _
  rw [show fixedConfigurationDigest = fixedDigest from rfl, (plannedAtO_of_madeAt hX hm).1]
  rfl

/-- **In scope, where they return, the plan's salt has 40 bytes.** -/
theorem saltAt_of_returns {Z : PublicFiles} (hZ : InScope Z = true) {X₀ : OnBytes.Model.Verify.Public}
    {m : Johnson.G.OfPlan.Made}
    (hX : publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : madeAt X₀ Z.lay fixedDigest = .ok m) : SaltAt Z :=
  (saltAt_iff hZ).2 ⟨_, planLaid_of_returns hX hm⟩

end Bind.Spell

#print axioms Bind.Spell.planLaid_of_returns
#print axioms Bind.Spell.saltAt_of_returns
