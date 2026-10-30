-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Planner/PublicReturns.lean: the reader of the public files, `Model.Verify.publicOf`
(OnBytes/Model/VerifyPublic.lean), returns at the three full-size public files as Ladder/Stored.lean
spells them (`VerifierAndGoals.storedPublicFiles`): no premise. One statement: a call and a rewriting. No definition: no
goal is stated.
Why. `madeAt_zFull_returns` (MadeReturns.lean) speaks of `publicOfO`, the reader's text with the
format's second hash function as a letter, at `OnBytes.secondHashFunction`. Other files of the library speak of
`publicOf`, which calls that hash by name. At `secondHashFunction` the two are one text (`publicOfO_older`,
Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean). A run of Lean's evaluator (#eval, #guard) can show
such a return too, but proves nothing; this is a theorem.
  **`publicOf_zFull_returns`**: there is an X₀ that `publicOf` returns at the three files;
    `publicOfO OnBytes.secondHashFunction` returns the same X₀; and at every cfg of 32 bytes `Key.madeAt X₀
    storedPublicFiles.lay cfg` returns.
Limits. Those of MadeReturns.lean: AT `VerifierAndGoals.storedPublicFiles` ALONE; `VerifierAndGoals.storedPublicFiles` is three terms written in
Ladder/Stored.lean, and no Lean code ties them to the repository's folder examples/; that a reader
returns is not that a verifier accepts anything. Nothing is said of what X₀ holds. This file lies in
the side library AtFullSide, which is built with a larger thread stack (lake build AtFullSide).
Nothing on soundness, on a binding of the commitment (the opening form, `BindsWith`), on correctness
of extraction, on completeness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import AtFullSide.Planner.MadeReturns
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.Planner
open OnBytes OnBytes.Model OnBytes.Model.Verify
open VerifiableInference.PlanWritten (publicOfO publicOfO_older)

/-- **`Model.Verify.publicOf` returns at the three files of `VerifierAndGoals.storedPublicFiles`**, and its value is the
one at which the steps behind return. -/
theorem publicOf_zFull_returns :
    ∃ X₀ : Public,
      publicOf VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      ∀ cfg : ByteArray, cfg.size = 32 →
        ∃ m, VerifiableInference.Desc.Key.madeAt X₀ VerifierAndGoals.storedPublicFiles.lay cfg = .ok m := by
  obtain ⟨X₀, hX, h⟩ := madeAt_zFull_returns
  refine ⟨X₀, ?_, hX, fun cfg h32 => ?_⟩
  · rw [← publicOfO_older]
    exact hX
  · obtain ⟨m, hm, -⟩ := h cfg h32
    exact ⟨m, hm⟩

end AtFullSide.Planner

#print axioms AtFullSide.Planner.publicOf_zFull_returns
