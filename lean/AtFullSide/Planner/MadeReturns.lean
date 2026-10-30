-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Planner/MadeReturns.lean: the library's planner returns at the three full-size public
files as Ladder/Stored.lean spells them (`VerifierAndGoals.storedPublicFiles`): no premise is left. The first three
statements are those of Johnson/AtFull/Made/PlannedZFull.lean with their two premises paid: calls
alone. The last two follow from the first in a few lines. No definition: no goal is stated.
Why. A run of Lean's evaluator (#eval, #guard) can show such a return too, but proves nothing; these
are theorems. Their closed facts are proved by evaluation in Lean's kernel (decide +kernel,
kernel_rfl): no compiled code, and no axiom beyond Lean's three (propext, Classical.choice,
Quot.sound).
The two premises that are paid here: the layout file of `VerifierAndGoals.storedPublicFiles` has 224,975 bytes
(`Johnson.Unfolds.Layout.lay_size`, AtFullSide/Layout/Size.lean), and it reads as the written value
`LW` (`Johnson.AtFull.LayoutRead.layoutRead_full`, AtFullSide/LayoutRead/Full.lean).
  **`madeAt_zFull_returns`**: there is a public part X₀ that `publicOfO` returns at the three files
    (at the second hash function `OnBytes.secondHashFunction`), and at every cfg of 32 bytes `Key.madeAt X₀
    storedPublicFiles.lay cfg` returns some m, whose plan holds X₀ and cfg.
  `plannedAtO_zFull_returns`: at every cfg of 32 bytes `plannedAtO secondHashFunction` returns at the three
    files: all three steps of the planner.
  `planned_zFull_returns`: `Model.Verify.planned` (OnBytes/Model/Verify.lean: the library's
    rendering of the C++ verifier's checking calls) returns at the three files, at their own digest.
  `madeAt_zFull_at_fixed`: the first at the constant `Key.fixedDigest`, 32 bytes of 0x01, at which
    the frame of `VerifierAndGoals.theDescription` lays its plan.
  `planLaid_zFull`: so the plan's seat of that frame, `thePlanLaid (asDescriptionFiles storedPublicFiles)`
    (Johnson/Goal/Description/Plan.lean), holds a plan (`planLaid_of_returns`,
    Johnson/Bind/Spell/SaltOfReturns.lean).
What else it pays. It goes toward completeness. That the description's test on the public files
(`protocolDataWellFormed`) says yes at these files wants more: that the key file's and the proof file's makers
return too. That is not shown in this file; `AtFullSide.Top.theProofLaid_zFull_returns` and
`AtFullSide.Top.theLive_zFull` (AtFullSide/Top/LiveAtFull.lean) show it. `SaltAt storedPublicFiles` follows
(SaltAtFull.lean).
Limits. AT `VerifierAndGoals.storedPublicFiles` ALONE: nothing is said of other files in the goals' scope. `VerifierAndGoals.storedPublicFiles`
is three terms written in Ladder/Stored.lean: no Lean code ties them to the repository's folder
examples/; the example's weights are synthetic and are no part of these statements. At the second
hash function `OnBytes.secondHashFunction`. That a planner returns is not that a verifier accepts anything: no
key file, entry file or proof file is read here. This file lies in the side library AtFullSide,
which is built with a larger thread stack (lake build AtFullSide): one constant beneath it,
`lay_chars` (AtFullSide/Layout/TieRfl.lean), was seen to fail in Lean's kernel at the default stack,
and passes at 128 MB. Nothing on soundness, on a binding of the commitment (the opening form,
`BindsWith`), on correctness of extraction or on hiding.
Terms: lean/GLOSSARY.md.

-/
import AtFullSide.Layout.Size
import AtFullSide.LayoutRead.Full
import Johnson.AtFull.Made.PlannedZFull
import Johnson.Bind.Spell.SaltOfReturns
import Johnson.Desc.Key.SlotIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.Planner
open OnBytes OnBytes.Model OnBytes.Model.Verify
open VerifiableInference.PlanWritten (publicOfO plannedAtO)
open VerifiableInference.Desc.Key (fixedDigest fixedDigest_size)
open Johnson.Unfolds.Layout (lay_size)
open Johnson.AtFull.LayoutRead (layoutRead_full)

/-- **`Key.madeAt` returns at the three files of `VerifierAndGoals.storedPublicFiles`, at every digest of 32 bytes.** -/
theorem madeAt_zFull_returns :
    ∃ X₀ : Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      ∀ cfg : ByteArray, cfg.size = 32 →
        ∃ m, VerifiableInference.Desc.Key.madeAt X₀ VerifierAndGoals.storedPublicFiles.lay cfg = .ok m ∧
          m.p.X = X₀ ∧ m.p.cfg = cfg :=
  Johnson.AtFull.Made.madeAt_zFull_any lay_size layoutRead_full

/-- All three steps of the planner return there, at every digest of 32 bytes. -/
theorem plannedAtO_zFull_returns {cfg : ByteArray} (h32 : cfg.size = 32) :
    ∃ p, plannedAtO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) cfg =
      .ok p ∧ p.cfg = cfg :=
  Johnson.AtFull.Made.plannedAtO_zFull_any lay_size layoutRead_full h32

/-- `Model.Verify.planned` returns there, at the three files' own digest. -/
theorem planned_zFull_returns :
    ∃ p, planned VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok p :=
  Johnson.AtFull.Made.planned_zFull lay_size layoutRead_full

/-- At the constant at which the description's frame lays its plan. -/
theorem madeAt_zFull_at_fixed :
    ∃ (X₀ : Public) (m : Johnson.G.OfPlan.Made),
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      VerifiableInference.Desc.Key.madeAt X₀ VerifierAndGoals.storedPublicFiles.lay fixedDigest = .ok m := by
  obtain ⟨X₀, hX, h⟩ := madeAt_zFull_returns
  obtain ⟨m, hm, -⟩ := h fixedDigest fixedDigest_size
  exact ⟨X₀, m, hX, hm⟩

/-- The plan's seat of the description's frame holds a plan there. -/
theorem planLaid_zFull : ∃ G, FlashProve.thePlanLaid (VerifierAndGoals.asDescriptionFiles VerifierAndGoals.storedPublicFiles) = .ok G := by
  obtain ⟨X₀, m, hX, hm⟩ := madeAt_zFull_at_fixed
  exact ⟨_, Bind.Spell.planLaid_of_returns hX hm⟩

end AtFullSide.Planner

#print axioms AtFullSide.Planner.madeAt_zFull_returns
#print axioms AtFullSide.Planner.plannedAtO_zFull_returns
#print axioms AtFullSide.Planner.planned_zFull_returns
#print axioms AtFullSide.Planner.madeAt_zFull_at_fixed
#print axioms AtFullSide.Planner.planLaid_zFull
