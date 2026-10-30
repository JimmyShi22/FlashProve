-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/PlannedZFull.lean: the planner returns at the three full-size public files as
Ladder/Stored.lean spells them (`VerifierAndGoals.storedPublicFiles`), at every digest of 32 bytes.

Why. Two routines of the library plan from the three public files. The frame of
`VerifierAndGoals.theDescription` lays its plan at a constant in the digest's place: `fixedConfigurationDigest`, 32 bytes of
0x01 (Johnson/Goal/Description/Plan.lean; Johnson/Desc/TheCfg.lean), which is `Key.fixedDigest`
(Johnson/Desc/Key/Slot.lean). `Model.Verify.planned`
(OnBytes/Model/Verify.lean), in the library's rendering of the C++ verifier's checking calls, plans
at the digest of the three files themselves. `madeAt_zFull` (Johnson/AtFull/Made/MadeAtZFull.lean)
speaks at the constant alone. The facts beneath it read of the digest its length and no more, so the
return stands at both. verify() is compiled from the first: for it take `plannedAtO_zFull_any` at
`fixedConfigurationDigest` (the frame's own `thePlanLaid`: lean/AtFullSide/Planner/MadeReturns.lean); `planned_zFull`
speaks of the second alone.

What it says, each under
  hsz   the layout file of `VerifierAndGoals.storedPublicFiles` has 224,975 bytes, and
  b₁    it reads as the written value `LW`:
  `madeAt_zFull_any`      there is a public part X₀ that `publicOfO` returns at the three files (at
                          the second hash function `OnBytes.secondHashFunction`), and at every cfg of 32 bytes
                          `Key.madeAt X₀ storedPublicFiles.lay cfg` returns some m, whose plan holds X₀ and cfg.
  `plannedAtO_zFull_any`  at every cfg of 32 bytes `plannedAtO secondHashFunction` returns at the three files:
                          all three steps of the planner (`publicOfO`, `chainsOf`, `builtOf`).
  `planned_zFull`         `Model.Verify.planned storedPublicFiles.pol storedPublicFiles.KL (some storedPublicFiles.lay)` returns: at
                          the files' own digest.

How. `publicOfO_zFull_all` (Johnson/AtFull/Public/AtX0All.lean) and `madeAt_fields`
(Johnson/AtFull/Made/MadeAtJoinD.lean), which is general in the digest; `plannedAtO_of_madeAt`
(Johnson/Goal/Description/PlanKey.lean); `plannedAtO_older`
(Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean) and `planned_eq` (OnBytes/Tie/ChainsAtCfg.lean):
at the second hash function itself and the files' own digest `plannedAtO` is `planned`;
`size_configurationDigest` (OnBytes/K/SeedRec.lean): that digest has 32 bytes.

Limits. hsz and b₁ are premises here: closed facts on the layout file, shown in a side library that
is built with a larger thread stack: one constant beneath them, `lay_chars`
(AtFullSide/Layout/TieRfl.lean), was seen to fail in Lean's kernel at the default stack. They are
`lay_size` (AtFullSide/Layout/Size.lean) and `layoutRead_full` (AtFullSide/LayoutRead/Full.lean). At
`VerifierAndGoals.storedPublicFiles` alone: nothing is said of other files in the goals' scope, nor of the files whose
policy has limits (`VerifierAndGoals.zGap`). `VerifierAndGoals.storedPublicFiles` is three terms written in Ladder/Stored.lean: no
Lean code ties them to the top-level folder examples/; the example's weights are synthetic. That a
planner returns is not that a verifier accepts anything: no key file, entry file or proof file is
read here. Nothing on soundness.
-/
import Johnson.AtFull.Made.MadeAtZFull
import Johnson.Goal.Description.PlanKey
import Johnson.Desc.Ok.PlanWritten.PublicAtLaws
import OnBytes.Tie.ChainsAtCfg
import OnBytes.K.SeedRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Model OnBytes.Model.Verify
open VerifiableInference.PlanWritten (publicOfO plannedAtO plannedAtO_older)
open Johnson.AtFull.LayoutRead (LW)

/-- **`Key.madeAt` returns at the three files of `VerifierAndGoals.storedPublicFiles`, at every digest of 32 bytes**,
under two closed facts on the layout file. -/
theorem madeAt_zFull_any (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (b₁ : Plan.layoutRead VerifierAndGoals.storedPublicFiles.lay = some LW) :
    ∃ X₀ : Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ ∧
      ∀ cfg : ByteArray, cfg.size = 32 →
        ∃ m, VerifiableInference.Desc.Key.madeAt X₀ VerifierAndGoals.storedPublicFiles.lay cfg = .ok m ∧
          m.p.X = X₀ ∧ m.p.cfg = cfg := by
  obtain ⟨X₀, hX, hG, hA, hV, ha, P, hc⟩ := Johnson.AtFull.Public.publicOfO_zFull_all hsz
  refine ⟨X₀, hX, fun cfg h32 => ?_⟩
  obtain ⟨m, hm, e1, e2, -⟩ := madeAt_fields P hG hA hV b₁ h32 ha hc
  exact ⟨m, hm, e1, e2⟩

/-- **All three steps of the planner return at the three files of `VerifierAndGoals.storedPublicFiles`, at every digest
of 32 bytes.** -/
theorem plannedAtO_zFull_any (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (b₁ : Plan.layoutRead VerifierAndGoals.storedPublicFiles.lay = some LW) {cfg : ByteArray} (h32 : cfg.size = 32) :
    ∃ p, plannedAtO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) cfg =
      .ok p ∧ p.cfg = cfg := by
  obtain ⟨X₀, hX, h⟩ := madeAt_zFull_any hsz b₁
  obtain ⟨m, hm, -, e2⟩ := h cfg h32
  exact ⟨m.p, (FlashProve.plannedAtO_of_madeAt hX hm).1, e2⟩

/-- **`Model.Verify.planned` returns at the three files of `VerifierAndGoals.storedPublicFiles`**, at their own digest,
under two closed facts on the layout file. -/
theorem planned_zFull (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (b₁ : Plan.layoutRead VerifierAndGoals.storedPublicFiles.lay = some LW) :
    ∃ p, planned VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok p := by
  have h32 : (configuration VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.lay VerifierAndGoals.storedPublicFiles.KL).size = 32 :=
    OnBytes.K.size_configurationDigest _
  obtain ⟨p, hp, -⟩ := plannedAtO_zFull_any hsz b₁ h32
  refine ⟨p, ?_⟩
  rw [OnBytes.Tie.planned_eq, Option.getD_some, ← plannedAtO_older]
  exact hp

#print axioms Johnson.AtFull.Made.madeAt_zFull_any
#print axioms Johnson.AtFull.Made.plannedAtO_zFull_any
#print axioms Johnson.AtFull.Made.planned_zFull

end Johnson.AtFull.Made
