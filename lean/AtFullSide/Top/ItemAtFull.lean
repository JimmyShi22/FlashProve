-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Top/ItemAtFull.lean: at `VerifierAndGoals.storedPublicFiles` and at `VerifierAndGoals.zGap`, for every request of the
right length, the item "request" is made and its comparison with the public part accepts: with no
premise on the layout file.

What it says.
* `item_zFull`, `item_zGap`: the theorems of these names in Johnson/AtFull/Item/ItemAtFull.lean and
  ItemAtGap.lean, with their premise on the layout file's size shown (`lay_size`,
  AtFullSide/Layout/Size.lean). That `publicOfO` returns X stays a premise, so that the caller names
  X.
* `item_zFull_whole`, `item_zGap_whole`: no premise: `publicOfO` returns, what it returns has 1,024
  tokens, and there the item is made and the comparison accepts.
* `gap_item_refused`, `full_item_refused`: the negative facts of
  Johnson/AtFull/Item/ItemSaysNo.lean, with the same premise shown.

Why here. The fact on the layout file's size is shown in this side library, which is built with a
larger thread stack than the files under lean/Johnson/. Nothing in the main library imports this
file, so only a build of the side library shows a break in it; no independent checker has replayed
it.

Limits. Those of the files under lean/Johnson/AtFull/Item/, whole: two of the seven steps of the
tests on an instance, and the caller has to show that they stand at `ProofFile.holdBy`'s own arguments;
other places where a test on the public files can make the verifier reject everything are known;
that the verifier accepts any proof is not shown; terms that no Lean ties to files in a folder; the
earlier hash. Nothing on soundness, on binding or on hiding.
-/
import Johnson.AtFull.Item.ItemSaysNo
import AtFullSide.Layout.Size

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.Top
open OnBytes.Model.Verify VerifiableInference.PlanWritten

/-- At `VerifierAndGoals.storedPublicFiles`, at whatever `publicOfO` returns. -/
theorem item_zFull {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) :
    ∀ req : ByteArray, req.size = 4 * (X₀.T + 2) →
      ∃ it, Fmt.requestItem OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL req = some it ∧
        statementHeld X₀ it = .ok () :=
  Johnson.AtFull.Item.item_zFull Johnson.Unfolds.Layout.lay_size hX

/-- At `VerifierAndGoals.zGap`, at whatever `publicOfO` returns. -/
theorem item_zGap {X : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.KL (some VerifierAndGoals.zGap.lay) = .ok X) :
    ∀ req : ByteArray, req.size = 4 * (X.T + 2) →
      ∃ it, Fmt.requestItem OnBytes.secondHashFunction VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.KL req = some it ∧
        statementHeld X it = .ok () :=
  Johnson.AtFull.Item.item_zGap Johnson.Unfolds.Layout.lay_size hX

/-- **At `VerifierAndGoals.storedPublicFiles`, with no premise.** -/
theorem item_zFull_whole :
    ∃ X₀, publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
        .ok X₀ ∧ X₀.T = 1024 ∧
      ∀ req : ByteArray, req.size = 4 * (X₀.T + 2) →
        ∃ it, Fmt.requestItem OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL req = some it ∧
          statementHeld X₀ it = .ok () := by
  obtain ⟨X₀, hX, -⟩ :=
    Johnson.AtFull.Public.publicOfO_zFull_all Johnson.Unfolds.Layout.lay_size
  exact ⟨X₀, hX, Johnson.AtFull.Item.tokens_zFull Johnson.Unfolds.Layout.lay_size hX,
    item_zFull hX⟩

/-- **At `VerifierAndGoals.zGap`, with no premise.** -/
theorem item_zGap_whole :
    ∃ X, publicOfO OnBytes.secondHashFunction VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.KL (some VerifierAndGoals.zGap.lay) =
        .ok X ∧ X.T = 1024 ∧
      ∀ req : ByteArray, req.size = 4 * (X.T + 2) →
        ∃ it, Fmt.requestItem OnBytes.secondHashFunction VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.KL req = some it ∧
          statementHeld X it = .ok () := by
  obtain ⟨X₀, hX, -⟩ :=
    Johnson.AtFull.Public.publicOfO_zFull_all Johnson.Unfolds.Layout.lay_size
  have hG := LPFPol.gap_of_full hX
  rw [← VerifierAndGoals.lay_zGap] at hG
  exact ⟨_, hG, (Johnson.AtFull.Item.facts_zGap Johnson.Unfolds.Layout.lay_size hG).2.2,
    item_zGap hG⟩

/-- At the public part of `VerifierAndGoals.storedPublicFiles` every item made of `VerifierAndGoals.zGap`'s files is refused. -/
theorem gap_item_refused {X₀ : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) (req it : ByteArray)
    (hit : Fmt.requestItem OnBytes.secondHashFunction VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.KL req = some it) :
    statementHeld X₀ it ≠ .ok () :=
  Johnson.AtFull.Item.gap_item_refused Johnson.Unfolds.Layout.lay_size hX req it hit

/-- At the public part of `VerifierAndGoals.zGap` every item made of `VerifierAndGoals.storedPublicFiles`'s files is refused. -/
theorem full_item_refused {X : Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.zGap.pol VerifierAndGoals.zGap.KL (some VerifierAndGoals.zGap.lay) = .ok X)
    (req it : ByteArray)
    (hit : Fmt.requestItem OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL req = some it) :
    statementHeld X it ≠ .ok () :=
  Johnson.AtFull.Item.full_item_refused Johnson.Unfolds.Layout.lay_size hX req it hit

end AtFullSide.Top

#print axioms AtFullSide.Top.item_zFull
#print axioms AtFullSide.Top.item_zGap
#print axioms AtFullSide.Top.item_zFull_whole
#print axioms AtFullSide.Top.item_zGap_whole
#print axioms AtFullSide.Top.gap_item_refused
#print axioms AtFullSide.Top.full_item_refused
