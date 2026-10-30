-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/LayersLinkRunsThroughBatching.lean: the first nine members of a
layers' link of the run on shapes, from sixteen closed Bools. layersLink_runsThroughBatching: at an
even link l below 24, if the sixteen are true, then at every record that publicOfO returns at the
stored full-size public files, from the written value B.beforeFirst the members 14 l + 1 to 14 l + 9
return startAfterBatching at that record: the written value B.afterBatching with the layers' parts
that member 14 l + 9 left. General in the link, the hint and the written values; nothing is
evaluated.

Why. layersLink_runs (LayersLinkRuns.lean in this folder) shows the whole link and does not state
what stands between its pieces. A test on the shape after member 14 l + 10 needs the run as far as
the start of the link's last piece.

How. The proof repeats the first four stretches of layersLink_runs's proof, since that law states
none of them by itself. The two could be made one: layersLink_runs would be this law chained with
its last stretch.

Limits. Those of LayersLinkRuns.lean's head. That any of the Bools is true is not shown here. The
shape that the nine members return is no written value: it holds, as a term, the run of the table's
own cell at member 14 l + 9. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkRuns

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Layers
open OnBytes OnBytes.Model
open Johnson.AtFull.Shape Johnson.AtFull.Shape.LayersPartsAside
open VerifiableInference.PlanWritten (publicOfO)
open VerifiableInference.Desc.First.Shape

/-- **The first nine members of a layers' link**: if sixteen Bools are true, ten on the group's plan
and six on the shapes, then at every record that publicOfO returns at the stored full-size public
files, from B.beforeFirst the members 14 l + 1 to 14 l + 9 of the run on shapes return
startAfterBatching at that record. -/
theorem layersLink_runsThroughBatching (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975)
    (hint : Nat → List (Nat × Nat)) (l : Nat) (hl : l < 24) (he : l % 2 = 0) (B : LayersBorders)
    (hP : PlanLines (l / 2)) (h1 : lineMembersOneToThree hint l B = true)
    (h2 : lineOwnRoundsGuards hint l B = true) (h3 : lineMergeRecords l B = true)
    (h4 : lineAfterOwnRounds hint l B = true) (h5 : lineMembersFiveToEight hint l B = true)
    (h6 : lineBatching hint l B = true) (X₀ : Verify.Public)
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) :
    (shapeL (LWn X₀)).runFrom (14 * l + 1) 9 B.beforeFirst =
      .ok (startAfterBatching hint l B X₀) := by
  have hy := y_at_zFull hsz hX
  have T : PlanTests (l / 2) X₀ :=
    ⟨atXLC_all hsz hP.covers hX, atXLC_all hsz hP.numbers hX, atXLC_all hsz hP.points hX,
      atXLC_all hsz hP.small hX, atXLC_all hsz hP.panels hX, atXLC_all hsz hP.claimsCount hX,
      atXLC_all hsz hP.claimsFirstHalf hX, atXLC_all hsz hP.claimsSecondHalf hX,
      atXLC_all hsz hP.claimEmbedding hX, atXLC_all hsz hP.join hX⟩
  have ev : (l % 2 == 0) = true := by simpa using he
  have c4 : TabL.cells (LWn X₀) (14 * l + 4) = TabL.k4 (LWn X₀) (l / 2) := by
    have e : TabL.cells (LWn X₀) (14 * l + 3 + 1) = (TabL.linkRow (LWn X₀) l).at 3 :=
      table_link _ _ _ _ l 3 hl (by omega)
    have e' : (TabL.linkRow (LWn X₀) l).at 3 =
        if l % 2 == 0 then TabL.k4 (LWn X₀) (l / 2) else TabL.k5 (LWn X₀) (l / 2) := rfl
    rw [e', if_pos ev] at e
    exact e
  have c9 : TabL.cells (LWn X₀) (14 * l + 9) = TabL.batch (LWn X₀) l :=
    table_link _ _ _ _ l 8 hl (by omega)
  -- members 14 l + 1 … + 3
  have e1 : (shapeL (LWn X₀)).runFrom (14 * l + 1) 3 B.beforeFirst =
      .ok (startOwnRounds hint l B X₀) :=
    piece_runs hint hsz hX (.run 3 layersParts B.beforeOwnRounds) (14 * l + 1)
      (fun _ => B.beforeFirst) h1
  -- member 14 l + 4
  have f2 := atXLC_all hsz h2 hX
  obtain ⟨hp, hG⟩ := atPlan_plan f2
  have e2 : (shapeL (LWn X₀)).runFrom (14 * l + 4) 1 (startOwnRounds hint l B X₀) =
      .ok (startReads hint l B X₀) :=
    run_of_given hint hX 1 layersParts B.beforeReads (14 * l + 4) (startOwnRounds hint l B) (by
      obtain ⟨y, e, hy'⟩ := ownRounds_given hy T f2 (atXLC_all hsz h3 hX) (atXLC_all hsz h4 hX)
      exact ⟨y, by rw [runFrom_one, c4]; exact e, hy'⟩)
  -- members 14 l + 5 … + 8
  have e3 : (shapeL (LWn X₀)).runFrom (14 * l + 5) 4 (startReads hint l B X₀) =
      .ok (startBatching hint l B X₀) :=
    piece_runs hint hsz hX (.run 4 layersParts B.beforeBatching) (14 * l + 5) (startReads hint l B)
      h5
  -- member 14 l + 9
  have hI : OwnRecordHeard (LWn X₀).XG.layers hp (l / 2) (startBatching hint l B X₀).1 :=
    (ownRoundsCell_laysOwnHeard (LWn X₀) (l / 2) hG (ownRoundsLetter_atNumerals X₀ (l / 2) hG)
      (by rw [← c4, ← runFrom_one]; exact e2)).of_own (layersLinkRun_keepsOwn (LWn X₀) l hl he e3)
  have e4 : (shapeL (LWn X₀)).runFrom (14 * l + 9) 1 (startBatching hint l B X₀) =
      .ok (startAfterBatching hint l B X₀) :=
    run_of_given hint hX 1 layersParts B.afterBatching (14 * l + 9) (startBatching hint l B) (by
      obtain ⟨y, e, hy'⟩ := lessB_returns (atXLC_all hsz h6 hX)
      exact ⟨y,
          by rw [runFrom_one, c9]; exact layersBatchingLight_standsUnder (LWn X₀) l hl he hG hI e,
          hy'⟩)
  exact runFrom_chain _ (runFrom_chain _ (runFrom_chain _ e1 e2) e3) e4

end Johnson.AtFull.Shape.Layers

#print axioms Johnson.AtFull.Shape.Layers.layersLink_runsThroughBatching
