-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/LayersLinkRuns.lean: a layers' link of the run on shapes, from
seventeen closed Bools. layersLink_runs: at an even link l below 24, if the seventeen are true, then
from the written value B.beforeFirst the fourteen members 14 l + 1 to 14 l + 14 return the written
value B.afterLast, at every record that publicOfO returns at the stored full-size public files
(RunsAll, Johnson/AtFull/Shape/JoinAll.lean). General in the link, the hint and the six written
values; that the Bools are true is a premise; nothing is evaluated.

How the link is cut.
* Members 14 l + 1 to 14 l + 3: one Bool on the run.
* Member 14 l + 4, the layers' own rounds: by ownRounds_given (OwnRoundsByTests.lean in this
  folder), from ten Bools on the group's plan and three on the shapes. None of the thirteen is the
  member's own run.
* Members 14 l + 5 to 14 l + 8: one Bool on the run.
* Member 14 l + 9, the batching: one Bool on a light step (layersBatchingLight, LayersLinkCells.lean
  in this folder). Where the light step returns, the table's cell returns the same, if the component
  own is the shape of what a hearing returned; that condition is drawn from the two pieces before.
* Members 14 l + 10 to 14 l + 14: one Bool on the run, to a value that is written whole.
The four inner values are written without the layers' parts (LayersPartsAside.lean in this folder).
Each later start carries these parts as a term: the parts of what the piece before returned.

Main names.
* layersParts: the layers' parts as a member of SetAside (Johnson/AtFull/Shape/JoinMany.lean).
* run_of_given: a piece that is shown by a proposition at a record instead of a closed Bool.
* LayersBorders: the six written values.
* startOwnRounds, startReads, startBatching, startAfterBatching: the four inner starts, as functions
  of the record.
* lineMembersOneToThree to lineMembersTenToFourteen, PlanLines: the seventeen Bools.

Limits. That any of the Bools is true is not shown here. B.beforeFirst is a free letter: nothing
says that a run reaches it. RunsAll holds emptily where publicOfO returns nothing (JoinAll.lean);
the layout file's size hsz, under which it returns a record, is shown in a side library alone. The
run is the one over shapeL (LWn X₀), the table's second text at written letters and numerals; LWn X₀
is no test on X₀. A Bool on a later piece alone can be true although the piece just before it
returned an error: the parts in its start are then the empty ones. The carried parts can be costly:
startReads holds, as a term, the run of the table's own cell at member 14 l + 4, with the hearing in
it, and startAfterBatching the run of the table's own cell at member 14 l + 9, not the light step's;
whoever evaluates a Bool that opens such a part must bring that run to its return. Whether a Bool
opens one is not said here. At VerifierAndGoals.storedPublicFiles alone (written copies of public files; synthetic
weights), with publicOfO taken at OnBytes.secondHashFunction, the format's second hash function
(OnBytes/Hash/SecondHashFunction.lean). Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.OwnRoundsByTests
import Johnson.AtFull.Shape.Lines.Layers.LayersLinkCells
import Johnson.AtFull.Shape.JoinMany

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Layers
open OnBytes OnBytes.Model
open Johnson.AtFull.Shape Johnson.AtFull.Shape.LayersPartsAside
open VerifiableInference.PlanWritten (publicOfO)
open VerifiableInference.Desc.First.Shape

/-- The layers' parts (LayersPartsAside.lean) as what is set aside at a written value. -/
def layersParts : SetAside where
  P := LayersPartsData
  less := lessLayersParts
  put := shapeWithLayersParts
  part := layersPartsOf
  no := noLayersParts
  eta := fun _ _ h => shape_eq_lessParts_withParts h

/-- Where lessB accepts, the run returned some x, and x less the parts is c. -/
theorem lessB_returns {A : SetAside} {r : Except String ShA} {c : ShA}
    (h : A.lessB r c = true) : ∃ x, r = .ok x ∧ A.less x = c := by
  cases r with
  | error e => cases h
  | ok x => exact ⟨x, rfl, @of_decide_eq_true _ (ByLists.decShAL _ _) h⟩

/-- One member's run is its cell's step. -/
theorem runFrom_one (L : TabLetters) (m : Nat) (x : ShA) :
    (shapeL L).runFrom m 1 x = (TabL.cells L m).1 x := rfl

section
variable (hint : Nat → List (Nat × Nat))

/-- **A piece shown by a proposition at a record**: where the stretch returns some x that is c but
for the parts, it returns the start that JoinMany.lean lays after such a stretch. -/
theorem run_of_given {X₀ : Verify.Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) (k : Nat) (A : SetAside) (c : ShA) (m : Nat) (S : Verify.Public → ShA)
    (h : ∃ x, (shapeL (LWn X₀)).runFrom m k (S X₀) = .ok x ∧ A.less x = c) :
    (shapeL (LWn X₀)).runFrom m k (S X₀) = .ok ((RunPiece.run k A c).next hint m S X₀) := by
  obtain ⟨x, hx, hl⟩ := h
  have hx' := hx
  rw [runH_eq hint hX] at hx'
  rw [hx]
  show Except.ok x = .ok (A.put c (A.partE (runH hint X₀ m k (S X₀))))
  rw [hx']
  exact congrArg Except.ok (A.eta x c hl)

/-- Six written values for a layers' link: candidates for the shapes before and after its pieces.
The two outer ones are written whole, the four inner ones without the layers' parts. -/
structure LayersBorders where
  /-- before member 14 l + 1, whole -/
  beforeFirst : ShA
  /-- before member 14 l + 4, the layers' own rounds -/
  beforeOwnRounds : ShA
  /-- before member 14 l + 5, the reads -/
  beforeReads : ShA
  /-- before member 14 l + 9, the batching -/
  beforeBatching : ShA
  /-- after member 14 l + 9 -/
  afterBatching : ShA
  /-- after member 14 l + 14, whole -/
  afterLast : ShA

variable (l : Nat) (B : LayersBorders)

/-- The start of member 14 l + 4: its written value with the parts that members 14 l + 1 to
14 l + 3 left. -/
noncomputable def startOwnRounds : Verify.Public → ShA :=
  (RunPiece.run 3 layersParts B.beforeOwnRounds).next hint (14 * l + 1) fun _ => B.beforeFirst

/-- The start of member 14 l + 5: its written value with the parts that member 14 l + 4 left. -/
noncomputable def startReads : Verify.Public → ShA :=
  (RunPiece.run 1 layersParts B.beforeReads).next hint (14 * l + 4) (startOwnRounds hint l B)

/-- The start of member 14 l + 9: its written value with the parts that members 14 l + 5 to
14 l + 8 left. -/
noncomputable def startBatching : Verify.Public → ShA :=
  (RunPiece.run 4 layersParts B.beforeBatching).next hint (14 * l + 5) (startReads hint l B)

/-- The start of member 14 l + 10: its written value with the parts that member 14 l + 9 left. -/
noncomputable def startAfterBatching : Verify.Public → ShA :=
  (RunPiece.run 1 layersParts B.afterBatching).next hint (14 * l + 9) (startBatching hint l B)

/-! ## The seventeen Bools -/

/-- Members 14 l + 1 to 14 l + 3 return the written value but for the layers' parts. -/
noncomputable def lineMembersOneToThree : Bool :=
  atXLC fun X => layersParts.lessB (runH hint X (14 * l + 1) 3 B.beforeFirst) B.beforeOwnRounds

/-- The three guards of member 14 l + 4 that read the shape accept its start. -/
noncomputable def lineOwnRoundsGuards : Bool :=
  atXLC fun X => ownRoundsGuardsTest (l / 2) X (startOwnRounds hint l B X)

/-- The list of what is left of each weight claim, made from the plan, agrees with the list that the
written value after member 14 l + 4 holds. -/
def lineMergeRecords : Bool := atXLC fun X => mergeRecordsBorderTest (l / 2) X B.beforeReads

/-- The closed form of the shape after member 14 l + 4 is the written value but for the layers'
parts. The closed form takes the list of what is left of each weight claim from the written value
itself: for that list lineMergeRecords alone speaks. -/
noncomputable def lineAfterOwnRounds : Bool :=
  atXLC fun X => afterOwnRoundsTest (l / 2) X (startOwnRounds hint l B X) B.beforeReads

/-- Members 14 l + 5 to 14 l + 8 return the written value but for the layers' parts. -/
noncomputable def lineMembersFiveToEight : Bool :=
  atXLC fun X =>
    layersParts.lessB (runH hint X (14 * l + 5) 4 (startReads hint l B X)) B.beforeBatching

/-- The light step for member 14 l + 9 returns the written value but for the layers' parts. -/
noncomputable def lineBatching : Bool :=
  atXLC fun X => layersParts.lessB (layersBatchingLight (LWn X) l (startBatching hint l B X))
      B.afterBatching

/-- Members 14 l + 10 to 14 l + 14 return the written value, all components compared. -/
noncomputable def lineMembersTenToFourteen : Bool :=
  atXLC fun X => wholeB (runH hint X (14 * l + 10) 5 (startAfterBatching hint l B X)) B.afterLast

end

/-- The ten Bools on the plan of group g are true. -/
structure PlanLines (g : Nat) : Prop where
  covers : atXLC (planCovers g) = true
  numbers : atXLC (planNumbers g) = true
  points : atXLC (planPoints g) = true
  small : atXLC (planSmall g) = true
  panels : atXLC (planPanels g) = true
  claimsCount : atXLC (planClaimsCount g) = true
  claimsFirstHalf : atXLC (planClaimsFirstHalf g) = true
  claimsSecondHalf : atXLC (planClaimsSecondHalf g) = true
  claimEmbedding : atXLC (planClaimEmbedding g) = true
  join : atXLC (planJoin g) = true

/-- **A layers' link runs from one written value to another**: if the seventeen Bools are true, then
at every record that publicOfO returns at the stored full-size public files, from B.beforeFirst the
members 14 l + 1 to 14 l + 14 of the run on shapes return B.afterLast. -/
theorem layersLink_runs (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) (hint : Nat → List (Nat × Nat))
    (l : Nat) (hl : l < 24) (he : l % 2 = 0) (B : LayersBorders) (hP : PlanLines (l / 2))
    (h1 : lineMembersOneToThree hint l B = true) (h2 : lineOwnRoundsGuards hint l B = true)
    (h3 : lineMergeRecords l B = true) (h4 : lineAfterOwnRounds hint l B = true)
    (h5 : lineMembersFiveToEight hint l B = true) (h6 : lineBatching hint l B = true)
    (h7 : lineMembersTenToFourteen hint l B = true) :
    RunsAll (14 * l + 1) 14 B.beforeFirst B.afterLast := fun X₀ hX => by
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
  -- members 14 l + 10 … + 14
  have e5 : (shapeL (LWn X₀)).runFrom (14 * l + 10) 5 (startAfterBatching hint l B X₀) =
      .ok B.afterLast :=
    (runH_eq hint hX _ _ _).trans (wholeB_ok (atXLC_all hsz h7 hX))
  exact runFrom_chain _ (runFrom_chain _ (runFrom_chain _ (runFrom_chain _ e1 e2) e3) e4) e5

end Johnson.AtFull.Shape.Layers

#print axioms Johnson.AtFull.Shape.Layers.lessB_returns
#print axioms Johnson.AtFull.Shape.Layers.runFrom_one
#print axioms Johnson.AtFull.Shape.Layers.run_of_given
#print axioms Johnson.AtFull.Shape.Layers.layersLink_runs
#print axioms Johnson.AtFull.Shape.Layers.layersParts
