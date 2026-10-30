-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Head/BatchHeadFrame.lean: the output head's batching (member 347 of the
first chain, the batching of the head's row) over light rows. The frame: general in the runs that
take the places of "norm", "policy", "logits" and "join". No shape is evaluated.

Why. HeadLight.lean fills the frame with the runs of HeadCover.lean. What holds for any such runs
stands here. "Light" is as in ClaimCovers.lean: claims that hand on a few entries in the place of
many.

  headPlanesSecondText    the head's "planes" run with addAllSh_L
                          (Johnson/AtFull/Shape/AddAllL.lean) laid in: an equal text, which the
                          closing rfl fills.
  headLightRowsFrame      the eleven rows' runs: equationsRunCovered at "K8.equations", the given
                          runs at "norm", "policy", "logits" and "join", headPlanesSecondText at
                          "planes", else the table's (rowsHead,
                          Johnson/AtFull/Shape/BatchCells.lean). iU3: the reads' array.
  **headLightRowsFrame_standUnder**   from the two laws on the given runs, the light rows stand for
                          the table's.
  headBatchingLightFrame, **headBatchingLightFrame_standsUnder**   the light step of the member:
                          the light rows, and batchGSL.1 (Johnson/AtFull/Shape/TabLight.lean) in the
                          place of batchGS. Where the rows stand for the table's and it returns, the
                          table's cell at the head's batching (TabL.batch,
                          Johnson/AtFull/Shape/TabLetters.lean) returns the same. No premise on the
                          shape.
  headBatchingLightFrame_atCell   the same at TabL.cells, member 347.

Limits. One way: where the light step refuses nothing is said. The given runs are free here: what
stands in their place is said in HeadLight.lean. What any of this costs Lean's kernel is not
measured here. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Layers.ClaimCovers
import Johnson.AtFull.Shape.Lines.Layers.ReadsEquationsCover
import Johnson.AtFull.Shape.TabLight
import Johnson.AtFull.Shape.TabLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.K8.Honest (equationsRunCovered equationsRunCovered_standsUnder)
open VerifiableInference.Desc.K9 (SegSort testsWhere)
open VerifiableInference.Desc.K9.Shape
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workAtW)
open IM (subAt)

/-- The head's "planes" with addAllSh_L laid in. The first field is made by Lean; the second is the
tie. -/
def headPlanesSecondText :
    { f : Nat → Nat → Nat → ChainSh → Except String (List ClaimSh × ChainSh) //
    ∀ lm iU3, ProofFile.Honest.K3.Shape.planesShG lm (ProofFile.Honest.K3.Shape.headReadersG iU3) =
        f lm iU3 } :=
  ⟨_, fun lm iU3 => by
    delta ProofFile.Honest.K3.Shape.planesShG ProofFile.Honest.K3.Shape.planesShO
      ProofFile.Honest.K3.Shape.planesAtSh
    simp -zeta only [Johnson.AtFull.Shape.AddAllL.addAllSh_L]
    rfl⟩

/-- The runs of the eleven rows, with given runs at the four that hand on forms or key vectors. -/
def headLightRowsFrame (W : Verify.Public) (iU3 lm : Nat)
    (three : String → Nat → ChainSh → Except String (List ClaimSh × ChainSh))
    (join : Nat → ChainSh → Except String (List ClaimSh × ChainSh)) (o : Nat × String) :
    Nat → ChainSh → Except String (List ClaimSh × ChainSh) :=
  if o == (5, "K8.equations") then equationsRunCovered
  else if o == (3, "norm") then three "norm"
  else if o == (3, "policy") then three "policy"
  else if o == (3, "logits") then three "logits"
  else if o == (3, "join") then join
  else if o == (2, "planes") then headPlanesSecondText.1 lm iU3
  else (tabOf (rowsHead W iU3 lm) o).g

/-- **The light rows stand for the table's**, from the laws on the two given runs. -/
theorem headLightRowsFrame_standUnder (W : Verify.Public) (iU3 lm : Nat)
    {three : String → Nat → ChainSh → Except String (List ClaimSh × ChainSh)}
    {join : Nat → ChainSh → Except String (List ClaimSh × ChainSh)}
    (hT : ∀ name n a y', three name n a = .ok y' →
      ∃ y, (rowThree W iU3 name).g n a = .ok y ∧ ClaimsStandUnder y'.1 y.1 ∧ y'.2 = y.2)
    (hJ : ∀ n a y', join n a = .ok y' →
      ∃ y, VerifiableInference.Desc.Kinds.Head.Shape.joinRunG W.hS iU3 (parOf W.hS (workAtW W)) n a
          =
        .ok y ∧ ClaimsStandUnder y'.1 y.1 ∧ y'.2 = y.2) :
    RowsStandUnder (fun _ => True) (headLightRowsFrame W iU3 lm three join)
      (fun o => (tabOf (rowsHead W iU3 lm) o).g) := by
  intro o n a y' _ h
  unfold headLightRowsFrame at h
  by_cases e1 : o = (5, "K8.equations")
  · subst e1
    rw [if_pos (by decide)] at h
    obtain ⟨y, ey, u, e2⟩ := equationsRunCovered_standsUnder h
    exact ⟨y, ey, u, e2, trivial⟩
  rw [if_neg (by simpa using e1)] at h
  by_cases e2 : o = (3, "norm")
  · subst e2
    rw [if_pos (by decide)] at h
    obtain ⟨y, ey, u, e3⟩ := hT _ n a y' h
    exact ⟨y, ey, u, e3, trivial⟩
  rw [if_neg (by simpa using e2)] at h
  by_cases e3 : o = (3, "policy")
  · subst e3
    rw [if_pos (by decide)] at h
    obtain ⟨y, ey, u, e4⟩ := hT _ n a y' h
    exact ⟨y, ey, u, e4, trivial⟩
  rw [if_neg (by simpa using e3)] at h
  by_cases e4 : o = (3, "logits")
  · subst e4
    rw [if_pos (by decide)] at h
    obtain ⟨y, ey, u, e5⟩ := hT _ n a y' h
    exact ⟨y, ey, u, e5, trivial⟩
  rw [if_neg (by simpa using e4)] at h
  by_cases e5 : o = (3, "join")
  · subst e5
    rw [if_pos (by decide)] at h
    obtain ⟨y, ey, u, e6⟩ := hJ n a y' h
    exact ⟨y, ey, u, e6, trivial⟩
  rw [if_neg (by simpa using e5)] at h
  by_cases e6 : o = (2, "planes")
  · subst e6
    rw [if_pos (by decide), ← headPlanesSecondText.2] at h
    exact ⟨y', h, ClaimsStandUnder.refl _, rfl, trivial⟩
  rw [if_neg (by simpa using e6)] at h
  exact ⟨y', h, ClaimsStandUnder.refl _, rfl, trivial⟩

/-- **The light step at the head's batching.** -/
def headBatchingLightFrame (L : TabLetters)
    (three : Nat → Nat → String → Nat → ChainSh → Except String (List ClaimSh × ChainSh))
    (join : Nat → Nat → Nat → ChainSh → Except String (List ClaimSh × ChainSh)) :
    ShA → Except String ShA :=
  match L.k9 24, testsWhere L.XZ 24 0, L.XG.H.tl.ix.U.getD 2 none,
      VerifiableInference.Desc.First.Look.placeAt L.XG 24 false with
  | some p, some w, some iU3, some q =>
    liftQ (batchGSL.1 p.rows w.1
      (headLightRowsFrame L.XG iU3 q.lm (three iU3 (L.XG.H.nU.getD 2 0)) (join iU3 (L.XG.H.nU.getD 2
          0)))
      (VerifiableInference.Desc.First.orderOf (subAt 24)))
  | _, _, _, _ => fun _ => .error "the light batching at the head: no numbers"

/-- **Where the rows stand for the table's (hR) and it returns, the table's cell returns the same**:
no premise on the shape. -/
theorem headBatchingLightFrame_standsUnder (L : TabLetters)
    {three : Nat → Nat → String → Nat → ChainSh → Except String (List ClaimSh × ChainSh)}
    {join : Nat → Nat → Nat → ChainSh → Except String (List ClaimSh × ChainSh)}
    (hR : ∀ iU3 lm n, RowsStandUnder (fun _ => True) (headLightRowsFrame L.XG iU3 lm (three iU3 n)
        (join iU3 n))
      (fun o => (tabOf (rowsHead L.XG iU3 lm) o).g))
    {x y : ShA} (h : headBatchingLightFrame L three join x = .ok y) : (TabL.batch L 24).1 x =
        .ok y := by
  unfold headBatchingLightFrame at h
  unfold TabL.batch
  cases h1 : L.k9 24 with
  | none =>
    rw [h1] at h
    exact nomatch h
  | some p =>
    cases h2 : testsWhere L.XZ 24 0 with
    | none =>
      rw [h1, h2] at h
      exact nomatch h
    | some w =>
      cases h3 : L.XG.H.tl.ix.U.getD 2 none with
      | none =>
        rw [h1, h2, h3] at h
        exact nomatch h
      | some iU3 =>
        cases h4 : VerifiableInference.Desc.First.Look.placeAt L.XG 24 false with
        | none =>
          rw [h1, h2, h3, h4] at h
          exact nomatch h
        | some q =>
          rw [h1, h2, h3, h4] at h
          have h' : liftQ (batchGSL.1 p.rows w.1 (headLightRowsFrame L.XG iU3 q.lm
              (three iU3 (L.XG.H.nU.getD 2 0)) (join iU3 (L.XG.H.nU.getD 2 0)))
              (VerifiableInference.Desc.First.orderOf (subAt 24))) x = .ok y := h
          show liftQ (batchGS p.rows w.1 (fun o => (tabOf (rowsHead L.XG iU3 q.lm) o).g)
              (VerifiableInference.Desc.First.orderOf (subAt 24))) x = .ok y
          unfold liftQ at h' ⊢
          rw [← batchGSL.2] at h'
          cases hb : batchGS p.rows w.1 (headLightRowsFrame L.XG iU3 q.lm
              (three iU3 (L.XG.H.nU.getD 2 0)) (join iU3 (L.XG.H.nU.getD 2 0)))
              (VerifiableInference.Desc.First.orderOf (subAt 24)) x.1 with
          | error e =>
            rw [hb] at h'
            exact nomatch h'
          | ok u =>
            rw [hb] at h'
            rw [batchingOnShapes_standsUnder (hR iU3 q.lm _) p.rows _ (fun _ _ _ _ =>
                trivial) trivial hb]
            exact h'

/-- The same at the table's member 347, under hR. -/
theorem headBatchingLightFrame_atCell (L : TabLetters)
    {three : Nat → Nat → String → Nat → ChainSh → Except String (List ClaimSh × ChainSh)}
    {join : Nat → Nat → Nat → ChainSh → Except String (List ClaimSh × ChainSh)}
    (hR : ∀ iU3 lm n, RowsStandUnder (fun _ => True) (headLightRowsFrame L.XG iU3 lm (three iU3 n)
        (join iU3 n))
      (fun o => (tabOf (rowsHead L.XG iU3 lm) o).g))
    {x y : ShA} (h : headBatchingLightFrame L three join x = .ok y) : (TabL.cells L 347).1 x =
        .ok y := by
  have e : TabL.cells L 347 = (TabL.headRow L).at 10 :=
    table_head _ _ _ _ 10 (by omega)
  rw [e]
  exact headBatchingLightFrame_standsUnder L hR h

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.headPlanesSecondText
#print axioms Johnson.AtFull.Shape.headLightRowsFrame
#print axioms Johnson.AtFull.Shape.headLightRowsFrame_standUnder
#print axioms Johnson.AtFull.Shape.headBatchingLightFrame
#print axioms Johnson.AtFull.Shape.headBatchingLightFrame_standsUnder
#print axioms Johnson.AtFull.Shape.headBatchingLightFrame_atCell
