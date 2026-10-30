-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/BatchAtt.lean: THE BATCHING MEMBER OF AN ATTENTION LINK GOES ALIKE UNDER
RelX AT TWO RECORDS THAT MEET SameRead.

  planes_alike   the row "planes".
  rowsAtt_alike  the ten rows, under the padding key's test at both plans.
  att_cell       what the cell is at an odd link.
  **batch_att_rel**   the place 8 of an odd link, in Join.lean's form.

Limits. Nothing is evaluated. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.BatchRel
import Johnson.AtFull.Shape.Scope.AttRowsB
import Johnson.AtFull.Shape.Scope.AttSorts
import Johnson.AtFull.Shape.Scope.LayerCells
import Johnson.AtFull.Shape.TabLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K9 (SegSort Where testsWhere)
open VerifiableInference.Desc.K9.Shape
open VerifiableInference.Desc.First.Look (placeAt lookAt)
open ProofFile.Honest.K3.Shape (planesShG planesShO planesAtSh)
open H2K5.Honest (k5ReadersG readersSh tabsGC inBlank)
open IM (subAt)

variable {X X₀ : Verify.Public}

theorem readers_same {A B : Attention.Plan} (e : stripPlan A = stripPlan B) {c c' : ChainSh}
    (hc : RC c c') : k5ReadersG A c = k5ReadersG B c' := by
  have eT := tabsGC_same e hc
  have eI := inBlank_same e hc
  have t : ∀ o : Option (VerifiableInference.Desc.First.Att.P.Runs.In × Nat),
      o.map readersSh = (o.map flatX).map readersSh := by
    intro o
    cases o <;> rfl
  unfold k5ReadersG
  rw [eT, t, t (inBlank B c'), eI]

theorem planesAtSh_strip (lm : Nat) (L : LedSh) (h : HeardAll) (q) :
    planesAtSh lm L (stripH h) q = planesAtSh lm L h q := rfl

theorem planes_alike {A B : Attention.Plan} (e : stripPlan A = stripPlan B) (lm : Nat) :
    RowAlike (planesShG lm (k5ReadersG A)) (planesShG lm (k5ReadersG B)) := by
  intro n c c' h
  have hq := readers_same e h
  have hh := h.lookHeard
  unfold planesShG planesShO
  rw [h.led, hq]
  cases c'.led with
  | none => exact alike_err _ _
  | some L =>
    cases e1 : c.lookHeard with
    | none =>
      rw [e1] at hh
      cases e2 : c'.lookHeard with
      | none => exact alike_err _ _
      | some _ =>
        rw [e2] at hh
        cases hh
    | some g =>
      rw [e1] at hh
      cases e2 : c'.lookHeard with
      | none =>
        rw [e2] at hh
        cases hh
      | some g' =>
        rw [e2] at hh
        have eg : stripH g = stripH g' := Option.some.inj hh
        have ep : planesAtSh lm L g = planesAtSh lm L g' := by
          funext q
          rw [← planesAtSh_strip lm L g, eg, planesAtSh_strip]
        simp only [Option.bind_some]
        rw [ep]
        cases k5ReadersG B c' with
        | none => exact alike_err _ _
        | some q =>
          simp only [Option.bind_some]
          cases planesAtSh lm L g' q with
          | none => exact alike_err _ _
          | some x => exact alike_ok ⟨rfl, h.setLed _⟩

theorem rowsAtt_alike {A B : Attention.Plan} (e : stripPlan A = stripPlan B) (lm : Nat)
    (hA : VerifiableInference.Desc.First.Att.P.padKeyOk
      (VerifiableInference.Desc.First.Att.P.parCOf A).geo = true)
    (hB : VerifiableInference.Desc.First.Att.P.padKeyOk
      (VerifiableInference.Desc.First.Att.P.parCOf B).geo = true) :
    RowsAlike (rowsAtt A lm) (rowsAtt B lm) :=
  .cons ⟨rfl, objects_alike false⟩ <| .cons ⟨rfl, guests_alike⟩ <|
  .cons ⟨rfl, fun n _ _ h => first_row e n h⟩ <|
  .cons ⟨rfl, fun n _ _ h => keys_row e hA hB n h⟩ <|
  .cons ⟨rfl, fun n _ _ h => join_row e hA hB n h⟩ <|
  .cons ⟨rfl, fun n _ _ h => second_row e n h⟩ <| .cons ⟨rfl, planes_alike e lm⟩ <|
  .cons ⟨rfl, objects_alike true⟩ <| .cons ⟨rfl, guests_alike⟩ <| .cons ⟨rfl, eq_alike⟩ .nil

theorem placeAt_att {X : Verify.Public} (h4 : X.p4 = true) {l : Nat} (ho : l % 2 = 1)
    {a : Attention.Plan} (hA : X.A[l / 2]? = some a) :
    ∃ q, placeAt X l false = some q ∧ q.lm = a.S.cf.lmb := by
  have hb : ¬ (l == 2 * X.NGr) = true := by
    intro e
    have : l = 2 * X.NGr := by simpa using e
    omega
  have hm : ¬ (l % 2 == 0) = true := by
    intro e
    have : l % 2 = 0 := by simpa using e
    omega
  unfold placeAt lookAt
  simp only [h4, if_true, if_neg hb, if_neg hm, hA]
  exact ⟨_, rfl, rfl⟩

theorem tests_att {X : Verify.Public} (h4 : X.p4 = true) {l : Nat} (ho : l % 2 = 1)
    {a : Attention.Plan} (hA : X.A[l / 2]? = some a) :
    ∃ w, testsWhere X l 0 = some w ∧ w.1 = .attention := by
  have hb : ¬ (l == 2 * X.NGr) = true := by
    intro e
    have : l = 2 * X.NGr := by simpa using e
    omega
  have hm : ¬ (l % 2 == 0) = true := by
    intro e
    have : l % 2 = 0 := by simpa using e
    omega
  unfold testsWhere
  simp only [h4, if_true, if_neg hb, if_neg hm, hA]
  exact ⟨_, rfl, rfl⟩

/-- **The cell at an odd link, where the plan stands.** -/
theorem att_cell {X : Verify.Public} (h4 : X.p4 = true) {l : Nat} (ho : l % 2 = 1)
    {a : Attention.Plan} (hA : X.A[l / 2]? = some a) :
    (TabL.batch (LW X) l).1 = cellG (k9L l) .attention (rowsAtt a a.S.cf.lmb)
      (VerifiableInference.Desc.First.orderOf (subAt l)) := by
  obtain ⟨q, hq, eq⟩ := placeAt_att h4 ho hA
  obtain ⟨w, hw, ew⟩ := tests_att h4 ho hA
  have h24 : (l == 24) = false := by
    have : l ≠ 24 := by omega
    simpa using this
  have hm : ¬ (l % 2 == 0) = true := by
    intro e
    have : l % 2 = 0 := by simpa using e
    omega
  have e1 : testsWhere (LW X).XZ l 0 = some w := hw
  have e2 : (LW X).XG.A[l / 2]? = some a := hA
  have e3 : placeAt (LW X).XG l false = some q := hq
  have e4 : (LW X).k9 l = some (k9L l) := rfl
  unfold TabL.batch
  rw [e4, e1]
  simp only [h24, Bool.false_eq_true, if_false, if_neg hm]
  rw [e2, e3]
  show cellG (k9L l) w.1 (rowsAtt a q.lm) _ = _
  rw [ew, eq]

/-- Where no plan stands, the cell refuses. -/
theorem att_none {X : Verify.Public} (h4 : X.p4 = true) {l : Nat} (ho : l % 2 = 1)
    (hA : X.A[l / 2]? = none) (x : ShA) : ((TabL.batch (LW X) l).1 x).toOption = none := by
  have hb : ¬ (l == 2 * X.NGr) = true := by
    intro e
    have : l = 2 * X.NGr := by simpa using e
    omega
  have hm : ¬ (l % 2 == 0) = true := by
    intro e
    have : l % 2 = 0 := by simpa using e
    omega
  have e1 : testsWhere (LW X).XZ l 0 = none := by
    show testsWhere X l 0 = none
    unfold testsWhere
    simp only [h4, if_true, if_neg hb, if_neg hm, hA]
    rfl
  unfold TabL.batch
  rw [e1]
  cases (LW X).k9 l <;> rfl

/-- **THE PLACE 8 OF AN ODD LINK**, under the padding key's test at both records' plans. -/
theorem batch_att_pad (S : SameRead X X₀) (h4 : X₀.p4 = true)
    (hP : ∀ (g : Nat) (a : Attention.Plan), X.A[g]? = some a →
      VerifiableInference.Desc.First.Att.P.padKeyOk
        (VerifiableInference.Desc.First.Att.P.parCOf a).geo = true)
    (hP₀ : ∀ (g : Nat) (a : Attention.Plan), X₀.A[g]? = some a →
      VerifiableInference.Desc.First.Att.P.padKeyOk
        (VerifiableInference.Desc.First.Att.P.parCOf a).geo = true)
    {l : Nat} (hl : l < 24) (ho : l % 2 = 1) :
    CellRel X X₀ (14 * l + 8 + 1) ((TabL.linkRow (LW X) l).at 8)
      ((TabL.linkRow (LW X₀) l).at 8) := by
  have h4' : X.p4 = true := by rw [S.toSamePlans.p4]; exact h4
  have o1 : oddAt (14 * l + 8 + 1) = true := by
    rw [oddAt_place hl (by omega)]
    simp [ho]
  have o2 : oddAt (14 * l + 8 + 1 + 1) = true := by
    rw [oddAt_inside hl (by omega), o1]
  intro a a' h
  rw [relAt_oddE o1] at h
  rw [relAt_oddE o2]
  show Alike _ ((TabL.batch (LW X) l).1 a) ((TabL.batch (LW X₀) l).1 a')
  rcases plans_alike S (l / 2) with ⟨h1, h2⟩ | ⟨p, q, h1, h2, e⟩
  · exact Or.inr ⟨att_none h4' ho h1 a, att_none h4 ho h2 a'⟩
  · rw [att_cell h4' ho h1, att_cell h4 ho h2]
    have elm : p.S.cf.lmb = q.S.cf.lmb := by
      have e1 := congrArg (fun r : Attention.Plan => r.S.cf.lmb) e
      exact e1
    rw [elm]
    exact cellG_rel _ _ (rowsAtt_alike e _ (hP _ _ h1) (hP₀ _ _ h2)) _ h

/-- At the stored files' record the proof covers attention. -/
theorem p4_of_return
    (h₀ : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL
      (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀) : X₀.p4 = true := by
  have e := step_of_return h₀
  have hN : X₀.NGr = 12 := (HonestTraceRun.SetUp.base_facts h₀).2.1
  cases hp : X₀.p4 with
  | true => rfl
  | false =>
    rw [hp, hN] at e
    simp at e

/-- **THE PLACE 8 OF AN ODD LINK**, at two returns of publicOfO. -/
theorem batch_att_rel (S : SameRead X X₀) {pol KL : ByteArray} {lay : Option ByteArray}
    (hX : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction pol KL lay = .ok X)
    (h₀ : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL
      (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀) {l : Nat} (hl : l < 24) (ho : l % 2 = 1) :
    CellRel X X₀ (14 * l + 8 + 1) ((TabL.linkRow (LW X) l).at 8)
      ((TabL.linkRow (LW X₀) l).at 8) :=
  batch_att_pad S (p4_of_return h₀) (hpad_of_public hX) (hpad_of_public h₀) hl ho

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.planes_alike
#print axioms Johnson.AtFull.Shape.Scope.rowsAtt_alike
#print axioms Johnson.AtFull.Shape.Scope.batch_att_pad
#print axioms Johnson.AtFull.Shape.Scope.p4_of_return
#print axioms Johnson.AtFull.Shape.Scope.batch_att_rel
