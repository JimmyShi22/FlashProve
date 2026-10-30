-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/AnswersAtScope.lean: the stored table's index has answers, index.answers = 1, at the
release's
lines: it is a function of two lines of the parameter file's first 32 alone ("record", "answers"),
and
these are pinned at every three public files in the scope of the goals.

The kind K14's text asks the equation on the record's answers ((rec_gamma)) over the record's seeds:
at index.answers = 0 it asks nothing there. Here: that case is
not
reached in scope.
  answers_of_lines: where deriveTable (settingOf l) l returns T: (indexShapeOf (settingOf l)
      T).answers
      is l.answers where l.record is not 0, else 0: nothing else of the lines enters
  answers_record: at the release's lines (recordLines): 1
  lines_at_scope: Johnson/Goal/Scope/ScopeLines.lean: inScope_reads_at: at every Z in
      scope
      the reader of the first 32 lines returns recordLines
  answers_at_scope: so, at every Z in scope, for every l that the reader returns and every T that
      deriveTable returns at it: the index's answers are 1
  answers_key, answers_key_at_scope: the key file's shape: by Lean's kernel at the written value; at
      every Z in scope with a planner that returns (key_eq_at_scope)
  index_at_scope: THE PROOF FILE's OWN INDEX, at every Z in scope with a planner that returns, is
      the
      key file's written one (planned_parts, configure_plans, sized_index,
      key_eq_at_scope)
  answers_proof_at_scope, answers_seat_at_scope: so its answers are 1: at the sized proof's batch's
      shape, and at p14Of p.chains bp, the parameters of the shared chain's seat
  answers_real: the proof file's typed shape (realSized): by Lean's kernel

What is not claimed. That verify()'s own road makes its plan by this planner on Z's three files.
What the kind's text does where there are no
answers. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Goal.Numbers.K14CondAt
import Johnson.Goal.Scope.ScopeLines

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Params.Prices Johnson.G
open VerifiableInference.Desc.K1 (realSized)
open Lk6.AtPlan (keyFull key_eq_at_scope)

/-- **The index's answers are a function of two lines alone.** -/
theorem answers_of_lines (l : Lines) (T : TableSize) (h : deriveTable (settingOf l) l = some T) :
    (indexShapeOf (settingOf l) T).answers = l.answers := rfl

/-- At the release's lines. -/
theorem answers_record (T : TableSize) (h : deriveTable recordSet recordLines = some T) :
    (indexShapeOf recordSet T).answers = 1 := answers_of_lines recordLines T h

/-- **At every three public files in scope.** -/
theorem answers_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) (l : Lines)
    (b : ByteArray) (hl : readLines Z.pol = .ok (l, b)) (T : TableSize)
    (h : deriveTable (settingOf l) l = some T) : (indexShapeOf (settingOf l) T).answers = 1 := by
  obtain ⟨b', -, hr⟩ := Johnson.G.ScopeLines.inScope_reads_at hZ
  rw [hr] at hl
  obtain rfl : recordLines = l := congrArg Prod.fst (Except.ok.inj hl)
  exact answers_record T h

/-- The key file's shape. -/
theorem answers_key : keyFull.once.shape.fold.index.answers = 1 := by decide +kernel

theorem answers_key_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) :
    p.chains.made.sized.key.once.shape.fold.index.answers = 1 := by
  rw [key_eq_at_scope hZ hp]
  exact answers_key

/-- **The proof file's own index, in scope, is the key file's written one**: the planner puts one
shape of the tables into the shapes that it makes (OnBytes/Model/VerifyShape.lean: sized_index), on
the lines that it reads off the parameter file (OnBytes/Model/Fit/PlannedParts.lean: planned_parts).
-/
theorem index_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) :
    p.chains.made.sized.proof.batch.shape.fold.index = keyFull.once.shape.fold.index := by
  obtain ⟨links, shapes, _, _, _, _, _, _, _, _, _, _, hc, _, _, _, _⟩ :=
    Model.Verify.planned_parts hp
  obtain ⟨i1, i2⟩ := Params.sized_index (Params.configure_plans hc).1
  rw [i2, ← i1, key_eq_at_scope hZ hp]

/-- **In scope the proof file's index has answers.** -/
theorem answers_proof_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p) :
    p.chains.made.sized.proof.batch.shape.fold.index.answers = 1 := by
  rw [index_at_scope hZ hp]
  exact answers_key

/-- **At the parameters that the shared chain's maker takes off the planner's chains.** -/
theorem answers_seat_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {p : Model.Verify.Planned} (hp : Model.Verify.planned Z.pol Z.KL (some Z.lay) = .ok p)
    (bp : List (Nat × Nat)) : (p14Of p.chains bp).S.fold.index.answers = 1 :=
  answers_proof_at_scope hZ hp

/-- The proof file's typed shape. -/
theorem answers_real : ∃ x : LinSized, realSized = some (x, codesFull2) ∧
    x.shape.fold.index.answers = 1 := by
  obtain ⟨x, a1, -, -⟩ := k14_real
  have h : (realSized.any fun p => decide (p.1.shape.fold.index.answers = 1)) = true := by
    decide +kernel
  rw [a1, Option.any_some] at h
  exact ⟨x, a1, of_decide_eq_true h⟩

end Desc.K14.Law

#print axioms Desc.K14.Law.answers_of_lines
#print axioms Desc.K14.Law.answers_record
#print axioms Desc.K14.Law.answers_at_scope
#print axioms Desc.K14.Law.answers_key
#print axioms Desc.K14.Law.answers_key_at_scope
#print axioms Desc.K14.Law.index_at_scope
#print axioms Desc.K14.Law.answers_proof_at_scope
#print axioms Desc.K14.Law.answers_seat_at_scope
#print axioms Desc.K14.Law.answers_real
