-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/JoinRecords.lean: pieces of the run on shapes whose two borders may
depend on the public record, and their join; and laws that turn a closed line for Lean's kernel
into such a piece, whether the line stands under `atXLC` or under `atXHC`
(Johnson/AtFull/Shape/AtXCounts.lean). General laws; nothing is evaluated here.

Why. The joins of Johnson/AtFull/Shape/JoinAll.lean and JoinMany.lean take lines under `atXLC`
alone. Under `atXLC` the head's layout is the unevaluated run of the function that makes it, tests
on the calls' tables included (`xLazy`, AtX.lean); under `atXHC` it is made without these tests. So
a line on a member that reads that layout, such as the head's lookup on the calls, can be stated
under `atXHC`. Here a line of either kind serves. What a line costs under either is not said here.

Main names.
  `RunsBetween m n start finish`   at every record X₀ that publicOfO returns at the stored full-size
      files: from `start X₀` the n members from m on return `finish X₀`, over `shapeL (LWn X₀)`, the
      text of the table over a record of letters (TabLetters.lean). At two constant borders it is
      `RunsAll`: `RunsBetween.runsAll`, `RunsAll.runsBetween`.
  `RunsBetween.chain`   two pieces, one after the other, are one.
  `atXHC_all`   under the layout file's size, a closed fact under `atXHC` holds at every record that
      publicOfO returns at the stored full-size files (`atXLC_all`, JoinMany.lean, says the same of
      `atXLC`).
  `borderWithPairOfRun hint m k start border`   the written border with the components look and
      lookHeard that the piece's own run over the cells of TailLight.lean left, as a term in the
      record.
  `runsBetween_of_lessPair`, `runsBetween_of_whole`   a piece from `lessB` or `wholeB` over
      `runOverLightTail` at every record.
  `borderWithPairOfStep`, `runsBetween_of_step`   the same for one member that is shown through a
      step of another text for which one direction is proved: where the step returns, the table's
      cell returns the same.

Limits. `RunsBetween` holds emptily if publicOfO returns nothing at these files, as `RunsAll` does.
The two components that are carried are a match on a run's outcome: a later piece that reads them
makes whoever evaluates its line evaluate the run before it until that run returns. A fact on a
later piece alone can be true although the piece before it returned an error: `pairE` then answers
(none, none). `runsBetween_of_step` says nothing where the step returns an error. Nothing holds
m + n at or below 358: from 358 on the table answers every number with the seal's cell (Table.lean),
so "the n members from m on" speaks of members only below 358. At VerifierAndGoals.storedPublicFiles and OnBytes.secondHashFunction,
the format's second hash function, alone. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.JoinMany
import Johnson.AtFull.Shape.Lines.TailLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open PairAside
open VerifiableInference.PlanWritten (publicOfO)

/-- From `start X₀` the n members from m on return `finish X₀`, over the text of the table over a
record of letters, at every record X₀ that publicOfO returns at the stored full-size files. It does
not say that a record is there. -/
def RunsBetween (m n : Nat) (start finish : Verify.Public → ShA) : Prop :=
  ∀ X₀ : Verify.Public,
    publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ →
    (shapeL (LWn X₀)).runFrom m n (start X₀) = .ok (finish X₀)

/-- At two constant borders it is RunsAll. -/
theorem RunsBetween.runsAll {m n : Nat} {a b : ShA}
    (h : RunsBetween m n (fun _ => a) fun _ => b) : RunsAll m n a b := h

/-- The way back. -/
theorem RunsAll.runsBetween {m n : Nat} {a b : ShA} (h : RunsAll m n a b) :
    RunsBetween m n (fun _ => a) fun _ => b := h

/-- **Two pieces, one after the other, are one.** -/
theorem RunsBetween.chain {m n₁ n₂ : Nat} {a b c : Verify.Public → ShA}
    (h1 : RunsBetween m n₁ a b) (h2 : RunsBetween (m + n₁) n₂ b c) :
    RunsBetween m (n₁ + n₂) a c :=
  fun X₀ hX => runFrom_chain _ (h1 X₀ hX) (h2 X₀ hX)

/-- Under the layout file's size, a closed fact under atXHC holds at every record that publicOfO
returns at the stored full-size files. -/
theorem atXHC_all (hsz : VerifierAndGoals.storedPublicFiles.lay.size = 224975) {t : Verify.Public → Bool}
    (h : atXHC t = true) {X₀ : Verify.Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) : t X₀ = true := by
  obtain ⟨X₁, h1, e⟩ := atXHC_zFull hsz h
  obtain rfl : X₁ = X₀ := Except.ok.inj (h1.symm.trans hX)
  exact e

section
variable (hint : Nat → List (Nat × Nat))

/-- At a record that publicOfO returns at the stored full-size files, the run over the text of the
table over a record of letters is the run over the cells of TailLight.lean. -/
theorem runFrom_eq_lightTail {X₀ : Verify.Public}
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) =
      .ok X₀) (m k : Nat) (a : ShA) :
    (shapeL (LWn X₀)).runFrom m k a = runOverLightTail hint X₀ m k a :=
  (runH_eq hint hX m k a).trans (runOverLightTail_eq hint X₀ m k a).symm

/-- The written border with the look and lookHeard that the piece's own run left, as a term in the
record. -/
noncomputable def borderWithPairOfRun (m k : Nat) (start : Verify.Public → ShA) (border : ShA)
    (X : Verify.Public) : ShA :=
  withLk border (pairE (runOverLightTail hint X m k (start X)))

/-- **A piece to a border that is written with look and lookHeard set to none.** -/
theorem runsBetween_of_lessPair (m k : Nat) (start : Verify.Public → ShA) (border : ShA)
    (h : ∀ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ →
      lessB (runOverLightTail hint X₀ m k (start X₀)) border = true) :
    RunsBetween m k start (borderWithPairOfRun hint m k start border) :=
  fun X₀ hX => (runFrom_eq_lightTail hint hX m k (start X₀)).trans (lessB_ok (h X₀ hX))

/-- **A piece to a border that is written in all components.** -/
theorem runsBetween_of_whole (m k : Nat) (start : Verify.Public → ShA) (border : ShA)
    (h : ∀ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ →
      wholeB (runOverLightTail hint X₀ m k (start X₀)) border = true) :
    RunsBetween m k start fun _ => border :=
  fun X₀ hX => (runFrom_eq_lightTail hint hX m k (start X₀)).trans (wholeB_ok (h X₀ hX))

end

/-- The written border with the look and lookHeard that a step left, as a term in the record. -/
def borderWithPairOfStep (step : Verify.Public → ShA → Except String ShA)
    (start : Verify.Public → ShA) (border : ShA) (X : Verify.Public) : ShA :=
  withLk border (pairE (step X (start X)))

/-- **One member, shown through a step that implies the table's cell in one direction**, to a border
that is written with look and lookHeard set to none. Where the step returns an error nothing is said
of the cell; the premise h says that it returns. -/
theorem runsBetween_of_step (m : Nat) (step : Verify.Public → ShA → Except String ShA)
    (under : ∀ (X : Verify.Public) (x y : ShA), step X x = .ok y →
      (TabL.cells (LWn X) m).1 x = .ok y)
    (start : Verify.Public → ShA) (border : ShA)
    (h : ∀ X₀ : Verify.Public,
      publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀ →
      lessB (step X₀ (start X₀)) border = true) :
    RunsBetween m 1 start (borderWithPairOfStep step start border) :=
  fun X₀ hX => under X₀ _ _ (lessB_ok (h X₀ hX))

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.RunsBetween
#print axioms Johnson.AtFull.Shape.RunsBetween.runsAll
#print axioms Johnson.AtFull.Shape.RunsAll.runsBetween
#print axioms Johnson.AtFull.Shape.RunsBetween.chain
#print axioms Johnson.AtFull.Shape.atXHC_all
#print axioms Johnson.AtFull.Shape.runFrom_eq_lightTail
#print axioms Johnson.AtFull.Shape.borderWithPairOfRun
#print axioms Johnson.AtFull.Shape.runsBetween_of_lessPair
#print axioms Johnson.AtFull.Shape.runsBetween_of_whole
#print axioms Johnson.AtFull.Shape.borderWithPairOfStep
#print axioms Johnson.AtFull.Shape.runsBetween_of_step
