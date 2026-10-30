-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/PlanWrittenHalves.lean: "in scope, either the verifier refuses everything, or
the file's data are the written data", a file at a time: the two halves of `WrittenOrRefuses`
(Johnson/Goal/Numbers/PlanWrittenAsked.lean), each with a refusal of its own, and how they join.

The two files' descriptions are laid by different hands. Whoever lays one of them can show its half
of the sentence from its half of the statement (`ProofWrittenAt`, `KeyWrittenAt`,
Johnson/Goal/Numbers/PlanWrittenMore.lean) and from `YesAsked` at its own yes and its own refusal.

Every declaration here is a tool: the makers, the yes and the refusals are letters, and
no description is named.

What is here.
  `ProofWrittenOrRefuses FP refuses`, `KeyWrittenOrRefuses FK refuses`: for every Z in scope,
    `refuses Z`, or the data of the file's description are the written data.
  `proof_written_or_refuses`, `key_written_or_refuses`: each follows from its half of
    `PlanWrittenAt` at a yes, and `YesAsked` at that yes. By cases on the yes.
  `writtenOrRefuses_of_halves`: halves at two refusals give `WrittenOrRefuses` at "one of the two
    refuses". `writtenOrRefuses_iff`: at one refusal the sentence is its two halves together.

Limits. Those of Johnson/Goal/Numbers/PlanWrittenAsked.lean: above all, a refusal is a free letter,
and with a refusal that always holds a half says nothing. That "one of the two refuses" means that
the verifier refuses is for whoever names the two refusals to show. Nothing on soundness.


-/
import Johnson.Goal.Numbers.PlanWrittenAsked
import Johnson.Goal.Numbers.PlanWrittenMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open Johnson.G VerifiableInference.Desc

variable {XiP XiK : Type}

/-- **The proof file's half of the sentence.** -/
def ProofWrittenOrRefuses (FP : VerifierAndGoals.PublicFiles → FileDescription XiP) (refuses : VerifierAndGoals.PublicFiles → Prop) : Prop :=
  ∀ Z : VerifierAndGoals.PublicFiles, VerifierAndGoals.InScope Z = true →
    refuses Z ∨ (FP Z).data "proof file" = .ok writtenPFull

/-- **The key file's half.** -/
def KeyWrittenOrRefuses (FK : VerifierAndGoals.PublicFiles → FileDescription XiK) (refuses : VerifierAndGoals.PublicFiles → Prop) : Prop :=
  ∀ Z : VerifierAndGoals.PublicFiles, VerifierAndGoals.InScope Z = true →
    refuses Z ∨ (FK Z).data "key file" = .ok writtenKFull

/-- The proof file's half follows from its half of the statement and a yes that is asked for. -/
theorem proof_written_or_refuses {FP : VerifierAndGoals.PublicFiles → FileDescription XiP}
    {yes refuses : VerifierAndGoals.PublicFiles → Prop} (hA : ProofWrittenAt FP yes) (hY : YesAsked refuses yes) :
    ProofWrittenOrRefuses FP refuses := by
  intro Z hZ
  by_cases hy : yes Z
  · exact .inr (hA Z hZ hy)
  · exact .inl (hY Z hZ hy)

/-- So does the key file's. -/
theorem key_written_or_refuses {FK : VerifierAndGoals.PublicFiles → FileDescription XiK}
    {yes refuses : VerifierAndGoals.PublicFiles → Prop} (hA : KeyWrittenAt FK yes) (hY : YesAsked refuses yes) :
    KeyWrittenOrRefuses FK refuses := by
  intro Z hZ
  by_cases hy : yes Z
  · exact .inr (hA Z hZ hy)
  · exact .inl (hY Z hZ hy)

/-- **Halves at two refusals give the sentence at "one of the two refuses".** -/
theorem writtenOrRefuses_of_halves {FP : VerifierAndGoals.PublicFiles → FileDescription XiP}
    {FK : VerifierAndGoals.PublicFiles → FileDescription XiK} {rP rK : VerifierAndGoals.PublicFiles → Prop}
    (hP : ProofWrittenOrRefuses FP rP) (hK : KeyWrittenOrRefuses FK rK) :
    WrittenOrRefuses FP FK fun Z => rP Z ∨ rK Z := by
  intro Z hZ
  rcases hP Z hZ with h | h
  · exact .inl (.inl h)
  · rcases hK Z hZ with k | k
    · exact .inl (.inr k)
    · exact .inr ⟨h, k⟩

/-- At one refusal the sentence is its two halves together. -/
theorem writtenOrRefuses_iff (FP : VerifierAndGoals.PublicFiles → FileDescription XiP) (FK : VerifierAndGoals.PublicFiles → FileDescription XiK)
    (refuses : VerifierAndGoals.PublicFiles → Prop) :
    WrittenOrRefuses FP FK refuses ↔
      ProofWrittenOrRefuses FP refuses ∧ KeyWrittenOrRefuses FK refuses := by
  constructor
  · intro H
    exact ⟨fun Z hZ => (H Z hZ).imp id fun h => h.1, fun Z hZ => (H Z hZ).imp id fun h => h.2⟩
  · rintro ⟨hP, hK⟩ Z hZ
    rcases hP Z hZ with h | h
    · exact .inl h
    · exact (hK Z hZ).imp id fun k => ⟨h, k⟩

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.proof_written_or_refuses
#print axioms VerifiableInference.PlanWritten.key_written_or_refuses
#print axioms VerifiableInference.PlanWritten.writtenOrRefuses_of_halves
#print axioms VerifiableInference.PlanWritten.writtenOrRefuses_iff
