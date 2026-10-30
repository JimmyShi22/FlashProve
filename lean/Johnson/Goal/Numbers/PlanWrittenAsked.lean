-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Numbers/PlanWrittenAsked.lean: "in scope, either the verifier refuses everything, or
both files' data are the written data": the sentence, with letters for the makers of the two
descriptions and for what a refusal is, and the two statements from which it follows.

`PlanWrittenAt FP FK yes` (Johnson/Goal/Numbers/PlanWrittenRow.lean) says that in scope, where `yes
Z` holds, the data of the two files' descriptions are the written data. Its letter `yes` is free,
and the statement is only as strong as the yes that is named. With a yes that never holds it is true
of any makers. With the test itself for yes, its premise `SeatLaid` is true of any makers
(`seatLaid_of_test`). So the statement alone says nothing about a verifier. What is missing is that
the verifier asks for the yes: where it fails, the verifier refuses. That is `YesAsked` here.

Row or tool. Every declaration here is a tool: the makers, the yes and the refusal are letters, and
no description is named. At named makers, a named yes and the verifier's own refusal,
`WrittenOrRefuses` is the first clause of a row.

What is here.
  `YesAsked refuses yes`: for every Z in scope, where `yes Z` fails, `refuses Z` holds. `refuses Z`
    is to be the words of whoever lays the descriptions for "the verifier says no to everything at
    the public files Z". `yes Z` is to be their "the descriptions are laid at Z", not the test.
  `WrittenOrRefuses FP FK refuses`: the sentence: for every Z in scope, `refuses Z`, or the data of
    `FP Z` are `writtenPFull` and those of `FK Z` are `writtenKFull`. No yes is named in it.
  `written_or_refuses`: `PlanWrittenAt FP FK yes` and `YesAsked refuses yes` give the sentence. By
    cases on `yes Z`. `written_or_refuses_of_seat`: so do `SeatLaid FP FK yes` and `YesAsked refuses
    yes`.
  `planWrittenAt_idle`, `yesAsked_never`: with a yes that holds nowhere in scope, `PlanWrittenAt` is
    true of any makers, and `YesAsked` says that the verifier refuses at every Z in scope. So
    `YesAsked` bears the weight: an idle yes is paid for there.
  `seatLaid_of_test`: with the two tests themselves for yes, `SeatLaid` is true of any makers.
    `writtenOrRefuses_idle`: with a refusal that holds everywhere in scope, the sentence is true of
    any makers.
  `not_writtenOrRefuses`: the sentence can fail: at a Z in scope where the verifier does not refuse
    and the proof file's description has another depth than 32, it is false.

Limits. No description, no yes and no refusal is named, and neither premise is shown of any. The
letter `refuses` is as free as `yes`: the sentence is only as strong as the refusal that is named,
and with a refusal that always holds it says nothing (`writtenOrRefuses_idle`). It has content only
where `refuses Z` is in truth "the verifier says no to everything at Z", and, for an honest prover's
sake, where that fails at the public files that are meant to be served, which a run alone can show.
That a Z is in scope is held by tests of the build (Ladder/Guards.lean), by no theorem known to this
file, so `not_writtenOrRefuses` has that premise. The sentence speaks of the data alone: the
declared rounds, written out, without the first chain's last round, and the depth. It says nothing
of what else a description holds, and nothing on which hash function a description's text reaches.
`written_or_refuses` uses the law of the excluded middle on `yes Z`. All limits of
Johnson/Goal/Numbers/PlanWrittenRow.lean. Nothing on soundness.


-/
import Johnson.Goal.Numbers.PlanWrittenRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open Johnson.G VerifiableInference.Desc

variable {XiP XiK : Type}

/-- **The verifier asks for the yes**: in scope, where `yes Z` fails, `refuses Z` holds. refuses:
the words of whoever lays the descriptions for "the verifier says no to everything at Z". -/
def YesAsked (refuses yes : VerifierAndGoals.PublicFiles → Prop) : Prop :=
  ∀ Z : VerifierAndGoals.PublicFiles, VerifierAndGoals.InScope Z = true → ¬ yes Z → refuses Z

/-- **The sentence**: in scope, either the verifier refuses everything, or both files' data are the
written data. -/
def WrittenOrRefuses (FP : VerifierAndGoals.PublicFiles → FileDescription XiP) (FK : VerifierAndGoals.PublicFiles → FileDescription XiK)
    (refuses : VerifierAndGoals.PublicFiles → Prop) : Prop :=
  ∀ Z : VerifierAndGoals.PublicFiles, VerifierAndGoals.InScope Z = true →
    refuses Z ∨
      ((FP Z).data "proof file" = .ok writtenPFull ∧ (FK Z).data "key file" = .ok writtenKFull)

/-- **The sentence follows from the two statements.** -/
theorem written_or_refuses {FP : VerifierAndGoals.PublicFiles → FileDescription XiP} {FK : VerifierAndGoals.PublicFiles → FileDescription XiK}
    {yes refuses : VerifierAndGoals.PublicFiles → Prop} (hA : PlanWrittenAt FP FK yes)
    (hY : YesAsked refuses yes) : WrittenOrRefuses FP FK refuses := by
  intro Z hZ
  by_cases hy : yes Z
  · exact .inr (hA Z hZ hy)
  · exact .inl (hY Z hZ hy)

/-- It follows where the test is laid beneath a yes that the verifier asks for. -/
theorem written_or_refuses_of_seat {FP : VerifierAndGoals.PublicFiles → FileDescription XiP}
    {FK : VerifierAndGoals.PublicFiles → FileDescription XiK} {yes refuses : VerifierAndGoals.PublicFiles → Prop}
    (hS : SeatLaid FP FK yes) (hY : YesAsked refuses yes) : WrittenOrRefuses FP FK refuses :=
  written_or_refuses (planWrittenAt_of_seat hS) hY

/-! ## Which of the two statements bears the weight -/

/-- With a yes that holds nowhere in scope, `PlanWrittenAt` is true of any makers. -/
theorem planWrittenAt_idle (FP : VerifierAndGoals.PublicFiles → FileDescription XiP) (FK : VerifierAndGoals.PublicFiles → FileDescription XiK)
    {yes : VerifierAndGoals.PublicFiles → Prop} (h : ∀ Z, VerifierAndGoals.InScope Z = true → ¬ yes Z) :
    PlanWrittenAt FP FK yes := fun Z hZ hy => absurd hy (h Z hZ)

/-- With such a yes, `YesAsked` says that the verifier refuses at every Z in scope. -/
theorem yesAsked_never {refuses yes : VerifierAndGoals.PublicFiles → Prop}
    (h : ∀ Z, VerifierAndGoals.InScope Z = true → ¬ yes Z) :
    YesAsked refuses yes ↔ ∀ Z, VerifierAndGoals.InScope Z = true → refuses Z :=
  ⟨fun H Z hZ => H Z hZ (h Z hZ), fun H Z hZ _ => H Z hZ⟩

/-- With the two tests themselves for yes, `SeatLaid` is true of any makers. -/
theorem seatLaid_of_test (FP : VerifierAndGoals.PublicFiles → FileDescription XiP) (FK : VerifierAndGoals.PublicFiles → FileDescription XiK) :
    SeatLaid FP FK fun Z =>
      seatPinnedProof Z.pol (FP Z) = true ∧ seatPinnedKey Z.pol (FK Z) = true :=
  fun _ _ h => h

/-- With a refusal that holds everywhere in scope, the sentence is true of any makers. -/
theorem writtenOrRefuses_idle (FP : VerifierAndGoals.PublicFiles → FileDescription XiP) (FK : VerifierAndGoals.PublicFiles → FileDescription XiK)
    {refuses : VerifierAndGoals.PublicFiles → Prop} (h : ∀ Z, VerifierAndGoals.InScope Z = true → refuses Z) :
    WrittenOrRefuses FP FK refuses := fun Z hZ => .inl (h Z hZ)

/-- **The sentence can fail**: at a Z in scope where the verifier does not refuse and the proof
file's description has another depth than 32. -/
theorem not_writtenOrRefuses {FP : VerifierAndGoals.PublicFiles → FileDescription XiP} {FK : VerifierAndGoals.PublicFiles → FileDescription XiK}
    {refuses : VerifierAndGoals.PublicFiles → Prop} {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    (hr : ¬ refuses Z) (hd : (FP Z).tableDepth ≠ 32) : ¬ WrittenOrRefuses FP FK refuses := by
  intro H
  rcases H Z hZ with h | h
  · exact hr h
  · exact hd (data_depth h.1).symm

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.written_or_refuses
#print axioms VerifiableInference.PlanWritten.written_or_refuses_of_seat
#print axioms VerifiableInference.PlanWritten.planWrittenAt_idle
#print axioms VerifiableInference.PlanWritten.yesAsked_never
#print axioms VerifiableInference.PlanWritten.seatLaid_of_test
#print axioms VerifiableInference.PlanWritten.writtenOrRefuses_idle
#print axioms VerifiableInference.PlanWritten.not_writtenOrRefuses
