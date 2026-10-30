-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/PlanAtField.lean: THE FIELD planAt OF `LLT25.PlanOk₃` (hP), IN ITS OWN TEXT, AT THE JOIN's
OWN ms₂ := `Sh.ms A` · Ns := `numbersSh (Sh.t₁ A) (Sh.layU A) (Sh.layO A) a b` · r := `rWFull`,
A := `Sh.planAt Z N G`, general in ms₁ · N₁ · the stages · the frame · the description G'.
  **`planAt_field`**: the field FROM: `Written Z x`, the places and the named tests (they pay Omega's
    member's clauses one, two and five: Johnson/LLT25R/PlanAtOmega.lean) · hS (THE FIELD seats: clauses
    three and four at every one of mine) · hD (clause six at Omega's member: `noDeeperB`) ·
    hE (A NAMED TEST WITH CODE ON THE TWO ELDER MEMBERS ALONE: `planAt5B` at whoever of ms₁
    sits at N₁.w or N₁.index). Both tests: Johnson/P2LawR/PlanLeftAt.lean.
Limits. The two elder members' five clauses stay a test (their radii are read off the rows of the
sendings). hS · hD · hE are premises. No value is evaluated. Nothing on soundness.
-/
import Johnson.LLT25R.PlanAtOmega
import Johnson.LLT25R.LastMine

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LLT25.PlanB
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.K1 (realSized)
open Johnson.G (codesFull2)
open _root_.Desc.K14.Law _root_.Desc.K14.Law.Fence
open P2Law.PlanLeft
open ToldDesc (p14At)

/-- **The field planAt at the join's own list and numbers.** -/
theorem planAt_field {Xi Xi' : Type} (Z : ProofFile.Pub) (N : H2U.Places4) (G : FileDescription Xi)
    (G' : FileDescription Xi') {x : LinSized} (hx : realSized = some (x, codesFull2)) (h : Written Z x)
    (hN : H2U.placesOfMade Z.made = .ok N) (hT : Sh.Tests (Sh.planAt Z N G)) (Fr : Frame)
    (ms₁ : List Mem) (N₁ : Numbers) (a b : ℕ × ℕ) (stages : List Fmt.M1.Stage)
    (hS : SeatsFit (p14At Z).codes G' (mineOf ms₁ (Sh.ms (Sh.planAt Z N G)) N₁
      (numbersSh (Sh.t₁ (Sh.planAt Z N G)) (Sh.layU (Sh.planAt Z N G)) (Sh.layO (Sh.planAt Z N G))
        a b)))
    (hD : noDeeperB G' Fr (xOmega (Sh.planAt Z N G)) = true)
    (hE : ∀ st rest, stages = st :: rest →
      ((ms₁.filter fun y => decide (y.1.seat y.2 = N₁.w) || decide (y.1.seat y.2 = N₁.index)).all
        fun y => planAt5B G' (p14At Z).codes Fr H2K.Member.rWFull st y) = true) :
    ∀ y ∈ (mineOf ms₁ (Sh.ms (Sh.planAt Z N G)) N₁
      (numbersSh (Sh.t₁ (Sh.planAt Z N G)) (Sh.layU (Sh.planAt Z N G)) (Sh.layO (Sh.planAt Z N G))
        a b)), ∀ st rest, stages = st :: rest →
      LLT25.PlanAt (p14At Z).codes G' Fr H2K.Member.rWFull st y := by
  intro y hy st rest hst
  rcases mem_mineOf.1 hy with ⟨hm, hw⟩ | ⟨hm, hs⟩
  · have hf : y ∈ ms₁.filter fun y =>
        decide (y.1.seat y.2 = N₁.w) || decide (y.1.seat y.2 = N₁.index) := by
      refine List.mem_filter.2 ⟨hm, ?_⟩
      rcases hw with e | e
      · simp [e]
      · simp [e]
    exact (planAt_iff G' (p14At Z).codes Fr _ st y (hS y hy)).1
      (List.all_eq_true.1 (hE st rest hst) y hf)
  · obtain rfl := eq_xOmega (Sh.planAt Z N G) hT y hm hs
    exact planAt_omega Z N G G' hx h hN hT Fr st (hS _ hy) hD

end LLT25.PlanB

#print axioms LLT25.PlanB.planAt_field
