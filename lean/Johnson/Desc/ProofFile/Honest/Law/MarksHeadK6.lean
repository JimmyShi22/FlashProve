-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/MarksHeadK6.lean: the hypothesis h₆ of `marksHead_hM`
(Honest/Law/MarksHead.lean), the bound for the two marks of the output head's own sub-protocol (K6)
in the form of the field `hM`, from a bound in the form in which K6's authors state theirs: at a
member of the chain that stands at K6's place, at every mark of their list. A check that the two
forms meet. No definition.

  1  `part4_place`   both marks stand at the library's place of K6 (`IM.k6Place`,
    Johnson/IMR/K6Seat.lean)
  2  `h6_of_member`   h₆ from such a bound
  3  `marksHead_hM_member6`   `marksHead_hM` with h₆ replaced by it

How. The field `hM` runs over the members b of the first chain in front of its last and asks of the
marks whose place is b's. A mark of K6's list has K6's place, so b stands there; b is a member of
the whole chain by the cut. The hypothesis hd is written after the statement of
`K6.part4Marks_debt_blocks` (Honest/K6/Law/K6MarksBlocks.lean, K6's authors' file), behind its first
two premises. This file does not import that file, so that the two agree is not shown here: the kit
C and the number kap₆ are letters.

Limits.
  * hd is a hypothesis. Nothing here shows it at any kit or number.
  * A check of form. No number is evaluated, and none is a chance.
  * The four other owners' bounds (h₁, h₃, h₄, h₅) stay hypotheses of `marksHead_hM_member6`.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.MarksHead
import Johnson.IMR.K6Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (RDT)
open _root_.Run.PQ (CK)

variable {Zp : ProofFile.Pub} {G₀ : ProofFile.Ground}

/-- K6's authors' marks stand at the library's place of K6. -/
theorem part4_place : ∀ mk ∈ K6.part4Marks Zp G₀, mk.place = IM.k6Place := by
  intro mk hmk
  unfold K6.part4Marks at hmk
  rcases List.mem_cons.1 hmk with rfl | h2
  · rfl
  · rcases List.mem_cons.1 h2 with rfl | h3
    · rfl
    · exact absurd h3 List.not_mem_nil

variable {S Cl : Type}

/-- **The hypothesis h₆ of `marksHead_hM`, from a bound at the member at K6's place.** all: the
chain's members; pre₁, e₁: those in front of the last, and the last. -/
theorem h6_of_member (C : CK) (kap₆ : ℝ≥0∞) {all pre₁ : List (Block S Cl)} {e₁ : Block S Cl}
    (cut : all = pre₁ ++ [e₁]) {PM : Block S Cl → List Fmt.Drawn → Prop}
    (hd : ∀ b ∈ all, b.place = IM.k6Place → ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → ∀ P : List Fmt.Drawn → Prop,
      ∀ mk ∈ K6.part4Marks Zp G₀, MarkDebt C mk dsb P ((mk.share.num : ℝ≥0∞) * kap₆)) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (K6.part4Marks Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt C mk dsb (PM b) ((mk.share.num : ℝ≥0∞) * kap₆) := by
  intro A b b' B e mk hmk dsb hf
  obtain ⟨hm, hpl⟩ := List.mem_filter.1 hmk
  have hpl' : (mk.place == b.place) = true := hpl
  have hb : b ∈ all := by
    rw [cut, e]
    exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
  have hp : b.place = IM.k6Place := (eq_of_beq hpl').symm.trans (part4_place mk hm)
  exact hd b hb hp dsb hf (PM b) mk hm

/-- `marksHead_hM` with h₆ replaced by a bound at the member at K6's place. -/
theorem marksHead_hM_member6 (C : CK) (kap₃ kap₆ : ℝ≥0∞) {all pre₁ : List (Block S Cl)}
    {e₁ : Block S Cl} (cut : all = pre₁ ++ [e₁]) {PM : Block S Cl → List Fmt.Drawn → Prop}
    (k₁ : ∀ mk ∈ P1K8.part1Marks Zp G₀,
      mk.place.kind ≠ KindName.K3 ∧ mk.place.kind ≠ KindName.K6)
    (h₁ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (P1K8.part1Marks Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (mk.share.val))
    (k₃ : ∀ mk ∈ K3.Good.k3Marks Zp G₀, mk.place.kind = KindName.K3)
    (h₃ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (K3.Good.k3Marks Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) ((mk.share.num : ℝ≥0∞) * kap₃))
    (k₄ : ∀ mk ∈ K4.k4MarksWide Zp G₀,
      mk.place.kind ≠ KindName.K3 ∧ mk.place.kind ≠ KindName.K6)
    (h₄ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (K4.k4MarksWide Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (mk.share.val))
    (k₅ : ∀ mk ∈ K5.k5Marks Zp G₀,
      mk.place.kind ≠ KindName.K3 ∧ mk.place.kind ≠ KindName.K6)
    (h₅ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (K5.k5Marks Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → MarkDebt C mk dsb (PM b) (mk.share.val))
    (hd : ∀ b ∈ all, b.place = IM.k6Place → ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds → ∀ P : List Fmt.Drawn → Prop,
      ∀ mk ∈ K6.part4Marks Zp G₀, MarkDebt C mk dsb P ((mk.share.num : ℝ≥0∞) * kap₆)) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (marksHead Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt C mk dsb (PM b) (qMHead kap₃ kap₆ b mk) :=
  marksHead_hM C kap₃ kap₆ k₁ h₁ k₃ h₃ k₄ h₄ k₅ h₅ (h6_of_member C kap₆ cut hd)

end ProofFile.Honest

#print axioms ProofFile.Honest.part4_place
#print axioms ProofFile.Honest.h6_of_member
#print axioms ProofFile.Honest.marksHead_hM_member6
