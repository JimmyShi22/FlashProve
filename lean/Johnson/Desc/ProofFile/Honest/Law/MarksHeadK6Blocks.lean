-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/MarksHeadK6Blocks.lean: a check that two forms meet. K6's authors'
bound for their two marks at one named kit, strings of hash blocks (`K6.part4Marks_debt_blocks`,
Honest/K6/Law/K6MarksBlocks.lean), is called at the hypothesis h₆ of `marksHead_hM`
(Honest/Law/MarksHead.lean). No definition.

  1  `h6_blocks`   h₆ at the kit `Run.ckP .two`, with the letter kap₆ set to the one number of that
    bound
  2  `marksHead_hM_blocks6`   `marksHead_hM` at that kit and number, without h₆

How. `h6_of_member` (Honest/Law/MarksHeadK6.lean), whose hypothesis is paid by one call of K6's
authors' theorem.

Limits.
  * It shows that the forms meet, and no more. All limits of Honest/K6/Law/K6MarksBlocks.lean hold
    here. At one kit alone. The uniform law on the rounds' messages is named, not derived. The
    marks' stated shares are not shown to be held at this kit: they lack the factor `Iop.kapSl 128 ^
    3`; their numerators alone are spent.
  * K6's authors' six statements speak of a chance. By their own head no reviewer who owns such
    statements has seen them. Nothing here is a result before that.
  * No number is evaluated, and none is quoted as a chance.
  * The library's hypothesis `P5J.AtMgA`, hG and the cut are hypotheses. The four other owners'
    bounds (h₁, h₃, h₄, h₅) stay hypotheses of `marksHead_hM_blocks6`.
  * By the head of K6's authors' file its hypothesis h stands at the full size and the format's
    second hash function alone. The same h is asked here.
  * The lemmas prove no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.MarksHeadK6
import Johnson.Desc.ProofFile.Honest.K6.Law.K6MarksBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open scoped ENNReal
open VerifiableInference.Desc
open OnBytes.Maker (WholeD RDT)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {G₀ : ProofFile.Ground}

/-- **The hypothesis h₆ of `marksHead_hM` at strings of hash blocks**, by K6's authors' bound. -/
theorem h6_blocks (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) {pre₁ : List (Block P5J.TS ProofFile.Cl)}
    {e₁ : Block P5J.TS ProofFile.Cl} (cut : cF.blocksInOrder = pre₁ ++ [e₁])
    {PM : Block P5J.TS ProofFile.Cl → List Fmt.Drawn → Prop} :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (K6.part4Marks Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (PM b)
        ((mk.share.num : ℝ≥0∞) * (Iop.kapSl 128 ^ 3 / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞))) :=
  h6_of_member (_root_.Run.ckP .two) _ cut fun _ hb hp dsb hf P =>
    K6.part4Marks_debt_blocks h hG hb hp dsb hf P

/-- `marksHead_hM` at strings of hash blocks, without h₆. -/
theorem marksHead_hM_blocks6 (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) (kap₃ : ℝ≥0∞)
    {pre₁ : List (Block P5J.TS ProofFile.Cl)} {e₁ : Block P5J.TS ProofFile.Cl}
    (cut : cF.blocksInOrder = pre₁ ++ [e₁]) {PM : Block P5J.TS ProofFile.Cl → List Fmt.Drawn → Prop}
    (k₁ : ∀ mk ∈ P1K8.part1Marks Zp G₀,
      mk.place.kind ≠ KindName.K3 ∧ mk.place.kind ≠ KindName.K6)
    (h₁ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (P1K8.part1Marks Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (PM b) (mk.share.val))
    (k₃ : ∀ mk ∈ K3.Good.k3Marks Zp G₀, mk.place.kind = KindName.K3)
    (h₃ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (K3.Good.k3Marks Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (PM b) ((mk.share.num : ℝ≥0∞) * kap₃))
    (k₄ : ∀ mk ∈ K4.k4MarksWide Zp G₀,
      mk.place.kind ≠ KindName.K3 ∧ mk.place.kind ≠ KindName.K6)
    (h₄ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (K4.k4MarksWide Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (PM b) (mk.share.val))
    (k₅ : ∀ mk ∈ K5.k5Marks Zp G₀,
      mk.place.kind ≠ KindName.K3 ∧ mk.place.kind ≠ KindName.K6)
    (h₅ : ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (K5.k5Marks Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (PM b) (mk.share.val)) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B →
      ∀ mk ∈ (marksHead Zp G₀).filter (fun m => m.place == b.place), ∀ dsb : List RDT,
      List.Forall₂ KindFits dsb b.rounds →
      MarkDebt (_root_.Run.ckP .two) mk dsb (PM b)
        (qMHead kap₃ (Iop.kapSl 128 ^ 3 / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞)) b mk) :=
  marksHead_hM (_root_.Run.ckP .two) kap₃ _ k₁ h₁ k₃ h₃ k₄ h₄ k₅ h₅ (h6_blocks h hG cut)

end ProofFile.Honest

#print axioms ProofFile.Honest.h6_blocks
#print axioms ProofFile.Honest.marksHead_hM_blocks6
