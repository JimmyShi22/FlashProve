-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/FallFormLayWith.lean: K9's FALL AT THE TWELVE FEED-FORWARD SEGMENTS, IN THE FORM OF THE
FRAME's PREMISE hF9, AT THE SMALLNESS TEST's HOUSE's OWN GATE's CONDITION `PWith Zp cF Bs Pr`
(Johnson/P1K8R/LastAtAsks.lean): `k9_fallDebt_form_lay` (Honest/K9/FallFormLay.lean) called at PW := that condition. OF
ITS PREMISE hPW's TWO CONJUNCTS THE SECOND IS PAID; THE FIRST IS ASKED OF THE CALLER's LETTER Pr. EXCHANGED, NOT PAID.
The twin of Honest/K9/FallFormAttWith.lean. One statement and its proof; no definition; no goal is stated.
  **`k9_fallDebt_form_lay_with`**   under the head · hB · cut · hPr1: at the batching of 2 g, Pr b fr s' gives
      `BatFrontLay p4 u.2.2.filled s'` · hq. THE END: hF9's text at l := 2 g, with fs for the list of falls, the gate's
      condition to the letter. "Reached by the wrapped blocks" is `PWith`'s own second half: `PLast`'s first clause
      `WrapEnd` at 2 g
WHAT IS NOT CLAIMED. hPr1 at any Pr, here: `firstAsks_k9` (Johnson/P1K8R/MemberAtK9.lean) pays it at
one condition: the caller's Pr together with `BatFrontLay` itself, which `layE_handed`
(Johnson/P1K8R/FieldAtLay.lean) has at what the frame's field hands. All that
Honest/K9/FallFormLay.lean's and FallFormAny.lean's heads say holds here. Called by
Johnson/P1K8R/MemberAtK9.lean alone. Nothing on any property.
GROUND: beneath this file, beside the sealed library (laws.11), lie 506 files, this one among them: reading copies, all
but ours.
-/
import Johnson.Desc.ProofFile.Honest.K9.FallFormLay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Maker (RDT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest (Odds Fall FallDebt KindFits repsAt fallSeat)
open Iop
open scoped ENNReal

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **The same at the smallness test's house's own gate's condition** `PWith Zp cF Bs Pr`: "reached by the wrapped
blocks" is that condition's own (`PLast`'s first clause `WrapEnd`); `BatFrontLay` is asked of Pr. -/
theorem k9_fallDebt_form_lay_with (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (fs : List (Fall S)) (notGood : ℕ → Odds) {pre₁ : List (Block S ProofFile.Cl)} {e₁ : Block S ProofFile.Cl}
    (cut : cF.blocksInOrder = pre₁ ++ [e₁]) (Pr : Block S ProofFile.Cl → List Fmt.Drawn → S → Prop)
    (qF : Block S ProofFile.Cl → Fall S → ℝ≥0∞)
    (hPr1 : ∀ g, g < 12 → ∀ b, cF.blocksInOrder[14 * (2 * g) + 9]? = some b → ∀ p4 u,
      LPFK9.k4ParAt Zp Bs.G₀ (2 * g) = some p4 → Desc.K9.testsWhere Zp.p.X (2 * g) 0 = some u →
      ∀ fr s', Pr b fr s' → BatFrontLay p4 u.2.2.filled s')
    (hq : ∀ g, g < 12 → ∀ b p u, IM.k9At Zp (2 * g) = some p →
      Desc.K9.testsWhere Zp.p.X (2 * g) 0 = some u →
      kapSl 128 ^ 3 * ((u.2.2.filled * (u.2.1 - 1) : ℕ) : ℝ≥0∞) / ((sizeOfE : ℕ) : ℝ≥0∞) ≤
        qF b (quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g)))) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B → (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ g p u, g < 12 → IM.k9At Zp (2 * g) = some p →
      Desc.K9.testsWhere Zp.p.X (2 * g) 0 = some u →
      quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g)) ∈ repsAt cF.blocksInOrder fs b →
      ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt (_root_.Run.ckP .two) (quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g))) 0 b
        (b' :: B ++ [e₁]) dsb [] (P1K8.PWith Zp cF Bs Pr b)
        (qF b (quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g)))) := by
  refine k9_fallDebt_form_lay h hB fs notGood cut (P1K8.PWith Zp cF Bs Pr) qF ?_ hq
  intro g hg b hb p4 u h4 hu fr s' hP
  have hb' : cF.blocksInOrder[14 * (2 * g) + (if 2 * g = 24 then 11 else 9)]? = some b := by
    rw [if_neg (by omega)]
    exact hb
  obtain ⟨zp, hz⟩ := (hP.2 (2 * g) (by omega) hb').1
  rw [if_neg (by omega)] at hz
  exact ⟨hPr1 g hg b hb p4 u h4 hu fr s' hP.1, zp, hz⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.k9_fallDebt_form_lay_with
