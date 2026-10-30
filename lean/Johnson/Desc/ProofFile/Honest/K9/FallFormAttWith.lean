-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/FallFormAttWith.lean: K9's FALL ON THE FREE SLOTS AT THE TWELVE ATTENTION SEGMENTS, IN
THE FORM OF THE FRAME's PREMISE hF9, AT THE SMALLNESS TEST's HOUSE's OWN GATE's CONDITION `PWith Zp cF Bs Pr`
(Johnson/P1K8R/LastAtAsks.lean): `k9_fallDebt_form_att` (Honest/K9/FallFormAtt.lean) called at PW := that condition. OF
ITS PREMISE hPW's FOUR CONJUNCTS THE FOURTH IS PAID; THE OTHER THREE ARE ASKED OF THE CALLER's LETTER Pr. EXCHANGED, NOT
PAID. One statement and its proof; no definition; no goal is stated.
  **`k9_fallDebt_form_att_with`**   under the head · cut · u₀: any `HTailF2` · hPr3: at the batching of 2 g + 1, Pr b fr
      s' gives `HeldLive` and the lookups' `Clause` at what each of the two lookups has heard · hq, as there. THE END:
      hF9's text at l := 2 g + 1, with fs for the list of falls, the gate's condition now to the letter. "Reached by the
      wrapped blocks" is `PWith`'s own second half: `PLast`'s first clause `WrapEnd` (Johnson/P1K8R/LastAtFrame.lean,
      CountedAtRch.lean) at 2 g + 1
WHAT IS NOT CLAIMED. hPr3 at any Pr, here: `attClauses_handed` (Johnson/P1K8R/ClausesAtFrame.lean)
ends in the three at what the frame's field hands: `firstAsks_k9` (Johnson/P1K8R/MemberAtK9.lean)
lays them into the condition beside the caller's Pr and pays them there by `attE_handed`
(Johnson/P1K8R/FieldAtAtt.lean). All that Honest/K9/FallFormAtt.lean's head says of hq, of where the
statement is true for nothing, and of the other thirteen segments holds here. Called by
Johnson/P1K8R/MemberAtK9.lean alone. Nothing on any property.
GROUND: beneath this file, beside the sealed library (laws.11), lie 532 files, this one among them: reading copies, all
but ours.
-/
import Johnson.Desc.ProofFile.Honest.K9.FallFormAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open OnBytes OnBytes.Model
open OnBytes.Maker (RDT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest (Odds Fall FallDebt KindFits repsAt fallSeat)
open Iop
open H2K5.Honest (HeldLive)
open VerifiableInference.Desc.First.Look (placeAt)
open ProofFile.Honest.K3.Good.Live (Clause)
open scoped ENNReal

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place}

/-- **The same at the smallness test's house's own gate's condition** `PWith Zp cF Bs Pr`: "reached by the wrapped
blocks" is that condition's own (`PLast`'s first clause `WrapEnd`); the three sentences on what was heard are asked of
Pr. -/
theorem k9_fallDebt_form_att_with (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (u₀ : HTailF2)
    (fs : List (Fall S)) (notGood : ℕ → Odds) {pre₁ : List (Block S ProofFile.Cl)} {e₁ : Block S ProofFile.Cl}
    (cut : cF.blocksInOrder = pre₁ ++ [e₁]) (Bs : ProofFile.PureBase) (Pr : Block S ProofFile.Cl → List Fmt.Drawn → S → Prop)
    (qF : Block S ProofFile.Cl → Fall S → ℝ≥0∞)
    (hPr3 : ∀ g, g < 12 → ∀ b, cF.blocksInOrder[14 * (2 * g + 1) + 9]? = some b → ∀ a pC pD,
      (P5J.At.X Zp).A[g]? = some a → placeAt (P5J.At.X Zp) (2 * g + 1) false = some pC →
      placeAt (P5J.At.X Zp) (2 * g + 1) true = some pD → ∀ fr s', Pr b fr s' →
      HeldLive a.own (Forest.elems a.fs) s' ∧ Clause pC s'.lookHeard? ∧ Clause pD (s'.tl?.bind (·.heard)))
    (hq : ∀ g, g < 12 → ∀ b p u, IM.k9At Zp (2 * g + 1) = some p →
      Desc.K9.testsWhere Zp.p.X (2 * g + 1) 0 = some u →
      kapSl 128 ^ 3 * ((u.2.2.filled * (u.2.1 - 1) : ℕ) : ℝ≥0∞) / ((sizeOfE : ℕ) : ℝ≥0∞) ≤
        qF b (quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g + 1)))) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B → (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ g p u, g < 12 → IM.k9At Zp (2 * g + 1) = some p →
      Desc.K9.testsWhere Zp.p.X (2 * g + 1) 0 = some u →
      quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g + 1)) ∈ repsAt cF.blocksInOrder fs b →
      ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt (_root_.Run.ckP .two) (quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g + 1))) 0 b
        (b' :: B ++ [e₁]) dsb [] (P1K8.PWith Zp cF Bs Pr b)
        (qF b (quietFall p u.2.2.filled (u.2.1 - 1) (notGood (2 * g + 1)))) := by
  refine k9_fallDebt_form_att h u₀ fs notGood cut (P1K8.PWith Zp cF Bs Pr) qF ?_ hq
  intro g hg b hb a pC pD ha hC hD fr s' hP
  obtain ⟨h1, h2, h3⟩ := hPr3 g hg b hb a pC pD ha hC hD fr s' hP.1
  have hb' : cF.blocksInOrder[14 * (2 * g + 1) + (if 2 * g + 1 = 24 then 11 else 9)]? = some b := by
    rw [if_neg (by omega)]
    exact hb
  obtain ⟨zp, hz⟩ := (hP.2 (2 * g + 1) (by omega) hb').1
  rw [if_neg (by omega)] at hz
  exact ⟨h1, h2, h3, zp, hz⟩

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.k9_fallDebt_form_att_with
