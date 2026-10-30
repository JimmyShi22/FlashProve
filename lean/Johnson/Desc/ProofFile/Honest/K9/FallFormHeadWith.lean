-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K9/FallFormHeadWith.lean: K9's FALL AT THE OUTPUT HEAD's SEGMENT (l = 24), IN THE FORM OF
THE FRAME's PREMISE hF9, AT THE SMALLNESS TEST's HOUSE's OWN GATE's CONDITION `PWith Zp cF Bs Pr`
(Johnson/P1K8R/LastAtAsks.lean): `k9_fallDebt_form_at` (Honest/K9/FallFormAny.lean) called at I := (· = 24) and PW :=
that condition. EXCHANGED, NOT PAID. The sister of Honest/K9/FallFormAttWith.lean and FallFormLayWith.lean. One
statement and its proof; no definition; no goal is stated.
  **`k9_fallDebt_form_head_with`** under the head · cut · hPr24: at the batching of the head's segment (the member
      number 14 · 24 + 11 = 347), at K9's seat there: Pr b fr s' gives `goodW p ‹the segment's gatherer› s'
      w.2.2.filled` · hq: the inequality on the letter qF at l = 24. THE END: hF9's text at l := 24, with fs for the
      list of falls, the gate's condition to the letter. "Reached by the wrapped blocks" is `PWith`'s own second half.
      Bs is a letter, read by `PWith` alone
WHAT IS NOT CLAIMED. hPr24 at any Pr, here: Honest/K9/GoodHeadHandedMarks.lean has its end at the state that a walk
hands, from the silence of listed marks; the link from the frame's field to that walk is `headE_handed`
(Johnson/P1K8R/FieldAtHead.lean), and `firstAsks_k9` (Johnson/P1K8R/MemberAtK9.lean) pays hPr24 at one condition: the
caller's Pr together with `goodW` itself. qF is an open letter: whoever calls this lays it at or above the bound in hq.
The limits in Honest/K9/FallFormAny.lean's head hold here. Called by Johnson/P1K8R/MemberAtK9.lean alone. At the full
size and the format's second hash function alone, as h. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.FallFormAny

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

/-- **THE FRAME's PREMISE ON K9's FALL AT THE OUTPUT HEAD's SEGMENT, AT THE SMALLNESS TEST's HOUSE's OWN GATE's
CONDITION, EXCHANGED**: its end is that premise's text at l := 24. -/
theorem k9_fallDebt_form_head_with (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Bs : ProofFile.PureBase)
    (fs : List (Fall S)) (notGood : ℕ → Odds) {pre₁ : List (Block S ProofFile.Cl)} {e₁ : Block S ProofFile.Cl}
    (cut : cF.blocksInOrder = pre₁ ++ [e₁]) (Pr : Block S ProofFile.Cl → List Fmt.Drawn → S → Prop)
    (qF : Block S ProofFile.Cl → Fall S → ℝ≥0∞)
    (hPr24 : ∀ b, cF.blocksInOrder[14 * 24 + 11]? = some b → ∀ Lk p w, SeatedFree cF Zp 24 9 Lk p w →
      ∀ fr s', Pr b fr s' → goodW p (claimsInBy Lk.each Lk.hear Lk.order) s' w.2.2.filled)
    (hq : ∀ b p u, IM.k9At Zp 24 = some p → Desc.K9.testsWhere Zp.p.X 24 0 = some u →
      kapSl 128 ^ 3 * ((u.2.2.filled * (u.2.1 - 1) : ℕ) : ℝ≥0∞) / ((sizeOfE : ℕ) : ℝ≥0∞) ≤
        qF b (quietFall p u.2.2.filled (u.2.1 - 1) (notGood 24))) :
    ∀ A b b' B, pre₁ = A ++ b :: b' :: B → (fallSeat P5J.At.links) b.place = true → b.rounds ≠ [] →
      ∀ p u, IM.k9At Zp 24 = some p → Desc.K9.testsWhere Zp.p.X 24 0 = some u →
      quietFall p u.2.2.filled (u.2.1 - 1) (notGood 24) ∈ repsAt cF.blocksInOrder fs b →
      ∀ dsb : List RDT, List.Forall₂ KindFits dsb b.rounds →
      FallDebt (_root_.Run.ckP .two) (quietFall p u.2.2.filled (u.2.1 - 1) (notGood 24)) 0 b
        (b' :: B ++ [e₁]) dsb [] (P1K8.PWith Zp cF Bs Pr b)
        (qF b (quietFall p u.2.2.filled (u.2.1 - 1) (notGood 24))) := by
  intro A b b' B e hs hr p u hp hu hmem dsb hk
  refine k9_fallDebt_form_at h fs notGood cut (P1K8.PWith Zp cF Bs Pr) qF (fun l => l = 24) ?_ ?_ A b b' B e hs hr 24 p
    u (by omega) rfl hp hu hmem dsb hk
  · intro l hl hI b hb Lk p w Sd fr s' hP
    obtain ⟨zp, hz⟩ := (hP.2 l hl hb).1
    refine ⟨?_, zp, hz⟩
    have h24 : l = 24 := hI
    subst h24
    exact hPr24 b hb Lk p w Sd fr s' hP.1
  · intro l _ hI b p u hp hu
    have h24 : l = 24 := hI
    subst h24
    exact hq b p u hp hu

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.k9_fallDebt_form_head_with
