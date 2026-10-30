-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/BehindButHead.lean: THE SMALLNESS TEST's SECOND FALL: THE SENTENCE OF
`share_fallDebt_heard` (Johnson/P1K8R/BehindHeard.lean) WITH ONE MORE PAYMENT LAID IN: AT THE 24
SEGMENTS BELOW THE HEAD's, WHAT IT ASKED OF WHAT THE LOOKUP ON THE DIGITS HAS HEARD (`HeardAtZ`)
HOLDS AT EVERY STATE THAT `WrapEnd` ADMITS. SO OF `StillAtZ` (Johnson/P1K8R/BehindLast.lean) NOTHING
IS LEFT THERE; AT THE HEAD's SEGMENT ONE FIELD. Lemmas; NONE OF THE LIBRARY's GOALS. A joining.
Nothing on completeness, soundness or hiding.

  **`heardAtZ_below_head`**, `heardAtZ_of_head`, **`stillAtZ_below_head`**   `heard_at_wrap`
      (Johnson/Desc/K8/Honest/OneSentenceLeft.lean); `built_there` (BehindLast.lean);
      `stillAtZ_of_heard` (BehindHeard.lean)
  **`share_fallDebt_head`**, **`share_fallDebt_head_blocks`**   `share_fallDebt_heard`,
      `share_fallDebt_heard_blocks` by one call each
Limits. THE OBLIGATION MOVES; IT IS NOT MET: `WrapEnd`, `ShareLive`, `LiveFore`, `HeardAtZ` at the
head's segment and `RowsAsked Z` are premises; none is shown of any state or plan here. AT THE
HEAD's SEGMENT NOTHING OF `HeardAtZ` IS PAID. As in BehindFew.lean: whoever imports this file takes
a cone under Johnson/Goal/. No number is evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.BehindHeard
import Johnson.Desc.K8.Honest.OneSentenceLeft

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Slice
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (RDT uLT drawnT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open Johnson.Desc.First.Walk.Tied (Reach RchAt reach_raw reach_fold)
open ProofFile.Honest (Odds FallDebt)
open ProofFile.Honest.K8 (k8ShareFall k8Second)
open Iop
open scoped ENNReal

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **BELOW THE HEAD's SEGMENT `HeardAtZ` (Johnson/P1K8R/BehindHeard.lean) IS PAID AT EVERY STATE
THAT `WrapEnd` ADMITS**: our K8 author's reader's `heard_at_wrap`
(Johnson/Desc/K8/Honest/OneSentenceLeft.lean). -/
theorem heardAtZ_below_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {s : S} (w : WrapEnd Z c l s) : HeardAtZ s := by
  obtain ⟨zp, h⟩ := w
  rw [if_neg (by omega)] at h
  obtain ⟨Xl, e3⟩ := built_there hS hR O (by omega : l < 25)
  exact heard_at_wrap hS hR O hOk hl e3 h

/-- At all 25 segments, from what is left: the clause at the head's segment. -/
theorem heardAtZ_of_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {s : S} (w : WrapEnd Z c l s) (H : l = 24 → HeardAtZ s) :
    HeardAtZ s := by
  by_cases h4 : l < 24
  · exact heardAtZ_below_head hS hR O hOk h4 w
  · exact H (by omega)

/-- So `StillAtZ` (Johnson/P1K8R/BehindLast.lean), WHOLE, AT THE 24 SEGMENTS BELOW THE HEAD's, FROM
`WrapEnd` ALONE. -/
theorem stillAtZ_below_head (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 24) {s : S} (w : WrapEnd Z c l s) : StillAtZ Z Bs l s :=
  stillAtZ_of_heard hS hR O hOk (by omega) w (heardAtZ_below_head hS hR O hOk hl w)

/-- **THE SECOND FALL's SENTENCE WITH THAT PAYMENT LAID IN: at typed challenges.** The sentence and
the number of `share_fallDebt_last`; of the letter Q, in `StillAtZ`'s place: `HeardAtZ` at the
head's segment alone. -/
theorem share_fallDebt_head (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' →
          WrapEnd Z c l s' ∧ ShareLive s' ∧ LiveFore s' ∧ (l = 24 → HeardAtZ s')) →
        FallDebt (_root_.Run.ck .two)
          (k8ShareFall l (if l = 24 then 1 else 0) (ProofFile.k8NU Bs.G₀ X) share) ft b
          (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) [d] [] Q
          ((((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((2 * (X.tl.zzBlocks * X.tl.mz) * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((linkedCount X.tl * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((3 * X.tl.bzColumns * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (((symCount X.tl * (p.rows - 1) : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
              (((secondN X.tl : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) + 0)))))) := by
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt_heard hE hS hR O hOk hl
  refine ⟨b, p, X, hb, hp, hX, fun d he h5 h6 ft share Q hQ => ?_⟩
  exact H d he h5 h6 ft share Q fun fr s' hq =>
    ⟨(hQ fr s' hq).1, (hQ fr s' hq).2.1, (hQ fr s' hq).2.2.1,
      heardAtZ_of_head hS hR O hOk hl (hQ fr s' hq).1 (hQ fr s' hq).2.2.2⟩

/-- **The same at strings of hash blocks.** -/
theorem share_fallDebt_head_blocks (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' →
          WrapEnd Z c l s' ∧ ShareLive s' ∧ LiveFore s' ∧ (l = 24 → HeardAtZ s')) →
        FallDebt (_root_.Run.ckP .two)
          (k8ShareFall l (if l = 24 then 1 else 0) (ProofFile.k8NU Bs.G₀ X) share) ft b
          (c.blocksInOrder.drop (14 * l + (if l = 24 then 11 else 9) + 1)) [d] [] Q
          (kapSl 128 ^ 3 * (((ProofFile.k8NU Bs.G₀ X).getD 2 0 * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (kapSl 128 ^ 3 * ((2 * (X.tl.zzBlocks * X.tl.mz) * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (kapSl 128 ^ 3 * ((linkedCount X.tl * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (kapSl 128 ^ 3 * ((3 * X.tl.bzColumns * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
            (kapSl 128 ^ 3 * ((symCount X.tl * (p.rows - 1) : ℕ) : ℝ≥0∞) /
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
              (kapSl 128 ^ 3 * ((secondN X.tl : ℕ) : ℝ≥0∞) / ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) +
                0)))))) := by
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt_heard_blocks hE hS hR O hOk hl
  refine ⟨b, p, X, hb, hp, hX, fun d he h5 h6 ft share Q hQ => ?_⟩
  exact H d he h5 h6 ft share Q fun fr s' hq =>
    ⟨(hQ fr s' hq).1, (hQ fr s' hq).2.1, (hQ fr s' hq).2.2.1,
      heardAtZ_of_head hS hR O hOk hl (hQ fr s' hq).1 (hQ fr s' hq).2.2.2⟩

end

end P1K8

#print axioms P1K8.heardAtZ_below_head
#print axioms P1K8.heardAtZ_of_head
#print axioms P1K8.stillAtZ_below_head
#print axioms P1K8.share_fallDebt_head
#print axioms P1K8.share_fallDebt_head_blocks
