-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/StillAtAll.lean: THE SMALLNESS TEST's SECOND FALL: `StillAtZ`
(Johnson/P1K8R/BehindLast.lean) FOLLOWS WHOLE, AT ALL 25 SEGMENTS, FROM `WrapEnd`
(CountedAtRch.lean), WHICH THE HONEST SIDE's FRAME HANDS: THE HEAD's SEGMENT TOO. Lemmas; NONE OF
THE LIBRARY's GOALS. A joining. Nothing on completeness, soundness or hiding.

  **`heardAtZ_all`**   `heard_at_all` (Johnson/Desc/K8/Honest/HeardAtAll.lean), `built_there`
      (Johnson/P1K8R/BehindLast.lean)
  **`stillAtZ_all`**   `stillAtZ_of_heard` (Johnson/P1K8R/BehindHeard.lean)
  **`share_fallDebt_all`**, **`share_fallDebt_all_blocks`**   `share_fallDebt_head`,
      `share_fallDebt_head_blocks` (Johnson/P1K8R/BehindButHead.lean)
Limits. THE OBLIGATION MOVES; IT IS NOT MET: `WrapEnd`, `ShareLive`, `LiveFore` and `RowsAsked Z`
are premises. In scope alone: under an opening of the description and its test on its plan. Nothing
says that any state is reached. Like every file of this road it takes a cone under Johnson/Goal/
(through the sealed Johnson/IMR/ seats). No number is evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.BehindButHead
import Johnson.Desc.K8.Honest.HeardAtAll

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

/-- **`HeardAtZ` AT ALL 25 SEGMENTS, FROM WHAT THE FRAME HANDS.** By `heard_at_all`
(Johnson/Desc/K8/Honest/HeardAtAll.lean), whose end is `HeardAtZ`'s body. -/
theorem heardAtZ_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {s : S} (w : WrapEnd Z c l s) : HeardAtZ s := by
  obtain ⟨zp, h⟩ := w
  obtain ⟨Xl, e3⟩ := built_there hS hR O hl
  exact heard_at_all hS hR O hOk hl e3 h

/-- **So `StillAtZ`, whole, at all 25.** -/
theorem stillAtZ_all (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) {s : S} (w : WrapEnd Z c l s) : StillAtZ Z Bs l s :=
  stillAtZ_of_heard hS hR O hOk hl w (heardAtZ_all hS hR O hOk hl w)

/-- **THE SECOND FALL's SENTENCE WITH NOTHING OF `StillAtZ` LEFT: at typed challenges.** The
sentence and the number of `share_fallDebt_last`; the letter Q asks `WrapEnd`, `ShareLive` and
`LiveFore` alone. -/
theorem share_fallDebt_all (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' →
          WrapEnd Z c l s' ∧ ShareLive s' ∧ LiveFore s') →
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
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt_head hE hS hR O hOk hl
  refine ⟨b, p, X, hb, hp, hX, fun d he h5 h6 ft share Q hQ => ?_⟩
  exact H d he h5 h6 ft share Q fun fr s' hq =>
    ⟨(hQ fr s' hq).1, (hQ fr s' hq).2.1, (hQ fr s' hq).2.2,
      fun _ => heardAtZ_all hS hR O hOk hl (hQ fr s' hq).1⟩

/-- **The same at strings of hash blocks.** -/
theorem share_fallDebt_all_blocks (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' →
          WrapEnd Z c l s' ∧ ShareLive s' ∧ LiveFore s') →
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
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt_head_blocks hE hS hR O hOk hl
  refine ⟨b, p, X, hb, hp, hX, fun d he h5 h6 ft share Q hQ => ?_⟩
  exact H d he h5 h6 ft share Q fun fr s' hq =>
    ⟨(hQ fr s' hq).1, (hQ fr s' hq).2.1, (hQ fr s' hq).2.2,
      fun _ => heardAtZ_all hS hR O hOk hl (hQ fr s' hq).1⟩

end

end P1K8

#print axioms P1K8.heardAtZ_all
#print axioms P1K8.stillAtZ_all
#print axioms P1K8.share_fallDebt_all
#print axioms P1K8.share_fallDebt_all_blocks
