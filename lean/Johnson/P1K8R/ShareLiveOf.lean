-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ShareLiveOf.lean: THE SMALLNESS TEST's SECOND FALL: OF WHAT WAS STILL OWED OF THE
STATE IN FRONT OF THE BATCHING (`ShareOwed`, Johnson/P1K8R/ShareNeedsOf.lean) THE FIFTH CLAUSE, "THE
UPPER VIRTUAL ROWS OF THE DIGITS' ARRAY BEGIN AT COLUMN 0", IS PAID: FOUR TESTS ON WHAT WAS HEARD
ARE LEFT. A definition and lemmas; NONE OF THE LIBRARY's GOALS. Nothing on completeness, soundness
or hiding. An assembly: no new argument.

  `ShareLive s'`   whatever data and ledger the state holds pass `planesLive`, `digitsLive`,
      `readsLive`, `symbolsLive`
  **`shareOwed_of`**   in the goals' scope, under an opening of the description, at l < 25: `FoldEnd
      Z c l s'` and `ShareLive s'` give `ShareOwed s'`
  **`share_fallDebt_live`**, **`share_fallDebt_live_blocks`**   `share_fallDebt_plan`,
      `share_fallDebt_plan_blocks` with `ShareLive` in `ShareOwed`'s place
By: LinkJoin.l0_at_batch (Johnson/P1K8R/ZeroSeat.lean) · reach_of_fold
(Johnson/Top/H0/Walk/Reach.lean).
Limits. The number for `secondNo` stays a letter. `RowsAsked Z` stays a premise. `ShareLive` is
shown of no state here. No number is evaluated.
-/
import Johnson.P1K8R.ShareNeedsOf
import Johnson.P1K8R.ZeroSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.Slice
open OnBytes.Model.Stages (LinkH)
open OnBytes.Maker (RDT uLT drawnT)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open VerifiableInference.Desc.K9Asks (RowsAsked)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)
open ProofFile.Honest (Odds FallDebt)
open ProofFile.Honest.K8 (k8ShareFall)
open Iop
open scoped ENNReal

/-- The four tests on what was heard. -/
def ShareLive (s' : S) : Prop :=
  ∀ tl F', s'.tl? = some tl → s'.fork? = some F' →
    planesLive tl = true ∧ digitsLive tl = true ∧ readsLive tl = true ∧ symbolsLive tl = true

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **The fifth clause, paid.** -/
theorem shareOwed_of (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    {b : Block S Claim} (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b) {s' : S}
    (hf : FoldEnd Z c l s') (hw : ShareLive s') : ShareOwed s' := by
  obtain ⟨zp, rs, r, cs, c', hfold⟩ := hf
  have hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (zp, s') :=
    reach_of_fold _ (List.getElem?_eq_some_iff.1 hb).1.le s' rs r cs c' hfold
  intro tl F' ht hF
  obtain ⟨w1, w2, w3, w4⟩ := hw tl F' ht hF
  exact ⟨w1, w2, w3, w4, LinkJoin.l0_at_batch hS hR O hl hr hF⟩

/-- **The second fall's sentence under the four tests: at typed challenges.** -/
theorem share_fallDebt_live (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (qS : ℝ≥0∞)
          (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' → Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ck .two) [d]) |
          behindT b secondNo s' (drawnT (_root_.Run.ck .two) [d] ρ) = true} ≤ qS) →
        (∀ fr s', Q fr s' → FoldEnd Z c l s' ∧ ShareLive s') →
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
              (qS + 0)))))) := by
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt_plan hE hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, fun d he h5 h6 ft share qS Q hSc hQ => ?_⟩
  exact H d he h5 h6 ft share qS Q hSc fun fr s' hq =>
    ⟨(hQ fr s' hq).1, shareOwed_of hS hR O hl hb (hQ fr s' hq).1 (hQ fr s' hq).2⟩

/-- **The same at strings of hash blocks.** -/
theorem share_fallDebt_live_blocks (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (qS : ℝ≥0∞)
          (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' → Iop.prRho {ρ : Iop.Rho (uLT (_root_.Run.ckP .two) [d]) |
          behindT b secondNo s' (drawnT (_root_.Run.ckP .two) [d] ρ) = true} ≤ qS) →
        (∀ fr s', Q fr s' → FoldEnd Z c l s' ∧ ShareLive s') →
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
              ((Fmt.Fld.two.p ^ 3 : ℕ) : ℝ≥0∞) + (qS + 0)))))) := by
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt_plan_blocks hE hS hR O hl
  refine ⟨b, p, X, hb, hp, hX, fun d he h5 h6 ft share qS Q hSc hQ => ?_⟩
  exact H d he h5 h6 ft share qS Q hSc fun fr s' hq =>
    ⟨(hQ fr s' hq).1, shareOwed_of hS hR O hl hb (hQ fr s' hq).1 (hQ fr s' hq).2⟩

end P1K8

#print axioms P1K8.ShareLive
#print axioms P1K8.shareOwed_of
#print axioms P1K8.share_fallDebt_live
#print axioms P1K8.share_fallDebt_live_blocks
