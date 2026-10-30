-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/ShareNeedsOf.lean: THE SMALLNESS TEST's SECOND FALL: `ShareNeeds`
(Johnson/P1K8R/DebtsK8.lean) AT THE BUILT SEGMENT's OWN FOUR NUMBERS, FROM WHAT IS STILL OWED OF THE
STATE IN FRONT OF THE BATCHING; AND `share_fallDebt` WITH ITS FOUR LETTERS GONE. A definition and
lemmas; NONE OF THE LIBRARY's GOALS. Nothing on completeness, soundness or hiding. An assembly: no
new argument.

  `ShareOwed s'`   what is still owed of the state: whatever data and ledger it holds pass
      `planesLive`, `digitsLive`, `readsLive`, `symbolsLive`, and the upper virtual rows of the
      digits' array begin at column 0
  **`shareNeeds_of`**   in the goals' scope, under an opening of the description, at l < 25, X the
      built segment: `FoldEnd Z c l s'` and `ShareOwed s'` give `ShareNeeds` at 3 * X.tl.bzColumns,
      2 * (X.tl.zzBlocks * X.tl.mz), linkedCount X.tl, symCount X.tl
  **`share_fallDebt_plan`**, **`share_fallDebt_plan_blocks`**   `share_fallDebt`,
      `share_fallDebt_blocks` at these four numbers: P must give `FoldEnd` and `ShareOwed`
By: `numbers_at_batch`, `digitsLaid_of` (Johnson/P1K8R/NumbersAtBatch.lean) · `apart_at_batch`,
`planesLaid_at_batch` (ApartAtBatch.lean) · `tiesLaid_at_batch` (TiesAtBatch.lean) ·
`symbolsLaid_at_batch` (SymbolsAtBatch.lean) · reach_of_fold (Johnson/Top/H0/Walk/Reach.lean).
Limits. The number for `secondNo` stays a letter. `RowsAsked Z` stays a premise. `ShareOwed` is
shown of no state here. No number is evaluated.
-/
import Johnson.P1K8R.DebtsK8
import Johnson.P1K8R.NumbersAtBatch
import Johnson.P1K8R.TiesAtBatch
import Johnson.P1K8R.SymbolsAtBatch

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

/-- What is still owed of the state in front of the batching. -/
def ShareOwed (s' : S) : Prop :=
  ∀ tl F', s'.tl? = some tl → s'.fork? = some F' →
    planesLive tl = true ∧ digitsLive tl = true ∧ readsLive tl = true ∧
      symbolsLive tl = true ∧ ∀ b, b < tl.zzBlocks →
        ((F'.trees.getD tl.ix.ZZ {}).rows.getD (tl.zzBlocks + b) {}).L0 = 0

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A₂ : ProofFile.SharedSeat} {B₂ : ProofFile.SecondSeat}

/-- **`ShareNeeds` at the built segment's own numbers.** -/
theorem shareNeeds_of (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A₂ B₂) {l : ℕ} (hl : l < 25)
    {X : LinkH} (e3 : Bs.G₀.built[l]? = some X) {b : Block S Claim}
    (hb : c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b) {s' : S}
    (hf : FoldEnd Z c l s') (hw : ShareOwed s') :
    ShareNeeds Z c l (3 * X.tl.bzColumns) (2 * (X.tl.zzBlocks * X.tl.mz)) (linkedCount X.tl)
      (symCount X.tl) s' := by
  obtain ⟨zp, rs, r, cs, c', hfold⟩ := id hf
  have hr : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (zp, s') :=
    reach_of_fold _ (List.getElem?_eq_some_iff.1 hb).1.le s' rs r cs c' hfold
  obtain ⟨t1, a1, ap, -⟩ := apart_at_batch hS hR O hl hr
  obtain ⟨t2, a2, pl⟩ := planesLaid_at_batch hS hR O hl hr
  obtain ⟨t3, a3, ti⟩ := tiesLaid_at_batch hS hR O hl hr
  obtain ⟨t4, a4, sy⟩ := symbolsLaid_at_batch hS hR O hl hr
  obtain rfl : t1 = t2 := Option.some.inj (a1.symm.trans a2)
  obtain rfl : t1 = t3 := Option.some.inj (a1.symm.trans a3)
  obtain rfl : t1 = t4 := Option.some.inj (a1.symm.trans a4)
  obtain ⟨n1, n2, n3, n4, n5⟩ := numbers_at_batch hS hR O hl e3 hr a1
  refine ⟨hf, fun tl F' ht hF => ?_, fun tl F' ht hF => ?_, fun tl F' ht hF => ?_,
    fun tl F' ht hF => ?_⟩
  all_goals
    obtain rfl : t1 = tl := Option.some.inj (a1.symm.trans ht)
    obtain ⟨w1, w2, w3, w4, w5⟩ := hw t1 F' ht hF
  · exact ⟨by rw [pl, w1]; rfl, by rw [n1]⟩
  · exact ⟨by rw [digitsLaid_of t1 F' ap w5, w2]; rfl, by rw [n2, n3]⟩
  · exact ⟨by rw [ti, w3]; rfl, by rw [n4]⟩
  · exact ⟨by rw [sy, w4]; rfl, by rw [n5]⟩

/-- **The second fall's sentence at the built segment's numbers: at typed challenges.** -/
theorem share_fallDebt_plan (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
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
        (∀ fr s', Q fr s' → FoldEnd Z c l s' ∧ ShareOwed s') →
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
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt hE hS hR O hl
  have e3 : Bs.G₀.built[l]? = some X := by
    rw [← Array.getElem?_toList]
    exact hX
  refine ⟨b, p, X, hb, hp, hX, fun d he h5 h6 ft share qS Q hSc hQ => ?_⟩
  exact H d he h5 h6 ft share _ _ _ _ qS Q hSc fun fr s' hq =>
    shareNeeds_of hS hR O hl e3 hb (hQ fr s' hq).1 (hQ fr s' hq).2

/-- **The same at strings of hash blocks.** -/
theorem share_fallDebt_plan_blocks (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
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
        (∀ fr s', Q fr s' → FoldEnd Z c l s' ∧ ShareOwed s') →
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
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt_blocks hE hS hR O hl
  have e3 : Bs.G₀.built[l]? = some X := by
    rw [← Array.getElem?_toList]
    exact hX
  refine ⟨b, p, X, hb, hp, hX, fun d he h5 h6 ft share qS Q hSc hQ => ?_⟩
  exact H d he h5 h6 ft share _ _ _ _ qS Q hSc fun fr s' hq =>
    shareNeeds_of hS hR O hl e3 hb (hQ fr s' hq).1 (hQ fr s' hq).2

end P1K8

#print axioms P1K8.ShareOwed
#print axioms P1K8.shareNeeds_of
#print axioms P1K8.share_fallDebt_plan
#print axioms P1K8.share_fallDebt_plan_blocks
