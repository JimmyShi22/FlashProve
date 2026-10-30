-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/BehindFew.lean: THE SMALLNESS TEST's SECOND FALL: THE SENTENCE OF
`share_fallDebt_last` (Johnson/P1K8R/BehindLast.lean) WITH ONE MORE PAYMENT LAID IN: WHAT IT ASKED
OF A FEED-FORWARD SEGMENT's OWN RUNS (`RunAsks`, the field layers of `StillAtZ`; twelve segments) IS
PROVED BY THAT KIND's AUTHORS AT EVERY STATE THAT `WrapEnd` ADMITS. A structure and lemmas; NONE OF
THE LIBRARY's GOALS. A joining. Nothing on completeness, soundness or hiding.

  `StillAtY Bs l s`   two fields: heard, five
  **`stillAtZ_of_y`**   `runAsks_at_wrapped`
      (Johnson/Desc/ProofFile/Honest/K4/Law/RunsAtBatch.lean)
  **`share_fallDebt_few`**, **`share_fallDebt_few_blocks`**   `share_fallDebt_last`,
      `share_fallDebt_last_blocks` by one call each
Limits. THE OBLIGATION MOVES; IT IS NOT MET: `WrapEnd`, `ShareLive`, `LiveFore`, `StillAtY` and
`RowsAsked Z` are premises; none is shown of any state or plan here. Like every file of this road it
takes a cone under Johnson/Goal/ (through the sealed Johnson/IMR/ seats; the feed-forward layers'
authors' file, which is called here, reaches modules there too). No number is evaluated.
Terms: lean/GLOSSARY.md.
-/
import Johnson.P1K8R.BehindLast
import Johnson.Desc.ProofFile.Honest.K4.Law.RunsAtBatch

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

/-- **What is still asked of the state in front of the batching of the segment l**: `StillAtZ`
(Johnson/P1K8R/BehindLast.lean) without its field layers. -/
structure StillAtY (Bs : ProofFile.PureBase) (l : ℕ) (s : S) : Prop where
  heard : ∀ tl, s.tl? = some tl → ∀ g nbW W, tl.heard = some g → tl.wants = some (nbW, W) →
    ∀ w ∈ W, (g.zk.getD w.call #[]).size = (tl.zOf w.call).call.n ∧
      g.e.getD w.call zeroE = callWeightAgain g w.call
  five : ∀ (g : ℕ) (Ap : Attention.Plan), l = 2 * g + 1 → Bs.G₀.W.A[g]? = some Ap →
    ∃ hd, s.heard5? = some hd ∧ K5Law.HeardPlain hd

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **THE FIELD layers IS PAID AT EVERY STATE THAT `WrapEnd` ADMITS**: that kind's authors'
`runAsks_at_wrapped` (Johnson/Desc/ProofFile/Honest/K4/Law/RunsAtBatch.lean), bare. -/
theorem stillAtZ_of_y (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} {s : S} (w : WrapEnd Z c l s) (Y : StillAtY Bs l s) : StillAtZ Z Bs l s :=
  ⟨Y.heard, ProofFile.Honest.K4.runAsks_at_wrapped hS hR O hOk w, Y.five⟩

/-- **THE SECOND FALL's SENTENCE WITH THAT PAYMENT LAID IN: at typed challenges.** The sentence and
the number of `share_fallDebt_last`; of the letter Q: `StillAtY` for `StillAtZ`. -/
theorem share_fallDebt_few (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' →
          WrapEnd Z c l s' ∧ ShareLive s' ∧ LiveFore s' ∧ StillAtY Bs l s') →
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
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt_last hE hS hR O hOk hl
  refine ⟨b, p, X, hb, hp, hX, fun d he h5 h6 ft share Q hQ => ?_⟩
  exact H d he h5 h6 ft share Q fun fr s' hq =>
    ⟨(hQ fr s' hq).1, (hQ fr s' hq).2.1, (hQ fr s' hq).2.2.1,
      stillAtZ_of_y hS hR O hOk (hQ fr s' hq).1 (hQ fr s' hq).2.2.2⟩

/-- **The same at strings of hash blocks.** -/
theorem share_fallDebt_few_blocks (hE : RowsAsked Z) (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) :
    ∃ (b : Block S Claim) (p : K9.Where) (X : LinkH),
      c.blocksInOrder[14 * l + (if l = 24 then 11 else 9)]? = some b ∧ IM.k9At Z l = some p ∧
      Bs.G₀.built.toList[l]? = some X ∧
      ∀ (d : RDT), d.entry = K9.entry p → d.kind ≠ .seeds → d.kind ≠ .sealed →
        ∀ (ft : ℕ) (share : Odds) (Q : List Fmt.Drawn → S → Prop),
        (∀ fr s', Q fr s' →
          WrapEnd Z c l s' ∧ ShareLive s' ∧ LiveFore s' ∧ StillAtY Bs l s') →
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
  obtain ⟨b, p, X, hb, hp, hX, H⟩ := share_fallDebt_last_blocks hE hS hR O hOk hl
  refine ⟨b, p, X, hb, hp, hX, fun d he h5 h6 ft share Q hQ => ?_⟩
  exact H d he h5 h6 ft share Q fun fr s' hq =>
    ⟨(hQ fr s' hq).1, (hQ fr s' hq).2.1, (hQ fr s' hq).2.2.1,
      stillAtZ_of_y hS hR O hOk (hQ fr s' hq).1 (hQ fr s' hq).2.2.2⟩

end

end P1K8

#print axioms P1K8.StillAtY
#print axioms P1K8.stillAtZ_of_y
#print axioms P1K8.share_fallDebt_few
#print axioms P1K8.share_fallDebt_few_blocks
