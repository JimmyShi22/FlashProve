-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/OverOneNDerive.lean: the condition `OComp.FactorsBy` under the two transformations that are used
when coins are derived from a seed. A companion to Rom/OverOneN.lean.

Rom/OverOneN.lean: a program factors by a relation ag on answers if at every query node answers in
the relation have the same continuation program (`OComp.FactorsBy ag`). Its Section 5 has the
condition under bind, query, pure, sample. Here it is shown under `OComp.blocks β` (Rom/Blocks.lean:
every uniform sample is made from small ones) and under `OComp.derive σ s j` (Rom/SpecDerive.lean:
every sample is read out of an answer of the auxiliary oracle `σ.o`).

The hypothesis of `FactorsBy.derive` on ag at `σ.o` says that of an answer of the auxiliary oracle
nothing is left out. For `Agree m need` (agreement on the marked hash blocks, Rom/OverOneN.lean) it
holds if all hash blocks of `σ.o` are marked.
-/
import Rom.OverOneN
import Rom.Blocks

set_option autoImplicit false

namespace Rom

variable {S : OSpec} {α : Type} {ag : ∀ o, S.Dom o → S.Rng o → S.Rng o → Prop}

/-- If f v factors by ag for every v, so does `tossN w m f`: m small samples in a row, and what
follows them. -/
theorem factorsBy_tossN (w : ℕ) :
    ∀ (m : ℕ) (f : (Fin m → Fin (w + 1)) → OComp S α),
      (∀ v, (f v).FactorsBy ag) → (OComp.tossN w m f).FactorsBy ag
  | 0, _, h => h _
  | m + 1, f, h => fun r => factorsBy_tossN w m (fun v => f (Fin.cons r v)) fun _ => h _

namespace OComp.FactorsBy

/-- Making every uniform sample from small ones keeps the condition. -/
theorem blocks (β : CoinPlan) {c : OComp S α} : c.FactorsBy ag → (c.blocks β).FactorsBy ag := by
  induction c with
  | pure a => exact fun _ => trivial
  | sample n k ih => exact fun h => factorsBy_tossN β.w (β.m n) _ fun v => ih _ (h _)
  | query o q k ih =>
    exact fun h =>
      ⟨fun r r' hr => congrArg (fun x => OComp.blocks β x) (h.1 r r' hr), fun r => ih r (h.2 r)⟩

/-- Deriving the coins keeps the condition, if answers of the auxiliary oracle that are related by
ag are equal. -/
theorem derive (σ : SeedOracle S) (s : Fin (σ.sd + 1))
    (hσ : ∀ q r r', ag σ.o q r r' → r = r') {c : OComp S α} :
    c.FactorsBy ag → ∀ j, (c.derive σ s j).FactorsBy ag := by
  induction c with
  | pure a => exact fun _ _ => trivial
  | sample n k ih =>
    exact fun h j => ⟨fun r r' hr => by rw [hσ _ r r' hr], fun d => ih _ (h _) (j + 1)⟩
  | query o q k ih =>
    exact fun h j =>
      ⟨fun r r' hr => congrArg (fun x => OComp.derive σ s x j) (h.1 r r' hr),
        fun r => ih r (h.2 r) j⟩

end OComp.FactorsBy

end Rom
