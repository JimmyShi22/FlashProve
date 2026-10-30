-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/SeedRootCost.lean: the number of queries of an algorithm whose samples are made from small
samples, or derived from a seed.

  `Rom.OComp.QueryBound.tossN`, `QueryBound.blocks`
      Making samples from small ones adds no query.
  `Rom.OComp.QueryBound.derive`
      Deriving the coins of an algorithm with exactly n uniform samples on every path adds at most
      n queries.

Notation: `c.QueryBound t`: "at most t queries in all, on every path; a repeated query counts again"
(Rom/OComp.lean); `bk`: a `CoinPlan` (Rom/Blocks.lean): "how a uniform sample is made from small
ones"; `bk.w`: "a small sample has w + 1 outcomes"; `bk.m`: "the number of small samples for a
sample with n + 1 outcomes"; `σ`: a `SeedOracle S` (Rom/SpecDerive.lean): "An auxiliary oracle, used
as a source of coins"; `s`: an element of Fin (σ.sd + 1); "seeds are the elements of Fin (sd + 1)"
(there); `j`: a natural number; "j is the number of samples so far" (`OComp.derive`, there).

Limits: this file does not bound the queries of any committer. These are bounds on numbers of
queries. Nothing is said on time or memory.
-/
import Compile.SeedRoot
import Compile.Extraction

noncomputable section

open Rom Iop

namespace Rom
namespace OComp

variable {S : OSpec} {α : Type}

theorem QueryBound.tossN (w : ℕ) {t : ℕ} :
    ∀ (m : ℕ) (f : (Fin m → Fin (w + 1)) → OComp S α),
      (∀ v, (f v).QueryBound t) → (OComp.tossN w m f).QueryBound t
  | 0, _, h => h _
  | m + 1, f, h => fun r => QueryBound.tossN w m (fun v => f (Fin.cons r v)) fun _ => h _

/-- Making samples from small ones adds no query. -/
theorem QueryBound.blocks (bk : CoinPlan) :
    ∀ (c : OComp S α) (t : ℕ), c.QueryBound t → (c.blocks bk).QueryBound t
  | .pure _, _, _ => trivial
  | .query _ _ _, 0, h => h.elim
  | .query _ _ k, t + 1, h => fun r => QueryBound.blocks bk (k r) t (h r)
  | .sample n k, t, h => QueryBound.tossN bk.w (bk.m n) _ fun v => QueryBound.blocks bk (k (bk.φ n v)) t (h _)

/-- Deriving the coins of an algorithm with exactly n uniform samples on every path adds at most n
queries. -/
theorem QueryBound.derive (σ : SeedOracle S) (s : Fin (σ.sd + 1)) {n : ℕ}
    {c : OComp S α} (hc : Compile.Seed.Tosses n c) :
    ∀ (t j : ℕ), c.QueryBound t → (c.derive σ s j).QueryBound (t + n) := by
  induction hc with
  | pure a => exact fun _ _ _ => trivial
  | query o q _ ih =>
    intro t j h
    cases t with
    | zero => exact h.elim
    | succ t =>
      rename_i n k _
      show (OComp.query o q fun r => (k r).derive σ s j).QueryBound (t + 1 + n)
      rw [show t + 1 + n = (t + n) + 1 by omega]
      exact fun r => ih r t j (h r)
  | sample m _ ih =>
    intro t j h
    rename_i n k _
    show (OComp.query σ.o (σ.pt s j) fun d => (k (σ.ψ m d)).derive σ s (j + 1)).QueryBound
      (t + (n + 1))
    exact fun d => ih _ t (j + 1) (h _)

end OComp
end Rom
