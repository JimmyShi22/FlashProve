-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/WithOpeningsExtracts.lean: if whoever opens a key of a scheme A opens it to the extracted index
(`OpensToExtracted`, ZKCP/WithOpenings.lean), then the extractor returns the honest committer's
index, except with probability β tC 0.

`OpensToExtracted.extractionError_coinsFirst`: the scheme `A.coinsFirst bound`
(ZKCP/CoinsFirstArg.lean), whose committer samples one number first, has the extraction error β tC 0
(`HasExtractionError`, ZKCP/Optional.lean), where tC bounds the queries of A's committer. No
condition on `bound` is needed.
Why: the bound holds at each number (`OpensToExtracted.atCoins`), so it holds on average.
`HasExtractionError.coinsFirst` (ZKCP/CoinsFirstArg.lean) carries A's own extraction error and asks
that `bound + 1` be enough.
-/
import ZKCP.AtCoins
import ZKCP.Optional
import ZKCP.WithOpenings

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

namespace ZKCP

variable {lam : ℕ} {I X W IVK ISK Pf : Type}

/-- From the key and the queries of the honest committer that samples one number first, the
extractor returns the committed index, except with probability β tC 0. -/
theorem OpensToExtracted.extractionError_coinsFirst {A : Arg lam I X W IVK ISK Pf}
    {E : Extractor lam I X W IVK Pf} {β : ℕ → ℕ → ℝ≥0∞} (h : OpensToExtracted A E.Ei β)
    (bound : ℕ) {tC : ℕ} (hq : ∀ i, (A.C i).QueryBound tC) :
    HasExtractionError (A.coinsFirst bound) E (β tC 0) := by
  intro i
  show Pr (OComp.sample bound fun coins =>
      (((A.C i).withCoins coins.val).mapO fun key => (key.1, (i, coins))).withTrace)
    (fun _ => {o | E.Ei o.1.1 o.2 ≠ some i}) ≤ β tC 0
  refine Pr_sample_le bound _ _ _ fun coins => ?_
  refine le_trans (le_of_eq ?_) (h.atCoins i coins.val (hq i))
  unfold Pr PrCoins
  refine lintegral_congr fun f => ?_
  show prob ((((A.C i).withCoins coins.val).mapO fun key =>
      (key.1, (i, coins))).withTrace.run f) _
    = prob ((((A.C i).withCoins coins.val).mapO Prod.fst).withTrace.run f) _
  rw [OComp.withTrace_mapO, OComp.withTrace_mapO, OComp.run_mapO, OComp.run_mapO, prob_map,
    prob_map]
  exact congrArg (prob _) (Set.ext fun _ => Iff.rfl)

end ZKCP
