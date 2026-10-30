-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ZKCP/AtCoins.lean: a scheme with its committer run at a given number.

`Arg.atCoins A coins` is the scheme A (ZKCP/Defs.lean) whose committer reads its random choices off
the number `coins` and samples nothing (`OComp.withCoins`, ZKCP/CoinsFirst.lean).
  `wrongExp_coinsFirst`         the experiment with the honest committer and any prover (`wrongExp`,
                                ZKCP/HonestKey.lean) for `A.coinsFirst bound` is: sample a number,
                                then that experiment for A at that number
  `Pr_wrongExp_coinsFirst_le`   so a bound that holds for A at every number holds for
                                `A.coinsFirst bound`, for a prover that is handed the number
No condition on `bound` is needed. Whether a scheme has such a bound at every number is a question
about that scheme.
Words: a hash function is an `Oracle`; the verifier's and the prover's key are `IVK` and `ISK`.
-/
import ZKCP.CoinsFirstArg

set_option autoImplicit false

open scoped ENNReal

namespace ZKCP

variable {lam : ℕ} {I X W IVK ISK Pf : Type}

/-- The scheme A with its committer run at the given number (`OComp.withCoins`): the committer
samples nothing. The prover and the verifier are A's. -/
def Arg.atCoins (A : Arg lam I X W IVK ISK Pf) (coins : ℕ) : Arg lam I X W IVK ISK Pf where
  C := fun i => (A.C i).withCoins coins
  P := A.P
  V := A.V

/-- If each continuation of a sample gives an event probability at most β, so does the sample. -/
theorem Pr_sample_le {α : Type} (n : ℕ) (k : Fin (n + 1) → OComp lam α) (T : Set α) (β : ℝ≥0∞)
    (h : ∀ r, Pr (k r) (fun _ => T) ≤ β) : Pr (.sample n k) (fun _ => T) ≤ β := by
  rw [Pr_eq_PrFrom, PrFrom_sample]
  exact le_trans (expect_mono _ fun r => h r) (le_of_eq (expect_const _ _))

/-- `wrongExp` for `A.coinsFirst bound` is: sample a number, then `wrongExp` for A at that number,
with the prover handed the verifier's key, the index and the number. -/
theorem wrongExp_coinsFirst (A : Arg lam I X W IVK ISK Pf) (bound : ℕ) (i : I)
    (Pt : IVK × (I × Fin (bound + 1)) → OComp lam (X × Pf)) :
    wrongExp (A.coinsFirst bound) i Pt = .sample bound fun coins =>
      wrongExp (A.atCoins coins.val) i fun key => Pt (key.1, (i, coins)) := by
  unfold wrongExp
  show OComp.sample bound (fun coins =>
      (((A.C i).withCoins coins.val).mapO fun key => (key.1, (i, coins))).bind fun k =>
        (Pt k).bind fun o => (A.V k.1 o.1 o.2).bind fun b => .pure (b, o.1)) = _
  exact congrArg _ (funext fun coins => OComp.mapO_bind _ _ _)

/-- A bound on an event of `wrongExp` that holds for A at every number from 0 to `bound` holds for
`A.coinsFirst bound`. The prover is handed both keys of that scheme: the verifier's key, the index
and the sampled number. -/
theorem Pr_wrongExp_coinsFirst_le (A : Arg lam I X W IVK ISK Pf) (bound : ℕ) (i : I)
    (Pt : IVK × (I × Fin (bound + 1)) → OComp lam (X × Pf)) (T : Set (Bool × X)) (β : ℝ≥0∞)
    (h : ∀ coins : Fin (bound + 1),
      Pr (wrongExp (A.atCoins coins.val) i fun key => Pt (key.1, (i, coins))) (fun _ => T) ≤ β) :
    Pr (wrongExp (A.coinsFirst bound) i Pt) (fun _ => T) ≤ β := by
  rw [wrongExp_coinsFirst]
  exact Pr_sample_le _ _ _ _ h

end ZKCP
