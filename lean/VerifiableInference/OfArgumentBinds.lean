-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/OfArgumentBinds.lean: the commitment of the argument system of a scheme
(`ArgumentSystem.ofArgument`, VerifiableInference/OfArgument.lean) binds to the extractor's weights
(`BindsWith`, VerifiableInference/MoreStatements.lean), if whoever opens a verifier's key of the
scheme opens it to the extracted index (`ZKCP.OpensToExtracted`, ZKCP/WithOpenings.lean).

`bindsWith_ofArgument`: let `commit`, at an index and a number, be the verifier's key that the
committer of a scheme A₁ returns at that index and number (`ZKCP.Arg.commitAt`). A₁ may differ from
the scheme A of the argument system in its instances, witnesses, prover's keys and proofs. The bound
ε is any function of the sum of the two numbers of queries that is at least the scheme's bound β.
Both statements are the same game, except that the scheme's lets the opener name every natural
number and the argument system's only those up to `bound`: the scheme's is the stronger. The proof
compares them under each hash function.
-/
import VerifiableInference.Binds
import VerifiableInference.OfArgument
import ZKCP.WithOpenings

set_option autoImplicit false

open scoped ENNReal
open MeasureTheory

namespace VerifiableInference

open RandomizedAlgorithm

variable {I Pf : Type} {bound : ℕ}
  (A : ZKCP.Arg 256 I (List Token × List Token) Unit (ZKCP.Digest 256) (I × Fin (bound + 1)) Pf)
  (commit : I → Fin (bound + 1) → ZKCP.OComp 256 (ZKCP.Digest 256))
  (nextToken : I → List Token → Option Token)

/-- The commitment binds to the weights that `Ei` gives, if whoever opens a verifier's key of A₁
opens it to the index that `Ei` gives, and `commit` is the verifier's key of A₁ at an index and a
number. -/
theorem bindsWith_ofArgument {X₁ W₁ ISK₁ Pf₁ : Type}
    (A₁ : ZKCP.Arg 256 I X₁ W₁ (ZKCP.Digest 256) ISK₁ Pf₁)
    (hcommit : ∀ i coins, commit i coins = A₁.commitAt i coins.val)
    (Ei : Commitment → QueryLog → Option I) (β : ℕ → ℕ → ℝ≥0∞) (ε : ℕ → ℝ≥0∞)
    (h : ZKCP.OpensToExtracted A₁ Ei β) (hε : ∀ tC tO, β tC tO ≤ ε (tC + tO)) :
    BindsWith (ArgumentSystem.ofArgument A commit nextToken) Ei ε := by
  intro committerQueries proverQueries State committer committerBound opener openerBound
  have key := h committerQueries proverQueries State committer.toUpload
    (fun state => (opener state).toUpload.mapO fun y => (y.1, y.2.val))
    ((queryBound_toUpload committer committerQueries).2 committerBound)
    (fun state => ZKCP.OComp.QueryBound.mapO _ _ _
      ((queryBound_toUpload (opener state) proverQueries).2 (openerBound state)))
  refine le_trans ?_ (le_trans key (hε _ _))
  unfold Prob ZKCP.Pr ZKCP.PrCoins ZKCP.openingExp
  refine lintegral_mono fun hash => ?_
  show ZKCP.prob ((committer.withQueryLog.bind fun c => (opener c.1.2).bind fun y =>
        (deterministicOf (commit y.1 y.2)).toRandomized.bind fun recomputed =>
          RandomizedAlgorithm.done (Ei c.1.1 c.2, c.1.1, y.1, recomputed)).run hash) _
    ≤ ZKCP.prob ((committer.toUpload.withTrace.bind fun c =>
        ((opener c.1.2).toUpload.mapO fun y => (y.1, y.2.val)).bind fun o =>
          (A₁.commitAt o.1 o.2).bind fun key =>
            ZKCP.OComp.pure (Ei c.1.1 c.2, c.1.1, o.1, key)).run hash) _
  rw [run_bind, ZKCP.run_bind, run_toUpload_withTrace, ZKCP.prob_bind, ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun c => ?_
  rw [run_bind, ZKCP.OComp.mapO_bind, ZKCP.run_bind, run_toUpload, ZKCP.prob_bind,
    ZKCP.prob_bind]
  refine ZKCP.expect_mono _ fun y => ?_
  obtain ⟨value, hvalue⟩ :=
    ZKCP.OComp.DrawsNoCoin.run hash _ (A₁.drawsNoCoin_commitAt y.1 y.2.val)
  rw [run_bind, run_deterministicOf hash _ value (by rw [hcommit]; exact hvalue), PMF.pure_bind,
    ZKCP.run_bind, hvalue, PMF.pure_bind]
  show ZKCP.prob (PMF.pure _) _ ≤ ZKCP.prob (PMF.pure _) _
  rw [ZKCP.prob_pure, ZKCP.prob_pure]
  exact ind_le fun hb => hb

end VerifiableInference

#print axioms VerifiableInference.bindsWith_ofArgument
