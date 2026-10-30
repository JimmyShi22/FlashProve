-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/SoundAsIOPSum.lean: from "the prover has lost at the start" to a probability. Proofs of three
statements of Hiop/SoundAsIOP.lean.

  `probability_of_doomed`: a prover that has lost at the start (`Doomed`) reaches a transcript that
    is not bad for it with probability at most the sum of the rounds' errors, each as a share of its
    round's challenges and multiplied by the number of challenges that are cleared to one; over
    uniform challenges, cleared round by round. For every list of rounds, every deterministic
    strategy and every clearing.
  `sumOfProbabilities_le`: a sum is at most (number of rounds) times a bound on every error.
  `wholeRunSound_probability`: the first, at the whole run.

Limits. Where nothing is cleared the measure is the uniform one on ALL challenges. At a protocol whose
verifier rejects unless certain bits of its challenges (proof of work) are 0, every prover, the honest
one too, is accepted with a tiny probability under that measure, and the plain sum is then true for
that reason alone. What speaks there: the round-by-round statement itself, or the sum at the clearing
"set the bits of work to 0". No clearing of any protocol is written here.
-/
import Hiop.SoundAsIOP
import Iop.Compose
import Prob.Bias

set_option autoImplicit false

open scoped ENNReal

namespace Iop
open Prob

theorem probability_of_doomed : Spec.probability_of_doomed
  | [], _, _, _, _, _, _, _, h => by
      refine le_of_eq_of_le (pr_eq_zero_of_forall_not_mem _ fun ρ _ hρ => ?_) (_root_.zero_le _)
      exact absurd h hρ
  | r :: s, (e, ε), bad, β, (m, next), (k, K), (toOne, M), hk, h => by
      have hu : unif (Rho (r :: s)) = Prob.prod (unif r.Chal) (unif (Rho s)) := unif_prod
      have hcnt : cnt (fun c : r.Chal => ¬ Doomed s ε (fun τ => bad (m, k c, τ))) ≤ toOne * e :=
        ((cnt_comp_le k hk.1 fun c' => ¬ Doomed s ε (fun τ => bad (m, c', τ))).trans
          (Nat.mul_le_mul_right _ (h m))).trans (le_of_eq (Nat.mul_comm _ _))
      rw [hu]
      unfold Prob.prod
      refine le_trans (pr_bind_le_add _ _ _ {c | ¬ Doomed s ε (fun τ => bad (m, k c, τ))}
        (ε := Err.sumOfProbabilities (Err.timesByRound M ε)) fun c _ hc => ?_)
        (add_le_add (pr_unif_le_of_cnt_le hcnt) le_rfl)
      exact le_of_eq_of_le (pr_map _ _ _)
        (probability_of_doomed s ε (fun τ => bad (m, k c, τ)) β (next (k c)) K M hk.2 (not_not.1 hc))

theorem sumOfProbabilities_le : Spec.sumOfProbabilities_le
  | [], _, _, _ => _root_.zero_le _
  | r :: s, (e, ε), bound, h => by
      have h1 : (e : ℝ≥0∞) / (Fintype.card r.Chal : ℝ≥0∞) ≤ bound :=
        (ENNReal.div_le_iff (card_ne_zero' r.Chal) (card_ne_top' r.Chal)).2 h.1
      have h2 := sumOfProbabilities_le s ε bound h.2
      calc Err.sumOfProbabilities (s := r :: s) (e, ε)
          = (e : ℝ≥0∞) / (Fintype.card r.Chal : ℝ≥0∞) + Err.sumOfProbabilities ε := rfl
        _ ≤ bound + (s.length : ℝ≥0∞) * bound := add_le_add h1 h2
        _ = ((r :: s).length : ℝ≥0∞) * bound := by
            rw [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]

theorem wholeRunSound_probability : Spec.wholeRunSound_probability :=
  fun _ _ L _ errors fill β prover clearing toOne hk h =>
    probability_of_doomed (L.wholeRunShape fill) (errors.wholeRun fill) _ β prover clearing toOne hk h

end Iop

#print axioms Iop.probability_of_doomed
#print axioms Iop.sumOfProbabilities_le
#print axioms Iop.wholeRunSound_probability
