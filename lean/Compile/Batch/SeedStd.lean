-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedStd.lean: the standard way to use the auxiliary oracle as a source of coins, for
the oracles of the compiled scheme; and the bias along a path of its committer C. (Words of this
library: lean/GLOSSARY.md.)

The oracle `OracleName.other` of Compile/Batch/Oracles.lean takes a list of bits and answers with λ bits.
What does not depend on the family of oracles is taken from Compile/SeedStd.lean and not repeated:
`ptStd`, `pt_inj` (the query for a seed and a counter), `digNum` (λ bits as a number), `blocksStd`
(a small sample has 2^λ outcomes; a sample with exactly 2^λ outcomes is one small sample; any other
sample with n + 1 outcomes is made from ⌊⌈log₂ (n + 1)⌉ / λ⌋ + 2 small ones), `muStd` (the weight 0
for a sample with exactly 2^λ outcomes, 1 for every other), `bias_blocksStd_mu` (for λ > 0 a sample
made from small ones has a bias of at most muStd · 2^-λ / 4).

  `sigmaStdB`   seeds are the numbers below 2^λ; the query for the seed s and the counter j is the λ
                bits of s followed by the binary digits of j; an answer, read as a number and
                reduced modulo n + 1, is a sample with n + 1 outcomes
  `bias_sigmaStdB`   a sample with 2^λ outcomes has no bias
  `nWideB`   the number of those samples of C that do not have exactly 2^λ outcomes
  `nWideB_le`   if the salts of leaves and of chains have λ bits, nWideB ≤ 3 (M + 2): each of the M
                + 2 `Node`s has one such sample at most (the randomness of its encoding), each of
                the M + 2 proof strings of Test and Link two (the shared coins and the coins of its
                one slot); no salt counts

Limits. The file has no theorem on a scheme (Compile/Batch/SeedMain.lean). `nWideB_le` is an upper
bound, not the number. `blocksStd` wastes answers on samples other than salts: a sample with two
outcomes takes two answers of λ bits. The implementation takes its coins from a stream cipher under
the seed and not from a random oracle; this file inherits that difference from
Compile/Batch/SeedStar.lean and removes none.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Compile.Batch.SeedShape
import Compile.SeedStd

noncomputable section

open Rom Iop Prob
open scoped ENNReal

namespace Compile.Batch
namespace Seed

open Compile.Seed (ptStd pt_inj digNum two_pow_sub_add blocksStd muStd bias_blocksStd_mu Wt)

variable {I X : Type}

section Sigma
variable (lam K : ℕ) (L : BatchProtocol I X)

/-- The auxiliary oracle of the compiled scheme as a source of coins. -/
def sigmaStdB : SeedOracle (spec lam K L) where
  o := OracleName.other
  sd := 2 ^ lam - 1
  pt := ptStd lam
  inj := pt_inj lam
  ψ := fun n (d : Dig lam) => ⟨(digNum lam d).val % (n + 1), Nat.mod_lt _ n.succ_pos⟩

theorem sigmaStdB_o : (sigmaStdB lam K L).o = OracleName.other := rfl

/-- there are 2^λ seeds -/
theorem sigmaStdB_sd : (sigmaStdB lam K L).sd + 1 = 2 ^ lam := two_pow_sub_add lam

/-- A sample with 2^λ outcomes has no bias. -/
theorem bias_sigmaStdB : (sigmaStdB lam K L).bias (2 ^ lam - 1) = 0 := by
  have e : (fun d : Dig lam =>
      (⟨(digNum lam d).val % (2 ^ lam - 1 + 1),
        Nat.mod_lt _ (2 ^ lam - 1).succ_pos⟩ : Fin (2 ^ lam - 1 + 1)))
      = ⇑((digNum lam).trans (finCongr (two_pow_sub_add lam).symm)) := funext fun d => Fin.ext (by
    show (digNum lam d).val % (2 ^ lam - 1 + 1) = (digNum lam d).val
    exact Nat.mod_eq_of_lt (lt_of_lt_of_eq (digNum lam d).2 (two_pow_sub_add lam).symm))
  show tv ((unif (Dig lam)).map fun d : Dig lam =>
        (⟨(digNum lam d).val % (2 ^ lam - 1 + 1),
          Nat.mod_lt _ (2 ^ lam - 1).succ_pos⟩ : Fin (2 ^ lam - 1 + 1)))
      (unif (Fin (2 ^ lam - 1 + 1))) = 0
  rw [e, map_unif_equiv, tv_self]

/-- `bias_sigmaStdB` in the form that `Spec.seedMainB` (Compile/Batch/SeedStar.lean) requires: a
small sample of the standard decomposition is derived without bias -/
theorem bias_sigmaStdB_w : (sigmaStdB lam K L).bias (blocksStd lam).w = 0 := bias_sigmaStdB lam K L

end Sigma

variable {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

/-- The bias along a path of C: if a sample with k + 1 outcomes has a bias of at most μ k · bm, it
is at most off .. μ (M + 1) (the total weight of C's samples) · bm. -/
theorem pathBiasB_C_le (bk : CoinPlan) {μ : ℕ → ℕ} {bm : ℝ≥0∞}
    (hbm : ∀ k, bk.bias k ≤ μ k * bm) (i : I) :
    (C W WP p i).pathBiasB bk ≤ off W WP p μ (p.M + 1) * bm :=
  (wt_C W WP p μ i).pathBiasB_le bk hbm

/-- the number of those samples of C that do not have exactly 2^λ outcomes -/
def nWideB : ℕ := off W WP p (muStd lam) (p.M + 1)

/-- For λ > 0: the bias along a path of C with `blocksStd` is at most nWideB · 2^-λ / 4. -/
theorem pathBiasB_C_std (hl : 0 < lam) (i : I) :
    (C W WP p i).pathBiasB (blocksStd lam) ≤ nWideB W WP p * (((4 * 2 ^ lam : ℕ) : ℝ≥0∞))⁻¹ :=
  pathBiasB_C_le W WP p (blocksStd lam) (bias_blocksStd_mu lam hl) i

theorem muStd_salt (lam : ℕ) : muStd lam (2 ^ lam - 1) = 0 := if_pos (two_pow_sub_add lam)

theorem muStd_le_one (lam k : ℕ) : muStd lam k ≤ 1 := by
  unfold muStd
  split_ifs <;> omega

/-- if p.sMT = λ: a `Node` has at most one sample without exactly 2^λ outcomes -/
theorem cNode_muStd_le (h : p.sMT = lam) : cNode W WP p (muStd lam) ≤ 1 := by
  unfold cNode
  rw [h, muStd_salt, Nat.mul_zero, Nat.add_zero]
  exact muStd_le_one _ _

/-- with salts of λ bits: a compiled proof with n slots has at most n + 1 such samples -/
theorem cProveB_muStd_le {K : ℕ} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {Wt' : Type}
    {H : BatchHonestProver Q Wt'} (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H) (n : ℕ) :
    cProveB (muStd lam) lam lam wq wp n ≤ n + 1 := by
  unfold cProveB
  rw [muStd_salt, Nat.mul_zero, Nat.add_zero, Nat.add_zero]
  have h0 := muStd_le_one lam wp.coin0.n
  have h1 : n * muStd lam wp.coin.n ≤ n * 1 := Nat.mul_le_mul_left n (muStd_le_one lam wp.coin.n)
  omega

/-- If all salts have λ bits, at most 3 (M + 2) samples of C do not have exactly 2^λ outcomes. -/
theorem nWideB_le (h1 : p.sMT = lam) (h2 : p.sFS = lam) : nWideB W WP p ≤ 3 * (p.M + 2) := by
  unfold nWideB off cLeaf
  have hn := cNode_muStd_le W WP p h1
  have hT := cProveB_muStd_le W.T WP.T 1
  have hL := cProveB_muStd_le W.Lk WP.Lk 1
  rw [h1, h2]
  have hm : (p.M + 1) * (cNode W WP p (muStd lam) + cProveB (muStd lam) lam lam W.Lk WP.Lk 1) ≤
      (p.M + 1) * 3 :=
    Nat.mul_le_mul_left _ (by omega)
  omega

end Seed
end Compile.Batch
