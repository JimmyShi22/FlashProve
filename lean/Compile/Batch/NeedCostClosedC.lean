-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/NeedCostClosedC.lean: how many small samples (a plan, `CoinPlan`, makes each sample
from these) a node and one execution need: upper bounds in the counts in which the library's other
explicit bounds are stated. For every wire record, with or without proof-of-work bits, and every
plan in which a salt is one small sample (hs, hf: `bk.m (2 ^ p.sMT - 1) = 1` for the salt of a leaf,
`bk.m (2 ^ p.sFS - 1) = 1` for the salt of a chain) (words of this library: lean/GLOSSARY.md).
    `nLv_le`          the tree over a component has at most 2^d leaves
    `cChainB_le`      the salted leaves of the trees over prover messages are at most the leaves:
                      cChainB s A W ph n ≤ cTrees s A W n
    `cNode_le`        a node needs: those for the randomness of the encoding, and at most one for
                      each leaf of its tree
    `cProveB_le`      the small samples of one execution with one slot: those of its two coins, one
                      for the salt of its chain, at most one for each leaf
Notation:
  `bk.m n` (`CoinPlan`, Rom/Blocks.lean): the number of small samples for a sample with n + 1
    outcomes; a small sample has `bk.w` + 1 outcomes;
  `sMT`, `sFS`: natural numbers; sMT is the length of the salt of a leaf, sFS that of the salt of
    a chain (Compile/Batch/Verifier.lean);
  `WP.ri`: an `Enum L.EncodingRandomness` (`WireBP`, Iop/BatchWireP.lean): the enumeration of the encoding
    randomness; an `Enum` e (Iop/Wire.lean) has e.n + 1 entries;
  `coin0`, `coin` (fields of `WirePB`, Iop/BatchWireP.lean): enumerations of `H.Coin0`, the
    randomness of the shared part, and of `H.Coin`, the randomness of one slot (`BatchHonestProver`,
    Iop/Batch.lean);
  `nLv has d` (Compile/Batch/SeedStar.lean): the leaves of the tree over a component: 2^d if the
    component has a tree, else none.
Limits: upper bounds. The explicit bound on the queries of the committer with one seed and the cache
over one hash function, if only the marked blocks are queried, is not in this library; its
counterpart for the sum `cCPLW`, `cCPLW_le` of Compile/Batch/OneCallCostClosed.lean, uses `cNode_le`
and `cProveB_le`.
-/
import Compile.Batch.NeedCostPL
import Compile.Batch.NeedCostClosed

set_option autoImplicit false

open Rom Iop

namespace Compile.Batch
namespace Need
open Seed

theorem nLv_le (has : Bool) (d : ℕ) : nLv has d ≤ 2 ^ d := by
  unfold nLv
  cases has
  · exact le_trans (le_of_eq (Nat.zero_mul _)) (Nat.zero_le _)
  · exact le_of_eq (Nat.one_mul _)

theorem cChainB_le {lam K : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (ph : Ph) (n : ℕ),
      cChainB s A W ph n ≤ cTrees s A W n
  | [], _, _, _, _ => Nat.le_refl _
  | r :: s, (a, A), (w, W), ph, n => by
      have hJ : n * nLv w.hasJ w.depthJ ≤ n * 2 ^ w.depthJ := Nat.mul_le_mul_left _ (nLv_le _ _)
      have h0 := nLv_le w.has0 w.depth0
      have i1 := cChainB_le s A W ph.afterLo n
      have i2 := cChainB_le s A W .shr n
      have i3 := cChainB_le s A W ph n
      show cChainB (r :: s) (a, A) (w, W) ph n ≤ n * 2 ^ w.depthJ + 2 ^ w.depth0 + cTrees s A W n
      unfold cChainB
      split <;> omega

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (nb : Tag → ℕ → ℕ) (bk : CoinPlan)

theorem cNode_le (hs : bk.m (2 ^ p.sMT - 1) = 1) :
    cNode W WP p bk.m ≤ bk.m WP.ri.n + 2 ^ W.depth := by
  unfold cNode
  rw [hs, Nat.mul_one]
  exact Nat.add_le_add_left (le_trans (List.length_filter_le _ _) (le_of_eq List.length_range)) _

theorem cProveB_le (hs : bk.m (2 ^ p.sMT - 1) = 1) (hf : bk.m (2 ^ p.sFS - 1) = 1) {K : ℕ}
    {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} {Wt : Type} {H : BatchHonestProver Q Wt}
    (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H) :
    cProveB bk.m p.sMT p.sFS wq wp 1 ≤
      (bk.m wp.coin0.n + bk.m wp.coin.n) + 1 + cTrees Q.loc.shape Q.ann wq.sh 1 := by
  have h := cChainB_le Q.loc.shape Q.ann wq.sh .first 1
  unfold cProveB
  rw [hs, hf, Nat.mul_one, Nat.one_mul]
  omega

end Need
end Compile.Batch
