-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/OneCallCostClosed.lean: explicit upper bounds on the sums `cPUW`, `cCBW`, `cCPLW`
(Compile/Batch/OneCallCostR.lean, Compile/Batch/OneCallCostPL.lean), in the counts in which the
other bounds of the library are stated. For every wire record, every c (what a failed attempt that
is not the last weighs) and every bff (what the attempt weighs with which a search ends), if 1 ≤ bff
i. (Words of this library: lean/GLOSSARY.md.)

  `cSlotW_leG`   cSlotW c bff s A W i ph ≤ trJ + (sumB + c · sMoreJ) + jn 1. `sumB`: the sum of bff
                 over the rounds; `sMoreJ`, `sMore0`: the attempts after the first, at most
                 (Compile/Batch/CountsGr.lean)
  `cSharedW_leG`   cSharedW c bff Ns s A W i ph ≤ tr0 + (sumB + c · sMore0) + jn (Ns − 1) (without
                   the condition on bff)
  `wFSW`   the Fiat-Shamir part of one execution with one slot:
           2 · sumB + c · (sMoreJ + sMore0) + 1. Why the 1: in the joining round a slot queries g
           and its leaf of the request tree: two queries. `cSlotW_leG` covers one of them by the
           Fiat-Shamir query that it counts for the slot in that shared round, where the slot has
           none: for that, 1 ≤ bff i is required. The other is this 1.
  `cProve1W_le`   cProve1W c bff wq ≤ 2 · cTrees .. 1 + wFSW c bff wq
  `cPUW_le`   cPUW W c bf n ≤ 2 · cTrees (Batch) n + ((n + 1) · sumB + c · (n · sMoreJ + sMore0)) +
              (maxBatchSize − 1) + n
  `cCBW_le`   cCBW W p c bf ≤ 2 · xTree W p 0 + wFSW (Test) + (M + 1) · wFSW (Link)
  `cCPLW_le`   if a salt is one small sample (bk.m (2^sMT − 1) = 1, bk.m (2^sFS − 1) = 1):
               cCPLW W WP p bk c bf ≤ 3 · xTree W p 0 + 3 · (M + 1) · 2^depth + (2 M + 3) · uR +
               (wFSW Test + uT) + (M + 1) · (wFSW Link + uL) + (M + 2).
               The letters: M: p.M; depth: W.depth; xTree W p 0: the leaves of all trees of the
               setup; uR, uT, uL: the small samples for the randomness of the encoding, for the two
               coins of Test, of Link.
               Three times (the factors 3): a leaf query, an inner node, a salt derived under the
               seed.
               3 (M + 1) 2^depth and M + 1 of the uR: for the cache the `Node` of each copy is
               derived a second time
  `sumB_succ`   at bff i = nbf i + 1 `sumB` is `sumNb nbf`

Limits. Inequalities between numbers: nothing here bounds the queries of an algorithm (that the sums
bound the weights on every path: Compile/Batch/OneCallCostS.lean, Compile/Batch/OneCallCostPL.lean).
Nothing about time, memory or field operations; nothing about the mean. Upper bounds, worst case
over the oracle: every search at its cap. Coarse: `cSlotW_leG` and `cSharedW_leG`, and all that
rests on them, count for each slot and for the shared part a Fiat-Shamir query in every round.
-/
import Compile.Batch.OneCallCostPL
import Compile.Batch.NeedCostClosedC

set_option autoImplicit false

open Rom Iop

namespace Compile.Batch
namespace OneCall
open Compile.Need (sumNb)
open Compile.Batch.Need (PhK costJ cost0 tr trJ tr0 tr_le tr_sum_le cNode_le cProveB_le)
open Seed

section One
variable {lam K : ℕ} (c : ℕ) (bff : ℕ → ℕ)

/-- the sum of bff over the rounds -/
def sumB : Shape → ℕ → ℕ
  | [], _ => 0
  | _ :: s, i => bff i + sumB s (i + 1)

theorem sumB_succ (nbf : ℕ → ℕ) :
    ∀ (s : Shape) (i : ℕ), sumB (fun i => nbf i + 1) s i = sumNb nbf s i
  | [], _ => rfl
  | _ :: s, i => congrArg (nbf i + 1 + ·) (sumB_succ nbf s (i + 1))

variable {bff}

theorem cSlotW_leG (hb : ∀ i, 1 ≤ bff i) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ) (ph : PhK),
      cSlotW c bff s A W i ph ≤ trJ s A W + (sumB bff s i + c * sMoreJ s A W) + ph.jn 1
  | [], _, _, _, _ => Nat.zero_le _
  | r :: s, (a, A), (w, W), i, ph => by
      show _ ≤ (costJ w + trJ s A W) +
          ((bff i + sumB bff s (i + 1)) + c * (moreOf w.grJ + sMoreJ s A W)) + ph.jn 1
      have hq := hb i
      rw [Nat.mul_add, Nat.mul_comm c (moreOf w.grJ)]
      by_cases hk : a.kind = .lo
      · rw [cSlotW_lo c bff a A w W i hk]
        have h1 := cSlotW_leG hb s A W (i + 1) ph.afterLo
        have h2 := PhK.jn_afterLo 1 ph
        generalize moreOf w.grJ * c = q at *
        omega
      · have hk' : a.kind = .sh := by
          cases h : a.kind with
          | lo => exact absurd h hk
          | sh => rfl
        generalize moreOf w.grJ * c = q at *
        cases ph with
        | loc =>
          rw [cSlotW_join c bff a A w W i hk']
          have h1 : cSlotW c bff s A W (i + 1) .shr ≤
              trJ s A W + (sumB bff s (i + 1) + c * sMoreJ s A W) + 0 :=
            cSlotW_leG hb s A W (i + 1) .shr
          show _ ≤ _ + 1
          omega
        | first =>
          rw [cSlotW_sh c bff a A w W i hk' _ (.inl rfl)]
          have h1 := cSlotW_leG hb s A W (i + 1) .first
          omega
        | shr =>
          rw [cSlotW_sh c bff a A w W i hk' _ (.inr (.inl rfl))]
          have h1 := cSlotW_leG hb s A W (i + 1) .shr
          omega
        | aft =>
          rw [cSlotW_sh c bff a A w W i hk' _ (.inr (.inr rfl))]
          have h1 := cSlotW_leG hb s A W (i + 1) .aft
          omega

theorem cSharedW_leG (Ns : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (i : ℕ) (ph : PhK),
      cSharedW c bff Ns s A W i ph ≤ tr0 s A W + (sumB bff s i + c * sMore0 s A W) + ph.jn (Ns - 1)
  | [], _, _, _, _ => Nat.zero_le _
  | r :: s, (a, A), (w, W), i, ph => by
      show _ ≤ (cost0 w + tr0 s A W) +
          ((bff i + sumB bff s (i + 1)) + c * (moreOf w.gr0 + sMore0 s A W)) + ph.jn (Ns - 1)
      rw [Nat.mul_add, Nat.mul_comm c (moreOf w.gr0)]
      by_cases hk : a.kind = .lo
      · rw [cSharedW_lo c bff Ns a A w W i hk]
        have h1 := cSharedW_leG Ns s A W (i + 1) ph.afterLo
        have h2 := PhK.jn_afterLo (Ns - 1) ph
        omega
      · have hk' : a.kind = .sh := by
          cases h : a.kind with
          | lo => exact absurd h hk
          | sh => rfl
        cases ph with
        | loc =>
          rw [cSharedW_join c bff Ns a A w W i hk']
          have h1 : cSharedW c bff Ns s A W (i + 1) .shr ≤
              tr0 s A W + (sumB bff s (i + 1) + c * sMore0 s A W) + 0 :=
            cSharedW_leG Ns s A W (i + 1) .shr
          show _ ≤ _ + (Ns - 1)
          omega
        | first =>
          rw [cSharedW_none c bff Ns a A w W i hk' _ (.inl rfl)]
          have h1 := cSharedW_leG Ns s A W (i + 1) .first
          omega
        | shr =>
          rw [cSharedW_shr c bff Ns a A w W i hk']
          have h1 : cSharedW c bff Ns s A W (i + 1) .shr ≤
              tr0 s A W + (sumB bff s (i + 1) + c * sMore0 s A W) + 0 :=
            cSharedW_leG Ns s A W (i + 1) .shr
          show _ ≤ _ + 0
          omega
        | aft =>
          rw [cSharedW_none c bff Ns a A w W i hk' _ (.inr rfl)]
          have h1 := cSharedW_leG Ns s A W (i + 1) .aft
          omega

variable (bff)

/-- the Fiat-Shamir part of one execution with one slot -/
def wFSW {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q) : ℕ :=
  2 * sumB bff Q.loc.shape 0 +
    c * (sMoreJ Q.loc.shape Q.ann wq.sh + sMore0 Q.loc.shape Q.ann wq.sh) + 1

variable {bff}

theorem cProve1W_le (hb : ∀ i, 1 ≤ bff i) {Y : Type} {E : ExtSpec}
    {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q) :
    cProve1W c bff wq ≤ 2 * cTrees Q.loc.shape Q.ann wq.sh 1 + wFSW c bff wq := by
  have h1 := cSharedW_leG c (bff := bff) 1 Q.loc.shape Q.ann wq.sh 0 .first
  have h2 := cSlotW_leG c hb Q.loc.shape Q.ann wq.sh 0 .first
  have h3 := tr_sum_le 1 Q.loc.shape Q.ann wq.sh
  have e1 : PhK.first.jn (1 - 1) = 0 := rfl
  have e2 : PhK.first.jn 1 = 1 := rfl
  unfold cProve1W wFSW
  rw [Nat.mul_add]
  omega

end One

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (bk : CoinPlan) (c : ℕ) {bf : Tag → ℕ → ℕ}

/-- The prover with no query for an empty slot, on a batch with n requests. -/
theorem cPUW_le (hb : ∀ t i, 1 ≤ bf t i) (n : ℕ) :
    cPUW W c bf n ≤
      2 * cTrees L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh n +
        ((n + 1) * sumB (bf .onl) L.onlineBatch.loc.shape 0 +
          c * (n * sMoreJ L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh +
              sMore0 L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh)) +
        (L.maxBatchSize - 1) + n := by
  have h1 := cSharedW_leG c (bff := bf .onl) L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh 0 .first
  have h2 :=
    Nat.mul_le_mul_left n (cSlotW_leG c (hb .onl) L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh 0 .first)
  have h3 := tr_sum_le n L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh
  have e1 : PhK.first.jn (L.maxBatchSize - 1) = L.maxBatchSize - 1 := rfl
  have e2 : PhK.first.jn 1 = 1 := rfl
  rw [e1] at h1
  rw [e2, Nat.mul_add, Nat.mul_add, Nat.mul_add, Nat.mul_one] at h2
  have e3 : n * (c * sMoreJ L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh) =
      c * (n * sMoreJ L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh) := by ring
  unfold cPUW
  rw [Nat.add_mul, Nat.one_mul, Nat.mul_add c]
  omega

/-- The committer with fresh coins. -/
theorem cCBW_le (hb : ∀ t i, 1 ≤ bf t i) :
    cCBW W p c bf ≤
      2 * xTree W p 0 + wFSW c (bf .test) W.T + (p.M + 1) * wFSW c (bf .link) W.Lk := by
  have h1 : cProve1W c (bf .test) W.T ≤
      2 * cTrees L.offline.shape _ W.T.sh 1 + wFSW c (bf .test) W.T :=
    cProve1W_le c (hb .test) W.T
  have h2 : cProve1W c (bf .link) W.Lk ≤
      2 * cTrees L.link.shape _ W.Lk.sh 1 + wFSW c (bf .link) W.Lk :=
    cProve1W_le c (hb .link) W.Lk
  have h0 := tr_le W.depth
  have e : xTree W p 0 =
      (p.M + 1 + 1) * 2 ^ W.depth + cTrees L.offline.shape _ W.T.sh 1 +
        (p.M + 1) * cTrees L.link.shape _ W.Lk.sh 1 := by
    show (p.leaves + 1) * 2 ^ W.depth + cTrees L.offline.shape _ W.T.sh 1 +
        p.leaves * cTrees L.link.shape _ W.Lk.sh 1 + 0 * _ = _
    rw [Nat.zero_mul, Nat.add_zero]
    rfl
  unfold cCBW
  rw [e]
  generalize cTrees L.offline.shape _ W.T.sh 1 = aT at *
  generalize cTrees L.link.shape _ W.Lk.sh 1 = aL at *
  generalize cProve1W c (bf .test) W.T = cT at *
  generalize cProve1W c (bf .link) W.Lk = cL at *
  generalize wFSW c (bf .test) W.T = wT at *
  generalize wFSW c (bf .link) W.Lk = wL at *
  generalize tr W.depth = t at *
  generalize 2 ^ W.depth = D at *
  have h3 : (p.M + 1) * (t + cL) ≤ (p.M + 1) * (2 * D + (2 * aL + wL)) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add h0 h2)
  have e3 : (p.M + 1) * (2 * D + (2 * aL + wL)) =
      2 * ((p.M + 1) * D) + 2 * ((p.M + 1) * aL) + (p.M + 1) * wL := by ring
  have e5 : (p.M + 1 + 1) * D = (p.M + 1) * D + D := by ring
  rw [e3] at h3
  rw [e5]
  omega

/-- The committer with one seed and the cache. -/
theorem cCPLW_le (hb : ∀ t i, 1 ≤ bf t i)
    (hs : bk.m (2 ^ p.sMT - 1) = 1) (hf : bk.m (2 ^ p.sFS - 1) = 1) :
    cCPLW W WP p bk c bf ≤
      3 * xTree W p 0 + 3 * ((p.M + 1) * 2 ^ W.depth) + (2 * p.M + 3) * bk.m WP.ri.n +
        (wFSW c (bf .test) W.T + (bk.m WP.T.coin0.n + bk.m WP.T.coin.n)) +
        (p.M + 1) * (wFSW c (bf .link) W.Lk + (bk.m WP.Lk.coin0.n + bk.m WP.Lk.coin.n)) +
        (p.M + 2) := by
  have h1 := cCBW_le W p c hb
  have h2 := cNode_le W WP p bk hs
  have h3 : cProveB bk.m p.sMT p.sFS W.T WP.T 1 ≤
      (bk.m WP.T.coin0.n + bk.m WP.T.coin.n) + 1 + cTrees L.offline.shape _ W.T.sh 1 :=
    cProveB_le p bk hs hf W.T WP.T
  have h4 : cProveB bk.m p.sMT p.sFS W.Lk WP.Lk 1 ≤
      (bk.m WP.Lk.coin0.n + bk.m WP.Lk.coin.n) + 1 + cTrees L.link.shape _ W.Lk.sh 1 :=
    cProveB_le p bk hs hf W.Lk WP.Lk
  have h5 := tr_le W.depth
  have e : xTree W p 0 =
      (p.M + 1 + 1) * 2 ^ W.depth + cTrees L.offline.shape _ W.T.sh 1 +
        (p.M + 1) * cTrees L.link.shape _ W.Lk.sh 1 := by
    show (p.leaves + 1) * 2 ^ W.depth + cTrees L.offline.shape _ W.T.sh 1 +
        p.leaves * cTrees L.link.shape _ W.Lk.sh 1 + 0 * _ = _
    rw [Nat.zero_mul, Nat.add_zero]
    rfl
  unfold cCPLW cCPW off cLeaf
  rw [e] at h1 ⊢
  generalize cCBW W p c bf = cb at *
  generalize cNode W WP p bk.m = cn at *
  generalize cProveB bk.m p.sMT p.sFS W.T WP.T 1 = pT at *
  generalize cProveB bk.m p.sMT p.sFS W.Lk WP.Lk 1 = pL at *
  generalize cTrees L.offline.shape _ W.T.sh 1 = aT at *
  generalize cTrees L.link.shape _ W.Lk.sh 1 = aL at *
  generalize wFSW c (bf .test) W.T = wT at *
  generalize wFSW c (bf .link) W.Lk = wL at *
  generalize bk.m WP.T.coin0.n + bk.m WP.T.coin.n = uT at *
  generalize bk.m WP.Lk.coin0.n + bk.m WP.Lk.coin.n = uL at *
  generalize bk.m WP.ri.n = uR at *
  generalize tr W.depth = t at *
  generalize 2 ^ W.depth = D at *
  obtain ⟨k, hk⟩ : ∃ k, k = p.M + 1 := ⟨_, rfl⟩
  rw [← hk] at h1 ⊢
  have a1 : k * (cn + pL) ≤ k * ((uR + D) + (uL + 1 + aL)) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add h2 h4)
  have a2 : k * (t + cn) ≤ k * (2 * D + (uR + D)) := Nat.mul_le_mul_left _ (Nat.add_le_add h5 h2)
  have b1 : k * ((uR + D) + (uL + 1 + aL)) = k * uR + k * D + k * uL + k + k * aL := by ring
  have b2 : k * (2 * D + (uR + D)) = 3 * (k * D) + k * uR := by ring
  have b3 : (k + 1) * D = k * D + D := by ring
  have b4 : k * (wL + uL) = k * wL + k * uL := by ring
  have b5 : (2 * p.M + 3) * uR = 2 * (k * uR) + uR := by rw [hk]; ring
  rw [b1] at a1
  rw [b2] at a2
  rw [b3] at h1 ⊢
  rw [b4, b5]
  omega

end OneCall
end Compile.Batch
