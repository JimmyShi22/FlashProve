-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CutQueriesSum.lean: bounds on the queries to the one hash function f of the committer
and the prover after the four steps (Compile/Batch/CutQueries.lean), on every path (words of this
library: lean/GLOSSARY.md).

The count of Compile/Batch/OneCallCostW.lean and Compile/Batch/OneCallCostPL.lean, in which a failed
attempt that is not the last costs one call, is generic in what an attempt weighs (`TryW`); here it
is taken at the weight `wF` of Compile/Batch/CutQueries.lean.

  `bfF nb`  What a Fiat-Shamir query of round i weighs at most: 3 + (nb t i − 1): the first block,
            the state (two calls), the expansion queries.
  `tryW_wF`  `wF` meets `TryW`: a failed attempt that is not the last weighs at most 1, any
             Fiat-Shamir query at most `bfF`. Hypotheses: `Test0 W`, 2 ≤ W.K, nb t i < W.K, and a
             query encoding m of the typed family with `Need.Std`. Any such m will do: m is not in
             the scheme, and serves only the count, which is stated against the adaptive rule's
             number `numA m ..`; one exists (`Need.std_implOf`).
  `costC_wF`, `costP_wF`  Under these and further hypotheses, on every path the weights `wF` of
                          committer and prover of prunedK W p (argPL ..) add up to at most cCPLW W
                          WP p bk 1 (bfF nb), cPLW W WP p bk 1 (bfF nb) ℓ nE n
                          (Compile/Batch/OneCallCostPL.lean), for n requests.
  `queryBound_C_CSO`, `queryBound_P_CSO`  Under the same hypotheses, these bound their queries to f
                                          after the four steps, at the query encoding `implCS`.
  `cPLW_bfF_le`, `cCPLW_bfF_le`  cPLW .. 1 (bfF nb) ℓ nE n ≤ cPLA W WP p nb bk ℓ nE n + 2 (n + 1) ·
                                 rounds of Batch; cCPLW .. 1 (bfF nb) ≤ cCPLA W WP p nb bk + 4
                                 (rounds of Test + (M + 1) · rounds of Link).

Worst case over the oracle: every search at its maximal length; an attempt that fails and is not the
last costs 1. Compared with `cCPLA`, `cPLA` (Compile/Batch/SpecOneCallL.lean: an adaptive rule; bf =
nb t i + 1): one call more for each other Fiat-Shamir query (two in a round with nb t i = 0): the
state has two halves.

Notation: `WP`: a `WireBP L` (Iop/BatchWireP.lean): the prover's data for the three protocols, and
the enumeration of the encoding randomness; `p`: a `Params` (Compile/Star.lean), with the fields
sMT, sFS, M, s1; the number of copies is `p.M` + 1; `cCPLW W WP p bk ca bf`,
`cPLW W WP p bk ca bf ℓ nE n` (Compile/Batch/OneCallCostPL.lean): natural numbers: the sums for the
committer that also computes the cache, and for the lazy prover, a batch with n requests; `ca`: a
natural number; `bf`: a map `Tag → ℕ → ℕ`; in `TryW W nb m w ca bf`
(Compile/Batch/OneCallCostW.lean, where ca is called a): ca: what a failed attempt that is not the
last weighs at most; bf t i: what any Fiat-Shamir query of round i of protocol t weighs at most
(with proof-of-work bits: if the table nb marks a block there); `cCPLA`, `cPLA`
(Compile/Batch/SpecOneCallL.lean): the same two sums at the rule's own weight (ca = 1, bf t i = nb t
i + 1) (the head of Compile/Batch/OneCallCostPL.lean; `cCPLW_one`, `cPLW_one`); `bk`: a `CoinPlan`
(Rom/Blocks.lean): how a uniform sample is made from small ones.

Limits: no closed form, no numeral, no mean. A call counts as one however long its string.
-/
import Compile.Batch.CutQueries
import Compile.Batch.OneCallCostPL

set_option autoImplicit false

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP
open Compile.Batch.Need (needOf Std)
open Compile.Batch.OneCall (TryW nbAll num_nbAll numA_congr cntSt_congr wR_fail cCPLW cPLW)

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {W : QueryLayout lam L} {m : OracleCoding (spec lam W.K L) lam}

theorem cntSt_true : ∀ (K j : ℕ), cntSt (fun _ => true) K j = K
  | 0, _ => rfl
  | K + 1, j => by
    unfold cntSt
    rw [cntSt_true K (j + 1), if_pos rfl]
    omega

/-- under `Need.Std`, at an oracle other than `fb t`: `ruleT` at `nbAll W.K` queries all blocks -/
theorem numA_all_other (hm : Std m) {o : OracleName} (ho : ∀ t, o ≠ .fb t)
    (q : domOf lam L o) (r : rngOf lam W.K o) :
    numA m (ruleT W (nbAll W.K) m) o q r = m.blocks o := by
  rw [numA_congr m (ruleT_other W (nbAll W.K) m ho q) r,
    (ofNeedA _ lam m (needOf (nbAll W.K) m)).2.2 o q r, num_nbAll hm]

/-- under `Need.Std`, `Test0`, at a Fiat-Shamir query that is no failed attempt before the last:
`ruleT` at `nbAll W.K` queries all blocks -/
theorem numA_all_kept (hm : Std m) (h0 : Test0 W) (t : Tag) (q : FbIn lam L t)
    (r : rngOf lam W.K (.fb t)) (hf : ¬ failsAt W t q r.1 = true) :
    numA m (ruleT W (nbAll W.K) m) (.fb t) q r = W.K + 1 := by
  have hb : m.blocks (.fb t) = W.K + 1 := hm.blocks _
  cases hx : tryInfoT W t q.plain with
  | none =>
    rw [numA_congr (o := OracleName.fb t) m (ruleT_none W (nbAll W.K) m hx) r,
      (ofNeedA _ lam m (needOf (nbAll W.K) m)).2.2 (.fb t) q r, num_nbAll hm, hb]
  | some x =>
    have hp : (x.1 (fun _ => block0 m (.fb t) r) || x.2) = true := by
      rw [← test_block0 hm h0 hx r]
      unfold failsAt at hf
      rw [hx] at hf
      have h1 : ¬ (!x.1 r.1 && !x.2) = true := hf
      cases h2 : x.1 r.1 <;> cases h3 : x.2 <;> simp [h2, h3] at h1 ⊢
    unfold numA
    rw [ruleT_some W (nbAll W.K) m hx, cntFrom_ndTest' _ _ _ _ (by omega : 0 < m.blocks (.fb t)),
      if_pos (show (x.1 (fun _ => extBl (m.rng (.fb t) r) 0) || x.2) = true from hp)]
    have hb1 : m.blocks (.fb t) - 1 = W.K := by omega
    rw [hb1, cntSt_congr (st' := fun _ => true) W.K 1 fun i _ h3 => ?_, cntSt_true]
    · omega
    · show (if hh : i < m.blocks (.fb t) then needOf (nbAll W.K) m (.fb t) q ⟨i, hh⟩ else false) =
        true
      rw [dif_pos (by omega)]
      exact decide_eq_true (.inr (by show i < W.K + 1; omega))

/-- what a Fiat-Shamir query weighs at most: the first block, the state, the expansion queries -/
def bfF (nb : Tag → ℕ → ℕ) : Tag → ℕ → ℕ := fun t i => 3 + (nb t i - 1)

variable {nb : Tag → ℕ → ℕ}

theorem wF_fb_le (hK : 2 ≤ W.K) (hT : Test0 W) (t : Tag)
    (q : FbIn lam L t) (r : rngOf lam W.K (.fb t)) :
    wF W nb (.fb t) q r ≤ bfF nb t q.round := by
  by_cases hf : failsAt W t q r.1 = true
  · rw [wF_fail W nb hK hT hf]
    unfold bfF
    omega
  · rw [wF_kept W nb hK hT hf]
    unfold bfF
    omega

/-- Under the hypotheses below, wF meets `TryW`. -/
theorem tryW_wF (hm : Std m) (hT : Test0 W) (hK : 2 ≤ W.K) (hnb : ∀ t i, nb t i < W.K) :
    TryW W (nbAll W.K) m (wF W nb) 1 (bfF nb) where
  std := hm
  le := fun o q r => by
    by_cases ho : ∃ t, o = .fb t
    · obtain ⟨t, rfl⟩ := ho
      by_cases hf : failsAt W t q r.1 = true
      · rw [wF_fail W nb hK hT hf, wR_fail hm hT t q r hf]
      · rw [wF_kept W nb hK hT hf, numA_all_kept hm hT t q r hf]
        have := hnb t (q : FbIn lam L t).round
        omega
    · have ho' : ∀ t, o ≠ .fb t := fun t e => ho ⟨t, e⟩
      rw [wF_whole W nb ho' q r, numA_all_other hm ho' q r, hm.blocks o]
  none := fun t q r _ => wF_fb_le hK hT t q r
  some := fun t q r _ _ _ => wF_fb_le hK hT t q r
  fail := fun t q r hf => le_of_eq (wF_fail W nb hK hT hf)

theorem nbPosSh_all {K : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A) (i : ℕ), NbPosSh (fun _ => K + 1) s A ws i
  | [], _, _, _ => trivial
  | _ :: s, (_, A), (_, ws), i => ⟨fun _ => Nat.succ_pos _, nbPosSh_all s A ws (i + 1)⟩

theorem nbPos_all (W : QueryLayout lam L) : NbPos W (nbAll W.K) :=
  ⟨nbPosSh_all _ _ _ 0, nbPosSh_all _ _ _ 0, nbPosSh_all _ _ _ 0⟩

variable (WP : WireBP L) (p : Params) (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L)) (ℓ : ℕ)

/-- The committer. -/
theorem costC_wF (hm : Std m) (hT : Test0 W) (hK : 2 ≤ W.K) (hnb : ∀ t i, nb t i < W.K) (hW : W.OKG)
    (hσ : σ.o = OracleName.other) (i : I) :
    ((prunedK W p (Seed.argPL W WP p bk σ ℓ Seed.noK)).C i).CostBoundV
      (wF W nb) (cCPLW W WP p bk 1 (bfF nb)) :=
  ((OneCall.cav_C_argPL WP p (tryW_wF hm hT hK hnb) hW (nbPos_all W) bk σ hσ ℓ Seed.noK i).map
    (Q := fun _ => True) _ fun _ _ => trivial).cost

/-- The prover, on a batch b. -/
theorem costP_wF (hm : Std m) (hT : Test0 W) (hK : 2 ≤ W.K) (hnb : ∀ t i, nb t i < W.K)
    (hW : W.OKG) (hσ : σ.o = OracleName.other) {nE : ℕ} (hE : ∀ x ρ, (L.onlineBatch.loc.extReads x ρ).card ≤ nE)
    (kc : (I × Fin (σ.sd + 1)) × Seed.Ca lam)
    (hk : ∀ st ∈ kc.2, st.2.length ≤ 2 ^ (W.depth - ℓ)) (b : List (X × Unit)) :
    ((prunedK W p (Seed.argPL W WP p bk σ ℓ Seed.noK)).P kc b).CostBoundV
      (wF W nb) (cPLW W WP p bk 1 (bfF nb) ℓ nE b.length) :=
  ((OneCall.cav_P_argPL WP p (tryW_wF hm hT hK hnb) hW (nbPos_all W)
      bk σ hσ hE ℓ Seed.noK kc hk b).map
    (Q := fun _ => True) _ fun _ _ => trivial).cost

variable (c : StrCode (RealPtsCS lam W.K L)) (cG : StrCode (GhostPts lam W.K L))

/-- The committer's queries to f, under the hypotheses below. -/
theorem queryBound_C_CSO (hm : Std m) (hT : Test0 W) (hK : 2 ≤ W.K) (hnb : ∀ t i, nb t i < W.K)
    (hW : W.OKG) (hσ : σ.o = OracleName.other) (i : I) :
    (((((prunedK W p (Seed.argPL W WP p bk σ ℓ Seed.noK)).C i).cut
            (cutFS lam W.K L) (needT W)).stateFirstA
          (linksS lam W.K L) (needD nb)).overOne
        (implCS lam W.K L c cG)).QueryBound
      (cCPLW W WP p bk 1 (bfF nb)) :=
  queryBound_CSO W nb c cG _ _ (costC_wF WP p bk σ ℓ hm hT hK hnb hW hσ i)

/-- The prover's queries to f, on a batch b, under the hypotheses below. -/
theorem queryBound_P_CSO (hm : Std m) (hT : Test0 W) (hK : 2 ≤ W.K) (hnb : ∀ t i, nb t i < W.K)
    (hW : W.OKG) (hσ : σ.o = OracleName.other) {nE : ℕ} (hE : ∀ x ρ, (L.onlineBatch.loc.extReads x ρ).card ≤ nE)
    (kc : (I × Fin (σ.sd + 1)) × Seed.Ca lam)
    (hk : ∀ st ∈ kc.2, st.2.length ≤ 2 ^ (W.depth - ℓ)) (b : List (X × Unit)) :
    (((((prunedK W p (Seed.argPL W WP p bk σ ℓ Seed.noK)).P kc b).cut
            (cutFS lam W.K L) (needT W)).stateFirstA
          (linksS lam W.K L) (needD nb)).overOne
        (implCS lam W.K L c cG)).QueryBound
      (cPLW W WP p bk 1 (bfF nb) ℓ nE b.length) :=
  queryBound_CSO W nb c cG _ _ (costP_wF WP p bk σ ℓ hm hT hK hnb hW hσ hE kc hk b)

/-! ## Comparison with cPLA and cCPLA -/

section Add
open Compile.Batch.Need (PhK)
open Compile.Batch.OneCall
  (cSlotW cSharedW cProve1W cPUW cCBW cCPW cSlotW_lo cSlotW_join cSlotW_sh cSharedW_lo cSharedW_join
    cSharedW_shr cSharedW_none)

variable {K : ℕ} (a d : ℕ) {bff bff' : ℕ → ℕ} (h : ∀ i, bff' i ≤ bff i + d)
include h

theorem cSlotW_add :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A) (i : ℕ) (ph : PhK),
      cSlotW a bff' s A ws i ph ≤ cSlotW a bff s A ws i ph + d * s.length
  | [], _, _, _, _ => Nat.zero_le _
  | r :: s, (an, A), (w, ws), i, ph => by
    have hl : d * (r :: s).length = d * s.length + d := by rw [List.length_cons, Nat.mul_succ]
    rw [hl]
    by_cases hk : an.kind = .lo
    · rw [cSlotW_lo a bff' an A w ws i hk ph, cSlotW_lo a bff an A w ws i hk ph]
      have h1 := cSlotW_add s A ws (i + 1) ph.afterLo
      have h2 := h i
      omega
    · have hk' : an.kind = .sh := by
        cases e : an.kind with
        | lo => exact absurd e hk
        | sh => rfl
      cases ph with
      | loc =>
        rw [cSlotW_join a bff' an A w ws i hk', cSlotW_join a bff an A w ws i hk']
        have h1 := cSlotW_add s A ws (i + 1) .shr
        omega
      | first =>
        rw [cSlotW_sh a bff' an A w ws i hk' .first (.inl rfl),
          cSlotW_sh a bff an A w ws i hk' .first (.inl rfl)]
        have h1 := cSlotW_add s A ws (i + 1) .first
        omega
      | shr =>
        rw [cSlotW_sh a bff' an A w ws i hk' .shr (.inr (.inl rfl)),
          cSlotW_sh a bff an A w ws i hk' .shr (.inr (.inl rfl))]
        have h1 := cSlotW_add s A ws (i + 1) .shr
        omega
      | aft =>
        rw [cSlotW_sh a bff' an A w ws i hk' .aft (.inr (.inr rfl)),
          cSlotW_sh a bff an A w ws i hk' .aft (.inr (.inr rfl))]
        have h1 := cSlotW_add s A ws (i + 1) .aft
        omega

theorem cSharedW_add (Ns : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (ws : RoundsQueryLayout lam K s A) (i : ℕ) (ph : PhK),
      cSharedW a bff' Ns s A ws i ph ≤ cSharedW a bff Ns s A ws i ph + d * s.length
  | [], _, _, _, _ => Nat.zero_le _
  | r :: s, (an, A), (w, ws), i, ph => by
    have hl : d * (r :: s).length = d * s.length + d := by rw [List.length_cons, Nat.mul_succ]
    rw [hl]
    have h2 := h i
    by_cases hk : an.kind = .lo
    · rw [cSharedW_lo a bff' Ns an A w ws i hk ph, cSharedW_lo a bff Ns an A w ws i hk ph]
      have h1 := cSharedW_add Ns s A ws (i + 1) ph.afterLo
      omega
    · have hk' : an.kind = .sh := by
        cases e : an.kind with
        | lo => exact absurd e hk
        | sh => rfl
      cases ph with
      | loc =>
        rw [cSharedW_join a bff' Ns an A w ws i hk', cSharedW_join a bff Ns an A w ws i hk']
        have h1 := cSharedW_add Ns s A ws (i + 1) .shr
        omega
      | shr =>
        rw [cSharedW_shr a bff' Ns an A w ws i hk', cSharedW_shr a bff Ns an A w ws i hk']
        have h1 := cSharedW_add Ns s A ws (i + 1) .shr
        omega
      | first =>
        rw [cSharedW_none a bff' Ns an A w ws i hk' .first (.inl rfl),
          cSharedW_none a bff Ns an A w ws i hk' .first (.inl rfl)]
        have h1 := cSharedW_add Ns s A ws (i + 1) .first
        omega
      | aft =>
        rw [cSharedW_none a bff' Ns an A w ws i hk' .aft (.inr rfl),
          cSharedW_none a bff Ns an A w ws i hk' .aft (.inr rfl)]
        have h1 := cSharedW_add Ns s A ws (i + 1) .aft
        omega

theorem cProve1W_add {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E} (wq : ProtocolQueryLayout lam K Q) :
    cProve1W a bff' wq ≤ cProve1W a bff wq + 2 * (d * Q.loc.shape.length) := by
  unfold cProve1W
  have h1 := cSharedW_add a d h 1 Q.loc.shape Q.ann wq.sh 0 .first
  have h2 := cSlotW_add a d h Q.loc.shape Q.ann wq.sh 0 .first
  omega

end Add

theorem bfF_le (nb : Tag → ℕ → ℕ) (t : Tag) (i : ℕ) : bfF nb t i ≤ (nb t i + 1) + 2 := by
  unfold bfF
  omega

/-- The prover: at most two calls more for each round of each slot and of the shared part than in
cPLA. -/
theorem cPLW_bfF_le (W : QueryLayout lam L) (nb : Tag → ℕ → ℕ) (nE n : ℕ) :
    cPLW W WP p bk 1 (bfF nb) ℓ nE n ≤
      cPLA W WP p nb bk ℓ nE n + 2 * ((n + 1) * L.onlineBatch.loc.shape.length) := by
  rw [← OneCall.cPLW_one W WP p bk nb ℓ nE n]
  unfold cPLW OneCall.cPUW
  have h1 := cSharedW_add 1 2 (bfF_le nb .onl) L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh 0 .first
  have h2 : n * OneCall.cSlotW 1 (bfF nb .onl) L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh 0 .first ≤
      n * (OneCall.cSlotW 1 (fun i => nb .onl i + 1) L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh 0 .first +
          2 * L.onlineBatch.loc.shape.length) :=
    Nat.mul_le_mul_left n
      (cSlotW_add 1 2 (bfF_le nb .onl) L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh 0 .first)
  have h3 : 2 * ((n + 1) * L.onlineBatch.loc.shape.length) =
      n * (2 * L.onlineBatch.loc.shape.length) + 2 * L.onlineBatch.loc.shape.length := by ring
  rw [Nat.mul_add] at h2
  beta_reduce
  omega

/-- The committer: compared with cCPLA. -/
theorem cCPLW_bfF_le (W : QueryLayout lam L) (nb : Tag → ℕ → ℕ) :
    cCPLW W WP p bk 1 (bfF nb) ≤
      cCPLA W WP p nb bk + 4 * (L.offline.shape.length + (p.M + 1) * L.link.shape.length) := by
  rw [← OneCall.cCPLW_one W WP p bk nb]
  unfold cCPLW OneCall.cCPW OneCall.cCBW
  have h1 : OneCall.cProve1W 1 (bfF nb .test) W.T ≤
      OneCall.cProve1W 1 (fun i => nb .test i + 1) W.T + 2 * (2 * L.offline.shape.length) :=
    cProve1W_add 1 2 (bfF_le nb .test) W.T
  have h2 : (p.M + 1) * (Need.tr W.depth + OneCall.cProve1W 1 (bfF nb .link) W.Lk) ≤
      (p.M + 1) *
        (Need.tr W.depth +
          (OneCall.cProve1W 1 (fun i => nb .link i + 1) W.Lk + 2 * (2 * L.link.shape.length))) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_left (cProve1W_add 1 2 (bfF_le nb .link) W.Lk) _)
  have h3 : (p.M + 1) *
        (Need.tr W.depth +
          (OneCall.cProve1W 1 (fun i => nb .link i + 1) W.Lk + 2 * (2 * L.link.shape.length))) =
      (p.M + 1) * (Need.tr W.depth + OneCall.cProve1W 1 (fun i => nb .link i + 1) W.Lk) +
        4 * ((p.M + 1) * L.link.shape.length) := by ring
  beta_reduce
  omega

end Compile.Batch
