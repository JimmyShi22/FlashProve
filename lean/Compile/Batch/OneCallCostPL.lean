-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/OneCallCostPL.lean: for a weight with `TryW`, under the hypotheses of their
statements, on every path the weights of the queries of the committers of `argSeed` and `argPL` and
of the lazy prover add up to at most the sums `cCPW`, `cCPLW`, `cPLW`. The sums at the rule's own
weight are in Compile/Batch/SpecOneCallL.lean. (Words of this library: lean/GLOSSARY.md.)

The lemmas are generic in what an attempt weighs (Compile/Batch/OneCallCostW.lean:
`TryW W nb m wt ca bf`: `Std m`; a weight wt that is nowhere above the rule's; ca: what a failed
attempt that is not the last weighs at most; bf t i: what any Fiat-Shamir query of round i of
protocol t weighs at most, with proof-of-work bits if the table marks a block there), with the sums
`cCPW`, `cCPLW`, `cPLW` over `cCBW`, `cPUW` (Compile/Batch/OneCallCostR.lean); `cCPW_one`,
`cCPLW_one`, `cPLW_one`: at the rule's own weight (ca = 1, bf t i = nb t i + 1) they are `cCPA`,
`cCPLA`, `cPLA`.

How. Nothing but the Fiat-Shamir part has a search. Every part without a search is taken from the
lemmas for the table (Compile/Batch/NeedCostPL.lean, Compile/Batch/NeedCostChains.lean: `ca_nodeD`,
`ca_levelsV`, `ca_rD`, `ca_opL`, `ca_finishAllL`, `ca_cacheFrom`), at the table that marks every
block, by `CAV.of_ca`: the rule never asks for more blocks than an answer has (`numR_le_all`,
`numW_le_all`). (Exactly: so for the cache and the lazy prover; inside token programs (`Step`,
Rom/Defer.lean) the way is `swv_of`, Compile/Batch/OneCallCostR.lean; for the coins derived under
the seed: `CAV.derive`, `numW_seed`.) Their bounds do not depend on the table. The chains:
`swv_chainsU`, over `swv_chainTU` (Compile/Batch/OneCallCostR.lean). The committer with fresh coins:
`costV_C` (Compile/Batch/OneCallCostS.lean). One execution: `swv_proveBU`.

  `cav_C_argSeed`, `cav_C_argPL`, `cav_P_argPL`
      the three theorems (hypotheses: the header of Compile/Batch/SpecOneCallL.lean)

Not in this library: the four statements at the rule "block 0 first" (`ruleT`,
Compile/Batch/SpecOneCall.lean), for C and P of prunedK W p (Seed.argPL ..) and of prunedK W p (argP
..) (`prunedK`: Compile/Batch/StarO.lean); the sum and the lemmas for the prover of `argP` (but for
`swv_batOf`, which is here); a lemma that the sums `cCPW`, `cCPLW`, `cPLW` (at the rule's own
weight: `cCPA`, `cCPLA`, `cPLA`) are never larger than those for the table of the second exit
(Rom/OverOneN.lean).

Notation:
  the lazy prover: `PL` (Compile/Batch/SeedLazyDefs.lean); the cache: `Ca`: for each copy the root
    of its tree and the digests of one level (Compile/Batch/SeedCache.lean)
  `W`: a `QueryLayout lam L`, the wire record (Iop/BatchWire.lean)
  `WP`: a `WireBP L`: the prover's data for the three protocols, and the enumeration of the encoding
    randomness (Iop/BatchWireP.lean)
  `p`: a `Params` (Compile/Star.lean); `p.sMT`, `p.sFS`: the length of the salt of a leaf, and of
    the salt of a chain (Compile/Batch/Verifier.lean); the number of copies is `p.M` + 1
  `bk`: a `CoinPlan`: how a uniform sample is made from small ones (Rom/Blocks.lean); bk.m n: the
    number of small samples for a sample with n + 1 outcomes
  `σ`: a `SeedOracle`: an auxiliary oracle, used as a source of coins; `pt s j` is the query for the
    seed s and the counter j (Rom/SpecDerive.lean)
  `ℓ`, `nE`, `n`: natural numbers; ℓ: the number of the stored level (`keep`,
    Compile/Batch/SeedCache.lean); nE: in `hE`, a slot's verifier reads at most so many positions of
    the encoded index (the head of Compile/Batch/NeedCostPL.lean); n: a batch with n requests
  what the terms `off`, `cNode`, `tr`, `cOpL` of `cCPW`, `cCPLW`, `cPLW` count: the head of
    Compile/Batch/NeedCostPL.lean
Limits: the header of Compile/Batch/SpecOneCallL.lean. Worst case over the oracle: every search at
its cap; but an attempt that fails and is not the last weighs at most ca (1 at the rule's own
weight).

The analogue of Compile/Batch/NeedCostPL.lean.
-/
import Compile.CostPostV
import Compile.Batch.SpecOneCallL
import Compile.Batch.OneCallCostS

set_option autoImplicit false

open Rom Iop

namespace Compile.Batch
namespace OneCall
open Compile.CostP (SWV SWA)
open Compile.Seed (Tosses Wt)
open Compile.Batch.Need (Std needOf tr full cOpL)
open Seed

/-! ## The sums -/

section Sums
variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (bk : CoinPlan) (ca : ℕ) (bf : Tag → ℕ → ℕ)

/-- the committer with one seed -/
def cCPW : ℕ := cCBW W p ca bf + off W WP p bk.m (p.M + 1)
/-- the committer that also computes the cache -/
def cCPLW : ℕ := cCPW W WP p bk ca bf + (p.M + 1) * (tr W.depth + cNode W WP p bk.m)
/-- the lazy prover, a batch with n requests -/
def cPLW (ℓ nE n : ℕ) : ℕ :=
  (2 ^ (W.depth - ℓ) - 1) + bk.m WP.ri.n + cPUW W ca bf n + n * (nE * cOpL p bk ℓ)

variable (nb : Tag → ℕ → ℕ)

theorem cCPW_one : cCPW W WP p bk 1 (fun t i => nb t i + 1) = cCPA W WP p nb bk := by
  unfold cCPW cCPA; rw [cCBW_one]
theorem cCPLW_one : cCPLW W WP p bk 1 (fun t i => nb t i + 1) = cCPLA W WP p nb bk := by
  unfold cCPLW cCPLA; rw [cCPW_one]
theorem cPLW_one (ℓ nE n : ℕ) :
    cPLW W WP p bk 1 (fun t i => nb t i + 1) ℓ nE n = cPLA W WP p nb bk ℓ nE n := by
  unfold cPLW cPLA; rw [cPUW_one]

end Sums

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {W : QueryLayout lam L} {nb : Tag → ℕ → ℕ} {m : OracleCoding (spec lam W.K L) lam} {wt : (o : OracleName) → domOf lam L o → rngOf lam W.K o → ℕ} {ca : ℕ} {bf : Tag → ℕ → ℕ}

local notation "T1" => fun _ => True
local notation "SWr" => SWV (S := spec lam W.K L) (sp := split lam W.K L) (pre wt)
local notation "CVo" => OComp.CAV (S := spec lam W.K L) wt

/-! ## Part 1. Tools -/

/-- bound and property carry over to `realQ` of the algorithm (Compile/Batch/Oracles.lean: queries
to `fbw` become queries to `fb`) -/
theorem cav_realQ {α : Type} {P : α → Prop} (c : TypedOracleComputation lam W.K L α) :
    ∀ t, OComp.CAV (pre wt) c t P → CVo (realQ c) t P := by
  induction c with
  | pure a => exact fun _ h => h
  | sample n k ih => exact fun t h r => ih r t (h r)
  | query o q k ih =>
    intro t h
    cases o <;> exact fun r => let ⟨t', e, h'⟩ := h r; ⟨t', e, ih r t' h'⟩

theorem cav_eraseR {α : Type} {P : α → Prop} {c : St lam W.K L α} {n : ℕ}
    (h : SWr c n P) (vs : List Bits) :
    CVo (eraseR c vs) n fun o => P o.1 :=
  cav_realQ _ _ (h.cav vs)

/-- under `Std m`: the rule never asks for more blocks than an answer has -/
theorem numR_le_all (hm : Std m) (o : OracleName) (q : domOf lam L o) (r : rngOf lam W.K o) :
    numA m (ruleT W nb m) o q r ≤ (needOf (nbAll W.K) m).num o q := by
  rw [num_nbAll hm]
  exact numA_le_blocks m _ o q r

theorem numW_le_all (TW : TryW W nb m wt ca bf) (o : OracleName) (q : domOf lam L o) (r : rngOf lam W.K o) :
    wt o q r ≤ (needOf (nbAll W.K) m).num o q :=
  (TW.le o q r).trans (numR_le_all TW.std o q r)

/-- under `TryW`: a part that is bounded (`CA`) for the table that marks every block is bounded here
by the same number -/
theorem cav_of (TW : TryW W nb m wt ca bf) {α : Type} {c : TypedOracleComputation lam W.K L α} {n : ℕ} {P : α → Prop}
    (h : OComp.CA (S := spec lam W.K L) (Rom.Need.num (needOf (nbAll W.K) m)) c n P) : CVo c n P :=
  OComp.CAV.of_ca (numW_le_all TW) h

/-- under `TryW`, σ.o = `OracleName.other`: a query of the seed oracle weighs at most 1 -/
theorem numW_seed (TW : TryW W nb m wt ca bf) (σ : SeedOracle (spec lam W.K L))
    (hσ : σ.o = OracleName.other) (s : Fin (σ.sd + 1)) (j : ℕ) (r : rngOf lam W.K σ.o) :
    wt σ.o (σ.pt s j) r ≤ 1 :=
  (numW_le_all TW _ _ r).trans (Need.num_seed W (nbAll W.K) TW.std σ hσ s j)

/-! ## Part 2. The chains -/

/-- The first part of the compiled prover with no query for an empty slot, with what it returns. -/
theorem swv_chainsU (TW : TryW W nb m wt ca bf) (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec}
    (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam W.K Q) (wp : WirePB Q H)
    (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X)
    (depthReq : ℕ) (cms : List (Dig lam)) (w : Wt)
    (hR : RuleSh W nb t Q.loc.shape Q.ann wq.sh embP 0) (xs : List (Option Y)) :
    SWr (chainsU sMT sFS t Q H wq wp embS embP xin depthReq cms w xs)
      (cSharedW ca (bf t) xs.length Q.loc.shape Q.ann wq.sh 0 .first +
        (xs.map Option.isSome).count true * cSlotW ca (bf t) Q.loc.shape Q.ann wq.sh 0 .first)
      fun o => o.2.1.map (fun a => a.x.isSome) = xs.map Option.isSome := by
  unfold chainsU
  refine SWV.bind' (swv_of TW (Need.swa_drawT (nbAll W.K) wp.coin0))
    (fun c0 _ =>
      SWV.bind' (swv_eachM Option.isSome full 0
          (fun a =>
            (swv_of TW (Need.swa_initSlotU (nbAll W.K) sFS Q H wp w c0 a)).mono
              (fun _ h => h) (Nat.zero_le _)) xs)
        (fun zs hz =>
          SWV.bind' (swv_chainTU TW sMT t _ _ depthReq _ _ _ embS embP 0 .first _ zs _
              (xs.map Option.isSome) hR hz)
            (m' := 0) (fun out ho => ho) (Nat.le_refl _)) (Nat.le_refl _)) (le_of_eq ?_)
  rw [List.length_map, Nat.mul_zero, Nat.zero_add, Nat.zero_add, Nat.add_zero]
  rfl

/-! ## Part 3. One seed -/

/-- The committer of the scheme with isk = (i, seed), for every `F : Face`. -/
theorem cav_C_argSeed (WP : WireBP L) (p : Params) (TW : TryW W nb m wt ca bf) (hW : W.OKG)
    (hP : NbPos W nb) (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L)) (hσ : σ.o = OracleName.other)
    {IVK' Pf' : Type} (F : Face W IVK' Pf') (i : I) :
    CVo ((argSeed WP p F bk σ).C i) (cCPW W WP p bk ca bf) T1 := by
  intro s
  have hw : Wt bk.m (off W WP p bk.m (p.M + 1) + 0) ((argOf WP p F).C i) :=
    (wt_C W WP p bk.m i).bind fun _ => .pure _
  have hc : CVo ((argOf WP p F).C i) (cCBW W p ca bf) T1 :=
    (OComp.CAV.ofCost (costV_C WP p TW hW hP i)).map _ fun _ _ => trivial
  refine OComp.CAV.map (P := T1) ?_ _ fun _ _ => trivial
  exact (OComp.CAV.derive σ s (numW_seed TW σ hσ s) (hw.tosses_blocks bk)
      _ 0 (OComp.CAV.blocks bk _ _ hc)).mono
    (fun _ h => h) (by unfold cCPW; omega)

/-- one batch of the scheme with no query for an empty slot, on a `Node` -/
theorem swv_batOf (WP : WireBP L) (p : Params) (TW : TryW W nb m wt ca bf) (hW : W.OKG)
    (hP : NbPos W nb) (i : I) (j : ℕ) (nd : Option (Node lam L)) (b : List (X × Unit)) :
    SWr (batOf WP (runBU W WP p) i j nd b) (cPUW W ca bf b.length) T1 := by
  unfold batOf
  refine SWV.bind' (swv_of TW (Need.swa_drawT (nbAll W.K) WP.perm))
    (fun σ' _ => ?_) (le_of_eq (Nat.zero_add _))
  cases nd with
  | none => trivial
  | some nd =>
    refine SWV.bind'
      (swv_proveBU TW p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ _ _ W.depthReq
        _ _ (ruleSh_B hW hP) _ _)
      (m' := 0) (fun _ _ => trivial) ?_
    rw [Need.length_slotsOfReq, Nat.add_zero]
    exact Nat.add_le_add_left
      (Nat.mul_le_mul_right _
        (le_trans (Need.count_slotsOfReq σ' _) (le_of_eq (List.length_map _)))) _

/-! ## Part 4. The cache; the lazy prover -/

/-- The committer of the scheme with the lazy prover. -/
theorem cav_C_argPL (WP : WireBP L) (p : Params) (TW : TryW W nb m wt ca bf) (hW : W.OKG)
    (hP : NbPos W nb) (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L)) (hσ : σ.o = OracleName.other)
    (ℓ : ℕ) (no : (j : ℕ) → (b : List (X × Unit)) → ZKCP.Gen.Slots (PrfK lam L) b) (i : I) :
    CVo ((argPL W WP p bk σ ℓ no).C i) (cCPLW W WP p bk ca bf) T1 :=
  OComp.CAV.bind' (cav_C_argSeed WP p TW hW hP bk σ hσ (faceKE W WP p) i)
    (fun o _ =>
      ((cav_of TW
            (Need.ca_cacheFrom W WP p (nbAll W.K) TW.std bk σ hσ ℓ o.2 (List.range (p.M + 1)))).map
          _ fun _ _ => trivial).mono
        (fun _ h => h) (le_of_eq (by rw [List.length_range]))) (Nat.le_refl _)

/-- steps 4 to 6 of the lazy prover (the head of Compile/Batch/SeedLazyDefs.lean) -/
theorem cav_PLrun (WP : WireBP L) (p : Params) (TW : TryW W nb m wt ca bf) (hW : W.OKG)
    (hP : NbPos W nb) (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L)) (hσ : σ.o = OracleName.other)
    {nE : ℕ} (hE : ∀ x ρ, (L.onlineBatch.loc.extReads x ρ).card ≤ nE) (ℓ : ℕ)
    (no : (j : ℕ) → (b : List (X × Unit)) → ZKCP.Gen.Slots (PrfK lam L) b)
    (k : I × Fin (σ.sd + 1)) (b : List (X × Unit)) (j : ℕ) (st : Dig lam × List (Dig lam))
    (hi : List (List (Dig lam))) (r : L.EncodingRandomness) :
    CVo (PLrun W WP p bk σ ℓ no k b j st hi r)
      (cPUW W ca bf b.length + b.length * (nE * cOpL p bk ℓ)) T1 := by
  intro z
  have hcnt : ((slotsOfReq (WP.perm.e z) (b.map Prod.fst)).map Option.isSome).count true ≤
      b.length :=
    le_trans (Need.count_slotsOfReq _ _) (le_of_eq (List.length_map _))
  refine OComp.CAV.bind'
    (cav_eraseR
      (swv_chainsU TW p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ _ _ W.depthReq [st.1] (k.1, r)
        (ruleSh_B hW hP) (slotsOfReq (WP.perm.e z) (b.map Prod.fst))) [])
    (m' := b.length * (nE * cOpL p bk ℓ)) (fun o ho => ?_) ?_
  · refine OComp.CAV.bind' (Q := fun _ => True)
      (cav_of TW
        (Need.ca_finishAllL (nbAll W.K) L.onlineBatch L.honestOnlineBatchProver W.B WP.B (k.1, r) _
          (Need.ca_opL W WP p (nbAll W.K) TW.std bk σ hσ ℓ k j r st.2 hi)
          hE hW.B.ext.nodup _ o.1.1 o.1.2.2 o.1.2.1 0 o.2))
      (m' := 0) (fun oπ _ => ?_) ?_
    · cases oπ <;> exact trivial
    · rw [Nat.add_zero, ho]
      exact Nat.mul_le_mul_right _ hcnt
  · rw [Need.length_slotsOfReq]
    exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right _ hcnt) _) _

/-- The lazy prover, on a batch with n requests. -/
theorem cav_P_argPL (WP : WireBP L) (p : Params) (TW : TryW W nb m wt ca bf) (hW : W.OKG)
    (hP : NbPos W nb) (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L))
    (hσ : σ.o = OracleName.other) {nE : ℕ} (hE : ∀ x ρ, (L.onlineBatch.loc.extReads x ρ).card ≤ nE) (ℓ : ℕ)
    (no : (j : ℕ) → (b : List (X × Unit)) → ZKCP.Gen.Slots (PrfK lam L) b)
    (kc : (I × Fin (σ.sd + 1)) × Ca lam)
    (hk : ∀ st ∈ kc.2, st.2.length ≤ 2 ^ (W.depth - ℓ)) (b : List (X × Unit)) :
    CVo ((argPL W WP p bk σ ℓ no).P kc b) (cPLW W WP p bk ca bf ℓ nE b.length) T1 := by
  intro j
  show CVo (PLat W WP p bk σ ℓ no kc b j.val) _ T1
  unfold PLat
  cases hj : kc.2[j.val]? with
  | none => exact trivial
  | some st =>
    have hst : st.2.length - 1 ≤ 2 ^ (W.depth - ℓ) - 1 :=
      Nat.sub_le_sub_right (hk st (List.mem_of_getElem? hj)) 1
    refine OComp.CAV.bind' (Q := fun _ => True)
      (cav_of TW (Need.ca_levelsV W (nbAll W.K) TW.std (W.depth - ℓ) st.2))
      (m' := bk.m WP.ri.n + (cPUW W ca bf b.length + b.length * (nE * cOpL p bk ℓ)))
      (fun hi _ => ?_) (by unfold cPLW; omega)
    split_ifs
    · exact OComp.CAV.bind' (cav_of TW (Need.ca_rD W WP p (nbAll W.K) TW.std bk σ hσ kc.1 j.val))
        (fun ra _ => cav_PLrun WP p TW hW hP bk σ hσ hE ℓ no kc.1 b j.val st hi ra.1)
        (Nat.le_refl _)
    · exact trivial

end OneCall

end Compile.Batch
