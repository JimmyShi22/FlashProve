-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/OneCallCostS.lean: for a weight with `TryW`, under `W.OKG` and `NbPos`, on every path
the weights of the queries of the prover `PU` (no query for an empty slot), and of the committer,
add up to at most the counts of Compile/Batch/OneCallCostR.lean. (Statements at the rule's own
weight are not in this library.) (Words of this library: lean/GLOSSARY.md.)

The counterpart of Parts 5 and 6 of Compile/Batch/NeedCostP.lean for `SWV` (Compile/CostV.lean), for
every weight wt that meets `TryW W nb m wt ca bf` (Compile/Batch/OneCallCostW.lean), with the counts
`cPUW W ca bf n`, `cCBW W p ca bf` of Compile/Batch/OneCallCostR.lean. The parts that hold no search
(the proof strings, the start of a slot, the tree of a `Node`) are taken over from
Compile/Batch/NeedCostP.lean as they are (`swv_of`).

  `ruleSh_T`, `ruleSh_L`, `ruleSh_B`
      `RuleSh`, the hypothesis of the lemmas on chains, holds at the three whole protocols, from
      `W.OKG` and `NbPos W nb`
  `swv_PpJU`, `swv_PpU`, `costV_PU`
      under `TryW`, `W.OKG`, `NbPos`: the prover `PU`, a batch with n requests: on every path the
      weights add up to at most cPUW W ca bf n
  `swv_nodeP'`, `swv_proveT`, `swv_proveLk`, `swv_leavesC`, `swv_Cp`, `costV_C`
      under the same hypotheses: the committer's parts (`swv_nodeP'` .. `swv_leavesC`: each with its
      own term), and the committer (`swv_Cp`, `costV_C`): at most cCBW W p ca bf
  `loop_le`   moreOf gr + (c + 1) ≤ triesOf gr · (c + 1): one search

The case of the rule's own weight: `tryW_numA` of Compile/Batch/OneCallCostW.lean (ca = 1, bf t i =
nb t i + 1); there the counts are `cPUA`, `cCBA` of Compile/Batch/SpecOneCall.lean (`cPUW_one`,
`cCBW_one` of Compile/Batch/OneCallCostR.lean).

Of the like statements at the weight of Compile/Batch/NeedCostP.lean (its Parts 5 and 6),
`swa_nodeP'` alone is in this library (at a weight by the oracle's name alone, the whole committer
and `PU`: `honestKey_cost`, CompileK/HonestKeyWalkProofs.lean; `honestKey_costP`,
CompileK/HonestKeyWalkPProofs.lean).

Notation:
  `SWr c n P`: `SWV` (Compile/CostV.lean) at the weight `pre wt`: on every path the weights of the
    queries, each at its own answer, add up to at most n, and the result has the property P; `T1`:
    the property fun _ => True
  `c.CostBoundV wt n` (Rom/SpecOverOneA.lean), c an oracle algorithm: on every path the weights of
    the queries add up to at most n, where the weight of a query may depend on its answer; from
    `SWr`: `SWV.erase` (Compile/CostV.lean), then `costV_realQ_pre`
    (Compile/Batch/OneCallCostW.lean)
  `fl`, `fr`: ℕ → Bool; fl says for a slot, fr for a request, whether a proof string is made
    (`proveB`, Compile/Batch/Prover.lean; `FProg`, Compile/Batch/PubProg.lean)
  `p`: a `Params` (Compile/Star.lean); `p.sMT`, `p.sFS`: the length of the salt of a leaf, and of
    the salt of a chain (Compile/Batch/Verifier.lean); the number of copies is `p.M` + 1
  `depthReq`: a natural number; in `QueryLayout` (Iop/BatchWire.lean): depth of a request tree: there are
    2^depthReq slots
  `trees`: List (TreeH lam), the trees over the external strings (their roots are the cms of
    `chainsU`, Compile/Batch/SeedLazyDefs.lean); `embS`, `embP`: maps of the protocol's oracle
    symbols into `Body L`, and of its plain parts into those of protocol t
Limits: what the header of Compile/Batch/NeedCostP.lean lists. Worst case over the oracle.
-/
import Compile.Batch.OneCallCostR

noncomputable section

namespace Compile.Batch
namespace OneCall
open Iop Rom ZKCP
open Compile.CostP (SWV SWA)
open Compile.Batch.Need (Std needOf PhK phK costJ cost0 tr full)

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {W : QueryLayout lam L} {nb : Tag → ℕ → ℕ} {m : OracleCoding (spec lam W.K L) lam} {wt : (o : OracleName) → domOf lam L o → rngOf lam W.K o → ℕ} {ca : ℕ} {bf : Tag → ℕ → ℕ}

local notation "T1" => fun _ => True
local notation "SWr" => SWV (S := spec lam W.K L) (sp := split lam W.K L) (pre wt)

/-! ## One execution -/

section Prove
variable (TW : TryW W nb m wt ca bf) (sMT sFS : ℕ) (t : Tag) {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) {Wt : Type} (H : BatchHonestProver Q Wt) (wq : ProtocolQueryLayout lam W.K Q)
  (wp : WirePB Q H) (embS : (p : OPos Q.loc.shape) → OSym Q.loc.shape p → Body L)
  (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t)) (xin : Y → Option X) (depthReq : ℕ) (trees : List (TreeH lam)) (w : Wt)
include TW

/-- One execution of the compiled prover with no query for an empty slot. -/
theorem swv_proveBU (hR : RuleSh W nb t Q.loc.shape Q.ann wq.sh embP 0)
    (fl : ℕ → Bool) (xs : List (Option Y)) :
    SWr (proveBU sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs)
      (cSharedW ca (bf t) xs.length Q.loc.shape Q.ann wq.sh 0 .first +
        (xs.map Option.isSome).count true * cSlotW ca (bf t) Q.loc.shape Q.ann wq.sh 0 .first)
      T1 := by
  unfold proveBU
  refine SWV.bind' (swv_of TW (Need.swa_drawT (nbAll W.K) wp.coin0))
    (fun c0 _ =>
      SWV.bind' (swv_eachM Option.isSome full 0
          (fun a =>
            (swv_of TW (Need.swa_initSlotU (nbAll W.K) sFS Q H wp w c0 a)).mono
              (fun _ h => h) (Nat.zero_le _)) xs)
        (fun zs hz =>
          SWV.bind' (swv_chainTU TW sMT t _ _ depthReq _ _ _ embS embP 0 .first _ zs _
              (xs.map Option.isSome) hR hz)
            (m' := 0)
            (fun out _ =>
              swv_of TW (Need.swa_finishAll (nbAll W.K) Q H wq wp trees w fl c0 out.2 0 out.1))
            (Nat.le_refl _)) (Nat.le_refl _)) (le_of_eq ?_)
  rw [List.length_map, Nat.mul_zero, Nat.zero_add, Nat.zero_add, Nat.add_zero]
  rfl

/-- One execution of the compiled prover in which every slot works. -/
theorem swv_proveB (hR : RuleSh W nb t Q.loc.shape Q.ann wq.sh embP 0)
    (fl : ℕ → Bool) (xs : List (Option Y)) :
    SWr (proveB sMT sFS t Q H wq wp embS embP xin depthReq trees w fl xs)
      (cSharedW ca (bf t) xs.length Q.loc.shape Q.ann wq.sh 0 .first +
        xs.length * cSlotW ca (bf t) Q.loc.shape Q.ann wq.sh 0 .first) T1 := by
  unfold proveB
  refine SWV.bind' (swv_of TW (Need.swa_drawT (nbAll W.K) wp.coin0))
    (fun c0 _ =>
      SWV.bind' (swv_eachM_all 0
          (fun a =>
            (swv_of TW (Need.swa_initSlot (nbAll W.K) sFS Q H wp w c0 a)).mono
              (fun _ _ => trivial) (Nat.le_refl _)) xs)
        (fun zs hz =>
          SWV.bind'
            (swv_chainT TW sMT t _ _ depthReq _ _ _ embS embP 0 .first _ zs _ xs.length hR hz)
            (m' := 0)
            (fun out _ =>
              swv_of TW (Need.swa_finishAll (nbAll W.K) Q H wq wp trees w fl c0 out.2 0 out.1))
            (Nat.le_refl _)) (Nat.le_refl _)) (le_of_eq ?_)
  rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add, Nat.add_zero]
  rfl

end Prove

/-! ## The prover and the committer -/

theorem ruleSh_T (hW : W.OKG) (hP : NbPos W nb) :
    RuleSh W nb .test (BatchInteractiveOracleProof.ofProto L.offline).loc.shape
      (BatchInteractiveOracleProof.ofProto L.offline).ann W.T.sh id 0 :=
  ⟨hW.T.sh, fun _ => rfl, hP.1⟩
theorem ruleSh_L (hW : W.OKG) (hP : NbPos W nb) :
    RuleSh W nb .link (BatchInteractiveOracleProof.ofProto L.link).loc.shape
      (BatchInteractiveOracleProof.ofProto L.link).ann W.Lk.sh id 0 :=
  ⟨hW.Lk.sh, fun _ => rfl, hP.2.1⟩
theorem ruleSh_B (hW : W.OKG) (hP : NbPos W nb) :
    RuleSh W nb .onl L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh id 0 :=
  ⟨hW.B.sh, fun _ => rfl, hP.2.2⟩

section Star
variable (WP : WireBP L) (p : Params) (TW : TryW W nb m wt ca bf) (hW : W.OKG) (hP : NbPos W nb)
include TW hW hP

theorem swv_PpJU (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (j : ℕ) (σ : Equiv.Perm (Fin L.maxBatchSize)) :
    SWr (PpJU W WP p k fr xs j σ) (cPUW W ca bf xs.length) T1 := by
  unfold PpJU
  cases k.leaves[j]? with
  | none => trivial
  | some lf =>
    refine SWV.bind'
      (swv_proveBU TW p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ _ _ W.depthReq
        _ _ (ruleSh_B hW hP) _ _)
      (m' := 0) (fun _ _ => trivial) ?_
    rw [Need.length_slotsOfReq, Nat.add_zero]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Need.count_slotsOfReq σ xs)) _

theorem swv_PpU (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) :
    SWr (PpU W WP p k fr xs) (cPUW W ca bf xs.length) T1 :=
  fun j =>
    SWV.bind' (swv_of TW (Need.swa_drawT (nbAll W.K) WP.perm))
      (fun σ _ => swv_PpJU WP p TW hW hP k fr xs j.val σ) (le_of_eq (Nat.zero_add _))

/-- the prover with no query for an empty slot, on a batch with n requests -/
theorem costV_PU (k : ISK lam L) (b : List (X × Unit)) :
    (PU W WP p k b).CostBoundV wt (cPUW W ca bf b.length) := by
  have h := (swv_PpU WP p TW hW hP k.1 (fun _ => true) (b.map Prod.fst)).erase k.2
  rw [List.length_map] at h
  exact costV_realQ_pre wt _ _ (h.map _)

omit hW hP in
theorem swv_nodeP' (i : I) : SWr (nodeP' W WP p i) (tr W.depth) T1 :=
  swv_of TW (Need.swa_nodeP' W WP p (nbAll W.K) TW.std i)

theorem swv_proveT (tree : TreeH lam) (i : I) (r : L.EncodingRandomness) :
    SWr (proveT W WP p tree i r) (cProve1W ca (bf .test) W.T) T1 :=
  SWV.bind' (swv_proveB TW p.sMT p.sFS Tag.test _ _ W.T WP.T _ _ _ W.depthReq _ _ (ruleSh_T hW hP) _ [some ()]) (m' := 0) (fun _ _ => trivial) (le_of_eq (by
    show _ + 1 * _ + 0 = _
    rw [Nat.one_mul, Nat.add_zero]
    rfl))

theorem swv_proveLk (root tree : TreeH lam) (i : I) (r₀ r : L.EncodingRandomness) :
    SWr (proveLk W WP p root tree i r₀ r) (cProve1W ca (bf .link) W.Lk) T1 :=
  SWV.bind' (swv_proveB TW p.sMT p.sFS Tag.link _ _ W.Lk WP.Lk _ _ _ W.depthReq _ _ (ruleSh_L hW hP) _ [some ()]) (m' := 0) (fun _ _ => trivial) (le_of_eq (by
    show _ + 1 * _ + 0 = _
    rw [Nat.one_mul, Nat.add_zero]
    rfl))

theorem swv_leavesC (i : I) (root : Node lam L) :
    ∀ n, SWr (leavesC W WP p i root n) (n * (tr W.depth + cProve1W ca (bf .link) W.Lk)) T1
  | 0 => trivial
  | n + 1 =>
    SWV.bind' (swv_nodeP' WP p TW i)
      (m' := cProve1W ca (bf .link) W.Lk + n * (tr W.depth + cProve1W ca (bf .link) W.Lk))
      (fun nd _ =>
        SWV.bind' (swv_proveLk WP p TW hW hP _ _ _ _ _)
          (fun _ _ =>
            SWV.bind' (swv_leavesC i root n) (m' := 0) (fun _ _ => trivial) (Nat.le_refl _))
          (Nat.le_refl _))
      (le_of_eq (by rw [Nat.succ_mul]; omega))

theorem swv_Cp (i : I) : SWr (Cp W WP p i) (cCBW W p ca bf) T1 :=
  SWV.bind' (swv_nodeP' WP p TW i)
    (m' := cProve1W ca (bf .test) W.T + (p.M + 1) * (tr W.depth + cProve1W ca (bf .link) W.Lk))
    (fun root _ =>
      SWV.bind' (swv_proveT WP p TW hW hP _ _ _)
        (fun _ _ =>
          SWV.bind' (swv_leavesC WP p TW hW hP i root (p.M + 1)) (m' := 0)
            (fun _ _ => trivial) (Nat.le_refl _)) (Nat.le_refl _))
    (le_of_eq (by unfold cCBW; omega))

/-- the committer -/
theorem costV_C (i : I) : (C W WP p i).CostBoundV wt (cCBW W p ca bf) :=
  costV_realQ_pre wt _ _ (((swv_Cp WP p TW hW hP i).erase []).map _)

end Star

end OneCall


/-! ## One search (a lemma that the counts of Compile/Batch/OneCallCostR.lean (at the rule's own
weight: `cPUA`, `cCBA`, Compile/Batch/SpecOneCall.lean) are never larger than those for the table of
the second exit (Rom/OverOneN.lean) is not in this library) -/

namespace OneCall
open Iop Rom ZKCP
open Compile.Batch.Need (PhK)

theorem loop_le {C P : Type} (gr : Option (GrW C P)) (c : ℕ) :
    moreOf gr + (c + 1) ≤ triesOf gr * (c + 1) := by
  cases gr with
  | none => simp [moreOf, triesOf]
  | some g =>
    show g.more + (c + 1) ≤ (g.more + 1) * (c + 1)
    nlinarith [Nat.zero_le (g.more * c)]


end OneCall

end Compile.Batch
