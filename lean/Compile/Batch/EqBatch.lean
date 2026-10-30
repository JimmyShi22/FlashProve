-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/EqBatch.lean: given `Spec.eqProveB` and under the hypotheses of `Spec.eqBatchB`
(Compile/Batch/SpecEq.lean), a batch of the honest program has the distribution of the lifetime
game's batch on the adversary's own instances, then the reduction's program.

By name: the honest program is `PpLJ` (a program of `LStep`, Rom/DeferLate.lean), the game's batch
is `placeB` (Compile/Batch/SpecLifeStar.lean), the reduction's program is `PpW`
(Compile/Batch/Mirror.lean). The hypotheses of `Spec.eqBatchB`: `L.Wired`, `Coherent`, `Fmt`,
`W.OKG`, `GrFitPB W`, `WP.OK`; the copy exists (`k.leaves[j.val]? = some lf`); the batch has an own
request (`hasOwn b = true`) and at most L.maxBatchSize requests.

`Spec.eqProveB` (Compile/Batch/SpecEqProve.lean) is about one execution with given slots. Added here
is the placement (Compile/Batch/Place.lean): the prover places all requests by a uniform permutation
σ, the game places the own instances by a uniform σ'; with σ' = σ τ the own instances are in the
same slots; what the other slots hold does not influence the session of the own slots
(`BatchLife.bsess_vec_congr`); and the reply reads the proofs of the own requests only.

Notation: `b`: a `ZKCP.Gen.Batch X Unit` (ZKCP/Gen.lean): the batch; `reqs b`
(Compile/Batch/Chall.lean): the instances of all requests of the batch; `j`: a `Fin (p.M + 1)`: the
number of a copy (`Params.M`, Compile/Star.lean: the number of copies is M + 1); `k`: an
`IskH lam L` (Compile/Batch/Star.lean); `lf`: a `LeafRec lam L`, the type of the entries of
`k.leaves`; `σ`, `σ'`, `τ`: permutations of `Fin L.maxBatchSize`; `IsTau b τ` (Compile/Batch/Place.lean): τ
carries the place a' to the number, in the whole batch, of the a'-th own request; `N₀`, `δ`: natural
numbers, the arguments of `virtL` (Compile/Step1_defc_L.lean): the program under the renumbering of
tokens.
-/
import Compile.Batch.Place
import Compile.Batch.SpecEq
import Compile.Batch.SpecEqProve

noncomputable section

namespace Compile.Batch
open Iop Rom Prob
open Compile.GlueB (ownPf)
open Compile.BatchLife (slotList slotsOf ownAt placeB bsess vec BSess lt_of_mem_slotsOf)
open Compile.DefC (virtL)
open Place

namespace EqBatch

variable {X : Type} {N : ℕ}

/-- what slot s holds: request number σ⁻¹ s -/
def xAt (σ : Equiv.Perm (Fin N)) (xs : List X) : Fin N → Option X := fun s => xs[(σ.symm s).val]?

theorem slotsOfReq_eq (σ : Equiv.Perm (Fin N)) (xs : List X) :
    slotsOfReq σ xs = (List.finRange N).map (xAt σ xs) := rfl

theorem slotFlags_val (σ : Equiv.Perm (Fin N)) (fr : ℕ → Bool) (s : Fin N) :
    slotFlags σ fr s.val = fr (σ.symm s).val := by
  unfold slotFlags
  rw [dif_pos s.isLt]

variable {b : ZKCP.Gen.Batch X Unit} {τ : Equiv.Perm (Fin N)}

/-- Under `IsTau`: the slots with a flag are the slots of the first places of σ τ. -/
theorem ownSlots_eq (h : IsTau b τ) (σ : Equiv.Perm (Fin N)) :
    ownSlots (xAt σ (reqs b)) (slotFlags σ (ownFlag b)) = slotsOf (σ * τ) b.ownX.length := by
  ext s
  simp only [ownSlots, slotsOf, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [slotFlags_val, symm_mul, ← h.ownFlag_iff]
  refine ⟨fun hs => hs.1, fun hf => ⟨hf, ?_⟩⟩
  unfold xAt
  rw [List.getElem?_eq_getElem (by rw [length_reqs']; exact lt_of_ownFlag hf)]
  rfl

/-- Under `IsTau`: these slots hold the own instances, in the order of σ τ. -/
theorem xAt_of_mem (h : IsTau b τ) (σ : Equiv.Perm (Fin N)) (s : Fin N)
    (hs : s ∈ slotsOf (σ * τ) b.ownX.length) :
    xAt σ (reqs b) s = some (ownAt (σ * τ) b.ownX ⟨s, hs⟩) := by
  have ha : ((σ * τ).symm s).val < b.ownX.length := lt_of_mem_slotsOf ⟨s, hs⟩
  have h1 := h.ownX_at ((σ * τ).symm s) ha
  rw [symm_mul, Equiv.apply_symm_apply] at h1
  unfold xAt
  rw [← h1, ← symm_mul, List.getElem?_eq_getElem ha]
  rfl

theorem xAt_eq_vec (h : IsTau b τ) (σ : Equiv.Perm (Fin N)) :
    xAt σ (reqs b) =
      vec (slotsOf (σ * τ) b.ownX.length) (ownAt (σ * τ) b.ownX) fun s => xAt σ (reqs b) s.1 := by
  funext s
  unfold vec
  split
  · rename_i hs
    exact xAt_of_mem h σ s hs
  · rfl

/-- the instance of a slot of the first places, read through the list of these slots -/
theorem ownX_idxOf (h : IsTau b τ) (σ : Equiv.Perm (Fin N)) (s : Fin N)
    (hs : s ∈ slotsOf (σ * τ) b.ownX.length) :
    b.ownX[(slotList (σ * τ) b.ownX.length).idxOf s]? = xAt σ (reqs b) s := by
  have ha : ((σ * τ).symm s).val < b.ownX.length := lt_of_mem_slotsOf ⟨s, hs⟩
  have h1 := idxOf_slotList (σ * τ) ha ((σ * τ).symm s).isLt
  rw [Fin.eta, Equiv.apply_symm_apply] at h1
  rw [h1, xAt_of_mem h σ s hs, List.getElem?_eq_getElem ha]
  rfl

/-! ## What the reduction knows, and what is replied -/

section Proto

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {b : ZKCP.Gen.Batch X Unit} {τ : Equiv.Perm (Fin L.maxBatchSize)}

/-- Under `IsTau`: what the reduction knows of the slots is the same in both forms. -/
theorem osOf_eq_ownsOf (h : IsTau b τ) (σ : Equiv.Perm (Fin L.maxBatchSize))
    (so : BSess L.onlineBatch (slotsOf (σ * τ) b.ownX.length)) :
    osOf (xAt σ (reqs b)) (slotsOf (σ * τ) b.ownX.length) so =
      ownsOf b.ownX (slotList (σ * τ) b.ownX.length) (slotsOf (σ * τ) b.ownX.length) so := by
  unfold osOf ownsOf
  refine List.map_congr_left fun s _ => ?_
  by_cases hs : s ∈ slotsOf (σ * τ) b.ownX.length
  · rw [dif_pos hs, dif_pos hs, ownX_idxOf h σ s hs]
  · rw [dif_neg hs, dif_neg hs]

/-- the proofs of the own instances, as the reduction's program returns them -/
def prfsW (j : ℕ) (cm : Dig lam) (piL : Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)))
    (sl : List (Fin L.maxBatchSize)) (n : ℕ) (πs : List (Option (OneProtocolProof lam L.onlineBatch))) : List (Prf lam L) :=
  (List.range n).map fun a => ⟨j, cm, piL, (sl[a]?).bind fun s => πs.getD s.val none⟩

/-- Under the hypotheses below: the reply to the batch holds the proofs of the own instances, in
their order. -/
theorem replyOf_prfsOf (h : IsTau b τ) (hb : b.length ≤ L.maxBatchSize) (σ : Equiv.Perm (Fin L.maxBatchSize)) (j : ℕ)
    (cm : Dig lam) (piL : Option (OneProtocolProof lam (BatchInteractiveOracleProof.ofProto L.link)))
    (πs : List (Option (OneProtocolProof lam L.onlineBatch))) :
    replyOf b (RealB.prfsOf j cm piL σ (reqs b).length πs) =
      .inr (prfsW j cm piL (slotList (σ * τ) b.ownX.length) b.ownX.length πs) := by
  unfold replyOf
  rw [RealB.val_fitLen _ _ _ (by simp [RealB.prfsOf, RealB.length_reqs]), ownPf_eq]
  refine congrArg Sum.inr (List.ext_getElem? fun a' => ?_)
  have hsome : ∀ a ∈ ownIdx b,
      ((RealB.prfsOf j cm piL σ (reqs b).length πs)[a]?).isSome = true := by
    intro a ha
    have h1 := lt_of_ownFlag ((mem_ownIdx b a).1 ha)
    rw [List.getElem?_eq_getElem (by simp [RealB.prfsOf, length_reqs']; exact h1)]
    rfl
  rw [getElem?_filterMap_of_isSome _ _ hsome]
  by_cases ha : a' < b.ownX.length
  · have hN : a' < L.maxBatchSize := ha.trans_le ((length_ownX_le_length b).trans hb)
    have hlt : (τ ⟨a', hN⟩).val < (reqs b).length := by
      rw [length_reqs']
      exact lt_of_ownFlag ((mem_ownIdx b _).1 (List.mem_of_getElem? (h a' hN ha)))
    rw [h a' hN ha]
    unfold RealB.prfsOf prfsW
    simp only [Option.bind_some, List.getElem?_map, List.getElem?_range hlt, List.getElem?_range ha,
      Option.map_some, getElem?_slotList (σ * τ) ha hN]
    rw [dif_pos (τ ⟨a', hN⟩).isLt]
    rfl
  · rw [List.getElem?_eq_none (by rw [length_ownIdx]; omega),
      List.getElem?_eq_none (by simp [prfsW]; omega)]
    rfl

end Proto


/-! ## The theorem -/

section Main

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- a sample from an enumerated type, behind the translation -/
theorem run_drawL_bind {K : ℕ} {β γ : Type} [Fintype β] [Nonempty β] (e : Enum β) (he : e.OK)
    (f : β → Lp lam K L γ) (N₀ δ : ℕ) (st : LSt (spec lam K L)) :
    (virtL N₀ δ ((drawL e).bind f)).run st = (unif β).bind fun a => (virtL N₀ δ (f a)).run st := by
  have h1 : (virtL N₀ δ ((drawL e).bind f)).run st =
      (unif (Fin (e.n + 1))).bind fun r => (virtL N₀ δ (f (e.e r))).run st := rfl
  rw [h1, ← map_unif_equiv (Equiv.ofBijective e.e he), PMF.bind_map]
  rfl

/-- a program, and then a function of its result -/
theorem run_bind_pure {K : ℕ} {β γ : Type} (Q : Lp lam K L β) (f : β → γ)
    (N₀ δ : ℕ) (st : LSt (spec lam K L)) :
    (virtL N₀ δ (Q.bind fun a => LStep.pure (f a))).run st =
      ((virtL N₀ δ Q).run st).map fun y => (f y.1, y.2) := by
  rw [DefC.virtL_bind, DefC.run_bind]
  exact PMF.bind_pure_comp (fun y : β × LSt (spec lam K L) => (f y.1, y.2)) _

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

/-- one execution of Batch on the copy with the tree tr: the honest program, and the reduction's -/
def PLo (tr : TreeH lam) (w : I × L.EncodingRandomness) (fl : ℕ → Bool) (xsl : List (Option X)) :
    Lp lam W.K L (List (Option (OneProtocolProof lam L.onlineBatch))) :=
  proveBL p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩))
    id some embSg W.depthReq [tr] w fl xsl

def PWo (tr : TreeH lam) (os : List (Option (Own L.onlineBatch))) :
    Lp lam W.K L (List (Option (OneProtocolProof lam L.onlineBatch))) :=
  proveBW p.sMT p.sFS Tag.onl L.onlineBatch W.B (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩))
    id some embSg W.depthReq [tr] os

theorem PpJL_some (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (j : ℕ)
    (σ : Equiv.Perm (Fin L.maxBatchSize)) (lf : LeafRec lam L)
    (hl : k.leaves[j]? = some lf) :
    PpJL W WP p k fr xs j σ = (PLo W WP p lf.node.tree (k.i, lf.node.r) (slotFlags σ fr) (slotsOfReq σ xs)).bind fun πs =>
      LStep.pure (RealB.prfsOf j lf.node.tree.root lf.piL σ xs.length πs) := by
  unfold PpJL
  simp only [hl]
  rfl

theorem PpW_some (k : IskH lam L) (xs : List X) (j : ℕ) (ret : BatchLife.BRet L)
    (lf : LeafRec lam L) (hl : k.leaves[j]? = some lf) :
    PpW W p (keyOf k) xs j ret = (PWo W p lf.node.tree (ownsOf xs ret.1 ret.2.1 ret.2.2)).bind fun πs =>
      LStep.pure (prfsW j lf.node.tree.root lf.piL ret.1 xs.length πs) := by
  have hk : (keyOf k)[j]? = some (lf.node.tree, lf.piL) := by simp [keyOf, hl]
  unfold PpW
  simp only [hk]
  rfl

end Main

end EqBatch

open EqBatch in
/-- `Spec.eqProveB` implies `Spec.eqBatchB` (a batch, once the copy is sampled: told in the head).
-/
theorem eqBatchB (hP : Spec.eqProveB) : Spec.eqBatchB := by
  intro I X lam L W WP p N₀ δ k b j lf st _ _ hF hW hG hWP hl _ hlen
  have hblen : b.length ≤ L.maxBatchSize := by simpa [ZKCP.Gen.Batch.pairs] using hlen
  obtain ⟨τ, hτ⟩ := exists_tau b hblen
  -- the left side
  have hleft : ((virtL N₀ δ (PpLJ W WP p k (ownFlag b) (reqs b) j)).run st).map
        (fun z => (replyOf b z.1, z.2)) =
      (unif (Equiv.Perm (Fin L.maxBatchSize))).bind fun σ =>
          ((virtL N₀ δ (PLo W WP p lf.node.tree (k.i, lf.node.r) (slotFlags σ (ownFlag b))
                  ((List.finRange L.maxBatchSize).map (xAt σ (reqs b))))).run st).map fun y =>
                    (replyOf b (RealB.prfsOf j.val lf.node.tree.root lf.piL σ (reqs b).length y.1),
                      y.2) := by
    unfold PpLJ
    rw [run_drawL_bind WP.perm hWP.perm, PMF.map_bind]
    refine congrArg _ (funext fun σ => ?_)
    rw [PpJL_some W WP p k _ _ j.val σ lf hl, run_bind_pure, PMF.map_comp]
    rfl
  -- the right side
  have hright : ((placeB L (fun J xs rest => bsess L.honestOnlineBatchProver (k.i, lf.node.r) (vec J xs rest) J)
        b.ownX).bind fun ret =>
          ((virtL N₀ δ (PpW W p (keyOf k) b.ownX j.val ret)).run st).map fun z =>
            ((.inr z.1 : BIn lam L), z.2)) =
      (unif (Equiv.Perm (Fin L.maxBatchSize))).bind fun σ' =>
          (bsess L.honestOnlineBatchProver (k.i, lf.node.r)
              (vec (slotsOf σ' b.ownX.length) (ownAt σ' b.ownX) fun _ => none)
              (slotsOf σ' b.ownX.length)).bind fun so =>
            ((virtL N₀ δ (PWo W p lf.node.tree
                    (ownsOf b.ownX (slotList σ' b.ownX.length) (slotsOf σ' b.ownX.length) so))).run
                st).map fun y =>
                  ((.inr (prfsW j.val lf.node.tree.root lf.piL (slotList σ' b.ownX.length)
                        b.ownX.length y.1) : BIn lam L),
                    y.2) := by
    unfold placeB
    rw [PMF.bind_bind]
    refine congrArg _ (funext fun σ' => ?_)
    rw [PMF.bind_map]
    refine congrArg _ (funext fun so => ?_)
    show ((virtL N₀ δ
          (PpW W p (keyOf k) b.ownX j.val
            (slotList σ' b.ownX.length, ⟨slotsOf σ' b.ownX.length, so⟩))).run st).map _ = _
    rw [PpW_some W p k _ j.val _ lf hl, run_bind_pure, PMF.map_comp]
    rfl
  have hchg : ∀ {γ : Type} (G : Equiv.Perm (Fin L.maxBatchSize) → PMF γ),
      (unif (Equiv.Perm (Fin L.maxBatchSize))).bind G =
        (unif (Equiv.Perm (Fin L.maxBatchSize))).bind fun σ => G (σ * τ) := by
    intro γ G
    conv_lhs => rw [← map_unif_equiv (Equiv.mulRight τ)]
    rw [PMF.bind_map]
    rfl
  rw [hleft, hright]
  refine Eq.trans ?_ (hchg _).symm
  refine congrArg _ (funext fun σ => ?_)
  show _ = (bsess L.honestOnlineBatchProver (k.i, lf.node.r)
      (vec (slotsOf (σ * τ) b.ownX.length) (ownAt (σ * τ) b.ownX) fun _ => none)
      (slotsOf (σ * τ) b.ownX.length)).bind _
  have h1 := hP I X lam W.K L p.sMT p.sFS Tag.onl X _ L.onlineBatch _ L.honestOnlineBatchProver W.B WP.B
    (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩)) id some embSg W.depthReq [lf.node.tree] N₀ δ L.maxBatchSize
    (k.i, lf.node.r) (slotFlags σ (ownFlag b)) (xAt σ (reqs b)) st hW.B.sh hG.B hWP.B hF
  rw [ownSlots_eq hτ σ] at h1
  have h2 : bsess L.honestOnlineBatchProver (k.i, lf.node.r) (xAt σ (reqs b)) (slotsOf (σ * τ) b.ownX.length) =
      bsess L.honestOnlineBatchProver (k.i, lf.node.r)
        (vec (slotsOf (σ * τ) b.ownX.length) (ownAt (σ * τ) b.ownX) fun _ => none)
        (slotsOf (σ * τ) b.ownX.length) :=
    (congrArg (fun y => bsess L.honestOnlineBatchProver (k.i, lf.node.r) y (slotsOf (σ * τ) b.ownX.length))
        (xAt_eq_vec hτ σ)).trans
      (BatchLife.bsess_vec_congr _ _ _ _ _ _)
  rw [h2] at h1
  unfold PLo
  rw [h1, PMF.map_bind]
  refine congrArg _ (funext fun so => ?_)
  rw [osOf_eq_ownsOf hτ σ so]
  refine congrArg (fun f => PMF.map f _) (funext fun y => ?_)
  rw [replyOf_prfsOf hτ hblen σ]

end Compile.Batch
