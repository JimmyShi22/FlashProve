-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Late4.lean: the committer and the prover of the scheme with batches and their late
forms (their forms in `LStep`: `CpL`, `PpL`, Compile/Batch/Mirror.lean), under the hypotheses of
their statements, are related by `Rom.Late`: proofs of `Spec.lateCpB` and `Spec.latePpB`
(Compile/Batch/SpecLate.lean; words of this library: lean/GLOSSARY.md).

The rounds may have proof-of-work bits (`W.OKG`). Of the record `GrFitPB`
(Compile/Batch/SpecFit.lean) one clause is used, `readsPut`, for each of the three protocols
(`ReadsPut`; `lateCp_of`, `latePp_of` take this clause alone): the prover opens the positions that
the verifier reads at the plain parts with the nonces written in, and the late form knows the
symbols at the positions read at the plain parts as the interactive prover sends them.
-/
import Compile.Batch.SpecLate

noncomputable section

namespace Compile.Batch
open Iop Rom

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

theorem ExtK.ext {K : ℕ} {Γ Γ' : Cx lam K L} {n n' : ℕ} {body : ℕ → Body L}
    {salts : List (Option (Tok × Tok))} (h : ExtK Γ n body salts) (hE : Ext n Γ Γ') (hn : n ≤ n') :
    ExtK Γ' n' body salts := fun j s d hs => by
  obtain ⟨h1, h2, h3, h4⟩ := h j s d hs
  exact ⟨h1.ext hE h3, h2.ext hE h4, by omega, by omega⟩

theorem not_hasSh_allLocal : ∀ s : Shape, ¬ HasSh s (RoundSplits.allLocal s)
  | [] => fun h => h
  | _ :: s => fun h => h.elim (fun e => by cases e) (not_hasSh_allLocal s)

/-- The positions that the verifier reads do not depend on the nonces (the clause `readsPut` of
`GrFitP`, Compile/Batch/SpecFit.lean). -/
def ReadsPut {K : ℕ} {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) (wq : ProtocolQueryLayout lam K Q) : Prop :=
  ∀ x ρ pl ph nJ n0, Q.loc.reads x ρ (putB Q.loc.shape Q.ann wq.sh ph nJ n0 pl) = Q.loc.reads x ρ pl

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

theorem late_nodeP' (i : I) {n : ℕ} {Γ : Cx lam W.K L} (hF : Fut n Γ) :
    Late (fun n' Γ' a b =>
        a = b ∧ n ≤ n' ∧ Fut n' Γ' ∧ (∀ t, t < n → Γ' t = Γ t) ∧
        ExtK Γ' n' (encBody i a.r) a.tree.salts)
      n Γ (nodeP' W WP p i) (nodeLL W WP p) := by
  refine Late.sample fun rr => ?_
  have h0 := late_commitE (K := W.K) p.sMT W.depth
    (fun j =>
      if h : j < L.wordLength then ((some (.inl (L.encodeIndex i (WP.ri.e rr) ⟨j, h⟩)) : Body L), true)
      else (none, false))
    (fun j hj => by by_cases h : j < L.wordLength <;> simp [h] at hj ⊢) hF
  have e1 : (fun j =>
        (if h : j < L.wordLength then ((some (.inl (L.encodeIndex i (WP.ri.e rr) ⟨j, h⟩)) : Body L), true)
          else (none, false)).2) =
      fun j => decide (j < L.wordLength) :=
    funext fun j => by by_cases h : j < L.wordLength <;> simp [h]
  have e2 : (fun j =>
        (if h : j < L.wordLength then ((some (.inl (L.encodeIndex i (WP.ri.e rr) ⟨j, h⟩)) : Body L), true)
          else (none, false)).1) =
      encBody i (WP.ri.e rr) :=
    funext fun j => by unfold encBody; by_cases h : j < L.wordLength <;> simp [h]
  rw [e1] at h0
  simp only [e2] at h0
  refine Late.bind h0 fun n' Γ' t t' h => Late.pure ?_
  obtain ⟨rfl, a1, hF', fr, hK⟩ := h
  exact ⟨rfl, a1, hF', fr, hK⟩

theorem late_proveT (hL : L.Wired) (hW : W.OKG) (hR : ReadsPut (BatchInteractiveOracleProof.ofProto L.offline) W.T)
    (tree : TreeH lam) (i : I) (r : L.EncodingRandomness) {n : ℕ} {Γ : Cx lam W.K L} (hF : Fut n Γ)
    (hK : ExtK Γ n (encBody i r) tree.salts) :
    Late (fun n' Γ' a b => a = b ∧ n ≤ n' ∧ Fut n' Γ' ∧ Ext n Γ Γ') n Γ
      (proveT W WP p tree i r) (proveTL W WP p tree i r) := by
  refine Late.bind
    (late_proveB p.sMT p.sFS Tag.test (BatchInteractiveOracleProof.ofProto L.offline) (BatchHonestProver.ofHonest L.honestOfflineProver)
      W.T WP.T _ id (fun _ => none) embSg W.depthReq [tree] (i, r) hW.T.sh
      (Iop.BatchOne.BAnn.allLocal_coherent _) hR (fun _ => true) [some ()] hF
      (fun h => absurd h (not_hasSh_allLocal _)) Nat.one_le_two_pow fun q s d hs => ?_)
    fun n' Γ' l l' h => Late.pure ⟨by rw [h.1], h.2⟩
  obtain ⟨e1, e2⟩ := hW.extT q
  rw [e1, e2] at hs
  have := hK q.val s d hs
  have hb : encBody i r q.val =
      embSg ((oneExternalString L.wordLength L.Symbol).rd ((BatchHonestProver.ofHonest L.honestOfflineProver).ext (i, r)) q) := by
    show _ = embSg ((oneExternalString L.wordLength L.Symbol).rd (L.honestOfflineProver.ext (i, r)) q)
    rw [hL.extT]
    unfold encBody
    rw [dif_pos q.2]
    rfl
  rw [hb] at this
  exact this

theorem late_proveLk (hL : L.Wired) (hW : W.OKG) (hR : ReadsPut (BatchInteractiveOracleProof.ofProto L.link) W.Lk)
    (root tree : TreeH lam) (i : I) (r₀ r : L.EncodingRandomness) {n : ℕ} {Γ : Cx lam W.K L} (hF : Fut n Γ)
    (hK0 : ExtK Γ n (encBody i r₀) root.salts) (hK : ExtK Γ n (encBody i r) tree.salts) :
    Late (fun n' Γ' a b => a = b ∧ n ≤ n' ∧ Fut n' Γ' ∧ Ext n Γ Γ') n Γ
      (proveLk W WP p root tree i r₀ r) (proveLkL W WP p root tree i r₀ r) := by
  refine Late.bind
    (late_proveB p.sMT p.sFS Tag.link (BatchInteractiveOracleProof.ofProto L.link) (BatchHonestProver.ofHonest L.honestLinkProver)
      W.Lk WP.Lk _ id (fun _ => none) embSg W.depthReq [root, tree] (i, r₀, r) hW.Lk.sh
      (Iop.BatchOne.BAnn.allLocal_coherent _) hR (fun _ => true) [some ()] hF
      (fun h => absurd h (not_hasSh_allLocal _)) Nat.one_le_two_pow fun q s d hs => ?_)
    fun n' Γ' l l' h => Late.pure ⟨by rw [h.1], h.2⟩
  have hext : (BatchHonestProver.ofHonest L.honestLinkProver).ext (i, r₀, r) = (L.encodeIndex i r₀, L.encodeIndex i r) := hL.extL i r₀ r
  rw [hext]
  rcases q with q | q
  · obtain ⟨e1, e2⟩ := hW.extL.1 q
    rw [e1, e2] at hs
    have := hK0 q.val s d hs
    have hb : encBody i r₀ q.val = embSg ((twoExternalStrings L.wordLength L.Symbol).rd (L.encodeIndex i r₀, L.encodeIndex i r) (.inl q)) := by
      unfold encBody
      rw [dif_pos q.2]
      rfl
    rw [hb] at this
    exact this
  · obtain ⟨e1, e2⟩ := hW.extL.2 q
    rw [e1, e2] at hs
    have := hK q.val s d hs
    have hb : encBody i r q.val = embSg ((twoExternalStrings L.wordLength L.Symbol).rd (L.encodeIndex i r₀, L.encodeIndex i r) (.inr q)) := by
      unfold encBody
      rw [dif_pos q.2]
      rfl
    rw [hb] at this
    exact this

theorem late_leavesC (hL : L.Wired) (hW : W.OKG) (hR : ReadsPut (BatchInteractiveOracleProof.ofProto L.link) W.Lk)
    (i : I) (root : Node lam L) :
    ∀ (m n : ℕ) (Γ : Cx lam W.K L), Fut n Γ → ExtK Γ n (encBody i root.r) root.tree.salts →
      Late (fun n' Γ' a b =>
          a = b ∧ n ≤ n' ∧ Fut n' Γ' ∧ Ext n Γ Γ' ∧
          ∀ lf ∈ a, ExtK Γ' n' (encBody i lf.node.r) lf.node.tree.salts)
        n Γ (leavesC W WP p i root m) (leavesCL W WP p i root m)
  | 0, n, Γ, hF, _ => Late.pure ⟨rfl, le_rfl, hF, Ext.refl n Γ, fun lf h => absurd h (by simp)⟩
  | m + 1, n, Γ, hF, hK0 => by
      refine Late.bind (late_nodeP' W WP p i hF) fun n1 Γ1 nd nd' h1 => ?_
      obtain ⟨rfl, a1, hF1, fr1, hK1⟩ := h1
      have hE1 : Ext n Γ Γ1 := Ext.of_frame fr1
      refine Late.bind
        (late_proveLk W WP p hL hW hR root.tree nd.tree i root.r nd.r hF1 (hK0.ext hE1 a1) hK1)
        fun n2 Γ2 π π' h2 => ?_
      obtain ⟨rfl, a2, hF2, hE2⟩ := h2
      refine Late.bind (late_leavesC hL hW hR i root m n2 Γ2 hF2 ((hK0.ext hE1 a1).ext hE2 a2))
        fun n3 Γ3 rest rest' h3 => Late.pure ?_
      obtain ⟨rfl, a3, hF3, hE3, hK3⟩ := h3
      refine ⟨rfl, by omega, hF3, (hE1.trans hE2 a1).trans hE3 (by omega), fun lf hlf => ?_⟩
      rcases List.mem_cons.1 hlf with rfl | hlf
      · exact (hK1.ext hE2 a2).ext hE3 a3
      · exact hK3 lf hlf

/-- Under the hypotheses below (among them `W.OKG`, and `ReadsPut` for Test and for Link in place of
`GrFitPB`): the committer and its late form are related by `Late`. -/
theorem lateCp_of (i : I) (n : ℕ) (Γ : Cx lam W.K L) (hL : L.Wired) (hW : W.OKG)
    (hRT : ReadsPut (BatchInteractiveOracleProof.ofProto L.offline) W.T)
    (hRL : ReadsPut (BatchInteractiveOracleProof.ofProto L.link) W.Lk) (hF : Fut n Γ) :
    Late (fun n' Γ' a b => a = b ∧ n ≤ n' ∧ Fut n' Γ' ∧ Ext n Γ Γ' ∧ IskK Γ' n' a.2) n Γ
      (Cp W WP p i) (CpL W WP p i) := by
  refine Late.bind (late_nodeP' W WP p i hF) fun n1 Γ1 root root' h1 => ?_
  obtain ⟨rfl, a1, hF1, fr1, hK1⟩ := h1
  have hE1 : Ext n Γ Γ1 := Ext.of_frame fr1
  refine Late.bind (late_proveT W WP p hL hW hRT root.tree i root.r hF1 hK1)
    fun n2 Γ2 πT πT' h2 => ?_
  obtain ⟨rfl, a2, hF2, hE2⟩ := h2
  refine Late.bind (late_leavesC W WP p hL hW hRL i root (p.M + 1) n2 Γ2 hF2 (hK1.ext hE2 a2))
    fun n3 Γ3 ls ls' h3 => Late.pure ?_
  obtain ⟨rfl, a3, hF3, hE3, hK3⟩ := h3
  exact ⟨rfl, by omega, hF3, (hE1.trans hE2 a1).trans hE3 (by omega), hK3⟩

/-- Under the hypotheses below (among them `W.OKG`, and `ReadsPut` for Batch in place of `GrFitPB`):
the prover and its late form are related by `Late`. -/
theorem latePp_of (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (n : ℕ) (Γ : Cx lam W.K L)
    (hL : L.Wired) (hW : W.OKG) (hRB : ReadsPut L.onlineBatch W.B) (hA : L.onlineBatch.ann.Coherent)
    (hF : Fut n Γ) (hK : IskK Γ n k) :
    Late (fun n' Γ' a b => a = b ∧ n ≤ n' ∧ Fut n' Γ' ∧ Ext n Γ Γ') n Γ
      (Pp W WP p k fr xs) (PpL W WP p k fr xs) := by
  refine Late.sample fun j => Late.sample fun rσ => ?_
  show Late _ n Γ (PpJ W WP p k fr xs j.val (WP.perm.e rσ))
    (PpJL W WP p k fr xs j.val (WP.perm.e rσ))
  unfold PpJ PpJL
  cases hj : k.leaves[j.val]? with
  | none => exact Late.pure ⟨rfl, le_rfl, hF, Ext.refl n Γ⟩
  | some lf =>
    have hlen : (slotsOfReq (WP.perm.e rσ) xs).length = 2 ^ W.depthReq := by
      unfold slotsOfReq
      rw [List.length_map, List.length_finRange, hW.slots]
    refine Late.bind
      (late_proveB p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ id some embSg W.depthReq [lf.node.tree]
        (k.i, lf.node.r) hW.B.sh hA hRB (slotFlags (WP.perm.e rσ) fr) (slotsOfReq (WP.perm.e rσ) xs)
        hF (fun _ => hlen) (le_of_eq hlen) fun q s d hs => ?_)
      fun n' Γ' πs πs' h => Late.pure ⟨by rw [h.1], h.2⟩
    obtain ⟨e1, e2⟩ := hW.extB q
    rw [e1, e2] at hs
    have := hK lf (List.mem_of_getElem? hj) q.val s d hs
    have hb : encBody k.i lf.node.r q.val =
        embSg ((oneExternalString L.wordLength L.Symbol).rd (L.honestOnlineBatchProver.ext (k.i, lf.node.r)) q) := by
      rw [hL.extB]
      unfold encBody
      rw [dif_pos q.2]
      rfl
    rw [hb] at this
    exact this

theorem lateCpB : Spec.lateCpB := fun _ _ _ _ W WP p i n Γ hL hW hG hF =>
  lateCp_of W WP p i n Γ hL hW hG.T.readsPut hG.Lk.readsPut hF

theorem latePpB : Spec.latePpB := fun _ _ _ _ W WP p k fr xs n Γ hL hW hG hA hF hK =>
  latePp_of W WP p k fr xs n Γ hL hW hG.B.readsPut hA hF hK

end Compile.Batch
