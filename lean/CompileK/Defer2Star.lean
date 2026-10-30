-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/Defer2Star.lean: the committer and the prover of the scheme with batches, for the lemma on
deferred programming of the random oracle (`Spec.defer2`, CompileK/SpecDefer2.lean). The committer
and the prover of the scheme with batches obey the discipline with joint charges (`SafeO2`), if one
execution of the compiled prover does (`Spec.safeProveB2`); each under the hypotheses of its
statement (`Spec.safeCB2`, `Spec.safePB2`).

Definitions (`Spec.safeProveB2`, `IskOKB2`, `Spec.safeCB2`, `Spec.safePB2`) and the analogues for
`SafeO2` (CompileK/Defer2Safe.lean) of the theorems of Compile/Batch/DisciplineStar.lean;
`safeCB2_of`, `safePB2_of`. Nothing assumed beyond the hypotheses of the statements and whatever the
arguments hold as proofs.

Against `Spec.safeProveB` (Compile/Batch/DisciplineStar.lean), `Spec.safeCB`, `Spec.safePB`
(Compile/Batch/SpecDiscipline.lean): `Spec.safeProveB2` has the parameter mG and the premise maxMore
Q.loc.shape Q.ann wq.sh ≤ mG (no loop of the execution has more than mG later tries);
`Spec.safeCB2`, `Spec.safePB2` are stated at mG := maxMoreB W (Compile/Batch/Counts.lean: the
scheme's own largest number): that premise is not left in them. A premise that stays in both,
`TidyBoth p (maxMoreB W) d` (CompileK/Defer2Tree.lean), still speaks of later tries: its one clause
that reads mG (`TidyO.point`, Compile/Batch/SpecDiscipline.lean, at `rulesT`) says that every marked
evaluation in the start state d stands at an oracle of `osBG (maxMoreB W)`: one of the ten of `osB`,
or a name `OracleName.fbw t k` for a later try with k < maxMoreB W.

Words used in this file. The discipline with joint charges, orderly both ways, both ways: the
paragraph "Words used in this file." of CompileK/Defer2Chain.lean's head holds here too.

Terms: lean/GLOSSARY.md.
-/
import CompileK.Defer2E
import Compile.Batch.DisciplineStar

set_option autoImplicit false

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc (Rules TreeTok TreeNew)

/-- States, if no loop of the execution has more than mG later tries: one execution of the compiled
prover obeys the rules, from every state that is orderly both ways in which the handles of the trees
over the external oracles can be revealed, both ways, if the chains cannot join (`joins` = 0) or
there are 2^depthReq slots. Its marked evaluations hold only tokens that it has made; it shows only
such tokens and handles of the given trees; it makes no plain evaluation. -/
def Spec.safeProveB2 : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (p : Params) (mG : ℕ) (t : Tag) (Y : Type) (E : ExtSpec)
    (Q : BatchInteractiveOracleProof Y E) (Wt : Type) (H : BatchHonestProver Q Wt)
    (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
    (embS : (q : OPos Q.loc.shape) → OSym Q.loc.shape q → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t))
    (xin : Y → Option X) (depthReq : ℕ) (trees : List (TreeH lam)) (w : Wt)
    (fl : ℕ → Bool) (xs : List (Option Y)) (d : DSt (spec lam K L)),
    TidyBoth p mG d → (∀ tr ∈ trees, TreeOKB2 d tr) →
    (joins Q.loc.shape Q.ann = 0 ∨ xs.length = 2 ^ depthReq) →
    maxMore Q.loc.shape Q.ann wq.sh ≤ mG →
    SafeO2 (rulesT K L lam p mG) Jt (ellT lam) (proveB p.sMT p.sFS t Q H wq wp embS embP xin depthReq trees w fl xs) d fun _ d' =>
      TidyBoth p mG d' ∧
      GrowsO (fun _ => False) (fun u => ∃ tr ∈ trees, TreeTok tr u) (fun _ => 0)
        (mProveB t Q.loc.shape Q.ann wq.sh xs.length) d d'

/-- The handles of isk (`IskH`, Compile/Batch/Star.lean) can be revealed, both ways. -/
def IskOKB2 {I X : Type} {lam : ℕ} {L : BatchProtocol I X} {K : ℕ} (d : DSt (spec lam K L)) (k : IskH lam L) :
    Prop :=
  TreeOKB2 d k.root.tree ∧ ∀ lf ∈ k.leaves, TreeOKB2 d lf.node.tree

/-- States, under the hypothesis below: the committer obeys the discipline with joint charges. -/
def Spec.safeCB2 : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (i : I) (d : DSt (spec lam W.K L)),
    TidyBoth p (maxMoreB W) d →
    SafeO2 (rulesT W.K L lam p (maxMoreB W)) Jt (ellT lam) (Cp W WP p i) d fun out d' =>
      TidyBoth p (maxMoreB W) d' ∧
      IskOKB2 d' out.2 ∧
      GrowsO (fun _ => False) (fun _ => False) (eCB W p) (mCB W p) d d'

/-- States, under the hypotheses below: the prover obeys the discipline with joint charges. -/
def Spec.safePB2 : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (d : DSt (spec lam W.K L)),
    L.maxBatchSize = 2 ^ W.depthReq → TidyBoth p (maxMoreB W) d → IskOKB2 d k →
    SafeO2 (rulesT W.K L lam p (maxMoreB W)) Jt (ellT lam) (Pp W WP p k fr xs) d fun _ d' =>
      TidyBoth p (maxMoreB W) d' ∧
      IskOKB2 d' k ∧
      GrowsO (fun _ => False) (IskTokB k) ePB (mPB W) d d'

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L)
  (WP : WireBP L) (p : Params) {mG : ℕ}

/-- One encoded index with its tree. -/
theorem safe2_nodeP' (i : I) {d : DSt (spec lam W.K L)} (hd : TidyBoth p mG d) :
    SafeO2 (rulesT W.K L lam p mG) Jt (ellT lam) (nodeP' W WP p i) d fun nd d' =>
      TidyBoth p mG d' ∧
      GrowsO NoTok NoTok (eNodeB W) (mNodeB W) d d' ∧
      TreeOKB2 d' nd.tree ∧
      TreeNew d.vals.length nd.tree := by
  unfold nodeP'
  refine SafeO2.bind _ _ d ?_
  refine fun rr => ?_
  have hfun : (fun j =>
        ((if h : j < L.wordLength then (some (.inl (L.encodeIndex i (WP.ri.e rr) ⟨j, h⟩)), true)
          else (none, false) : Body L × Bool)).2) =
      fun j => decide (j < L.wordLength) := funext fun j => by
    by_cases h : j < L.wordLength
    · rw [dif_pos h, decide_eq_true h]
    · rw [dif_neg h, decide_eq_false h]
  change SafeO2 _ _ _ (Step.bind _ _) d _
  refine SafeO2.bind _ _ d (SafeO2.mono ?_ _ d (safe2_commitE W.depth _ hd))
  rintro t d₁ ⟨hd₁, hg₁, h3, h4⟩
  rw [hfun] at hg₁
  exact ⟨hd₁, hg₁, h3, h4⟩

variable (hB : Spec.safeProveB2)
include hB

/-- The compiled test. -/
theorem safe2_proveT (hmT : maxMore L.offline.shape _ W.T.sh ≤ mG) (tree : TreeH lam) (i : I)
    (r : L.EncodingRandomness) {d : DSt (spec lam W.K L)} (hd : TidyBoth p mG d) (ht : TreeOKB2 d tree) :
    SafeO2 (rulesT W.K L lam p mG) Jt (ellT lam) (proveT W WP p tree i r) d fun _ d' =>
      TidyBoth p mG d' ∧
      GrowsO NoTok (TreeTok tree) zr (mProveB Tag.test L.offline.shape _ W.T.sh 1) d d' := by
  unfold proveT
  refine SafeO2.bind _ _ d
    (SafeO2.mono ?_ _ d
      (hB I X lam W.K L p mG Tag.test _ _ (BatchInteractiveOracleProof.ofProto L.offline) _ (BatchHonestProver.ofHonest L.honestOfflineProver)
        W.T WP.T _ id (fun _ => none) W.depthReq [tree] (i, r) (fun _ => true) [some ()] d hd
        (fun tr htr => by rw [List.mem_singleton.mp htr]; exact ht)
        (Or.inl (Star.joins_allLocal _)) hmT))
  rintro l d₁ ⟨hd₁, hg₁⟩
  exact ⟨hd₁,
    hg₁.mono (fun _ h => Or.inl h)
      (fun u ⟨tr, htr, hu⟩ => Or.inl (by rw [List.mem_singleton.mp htr] at hu; exact hu))
      (fun _ => le_rfl) (fun _ => le_rfl)⟩

/-- A compiled link. -/
theorem safe2_proveLk (hmL : maxMore L.link.shape _ W.Lk.sh ≤ mG) (root tree : TreeH lam)
    (i : I) (r₀ r : L.EncodingRandomness) {d : DSt (spec lam W.K L)} (hd : TidyBoth p mG d)
    (hr : TreeOKB2 d root) (ht : TreeOKB2 d tree) :
    SafeO2 (rulesT W.K L lam p mG) Jt (ellT lam) (proveLk W WP p root tree i r₀ r) d fun _ d' =>
      TidyBoth p mG d' ∧
      GrowsO NoTok (fun u => TreeTok root u ∨ TreeTok tree u) zr
          (mProveB Tag.link L.link.shape _ W.Lk.sh 1) d d' := by
  unfold proveLk
  refine SafeO2.bind _ _ d
    (SafeO2.mono ?_ _ d
      (hB I X lam W.K L p mG Tag.link _ _ (BatchInteractiveOracleProof.ofProto L.link) _
        (BatchHonestProver.ofHonest L.honestLinkProver) W.Lk WP.Lk _ id
    (fun _ => none) W.depthReq [root, tree] (i, r₀, r) (fun _ => true)
    [some ()] d hd (fun tr htr => by
      rcases List.mem_cons.mp htr with rfl | htr
      · exact hr
      · rw [List.mem_singleton.mp htr]; exact ht)
    (Or.inl (Star.joins_allLocal _)) hmL))
  rintro l d₁ ⟨hd₁, hg₁⟩
  refine ⟨hd₁,
    hg₁.mono (fun _ h => Or.inl h) (fun u ⟨tr, htr, hu⟩ => Or.inl ?_)
      (fun _ => le_rfl) (fun _ => le_rfl)⟩
  rcases List.mem_cons.mp htr with rfl | htr
  · exact Or.inl hu
  · rw [List.mem_singleton.mp htr] at hu
    exact Or.inr hu

/-- The leaves of the star, each with its link to the root. -/
theorem safe2_leavesC (hmL : maxMore L.link.shape _ W.Lk.sh ≤ mG) (i : I) (root : Node lam L) :
    ∀ (n : ℕ) (d : DSt (spec lam W.K L)), TidyBoth p mG d → TreeOKB2 d root.tree →
    SafeO2 (rulesT W.K L lam p mG) Jt (ellT lam) (leavesC W WP p i root n) d fun out d' =>
      TidyBoth p mG d' ∧
      GrowsO NoTok (TreeTok root.tree) (fun o => n * eNodeB W o)
        (fun o => n * (mNodeB W o + mProveB Tag.link L.link.shape _ W.Lk.sh 1 o)) d d' ∧
      ∀ lf ∈ out, TreeOKB2 d' lf.node.tree ∧ TreeNew d.vals.length lf.node.tree
  | 0, d, hd, _ => ⟨hd, GrowsO.refl d, fun _ h => absurd h (List.not_mem_nil)⟩
  | n + 1, d, hd, hr => by
      rw [leavesC]
      refine SafeO2.bind _ _ d (SafeO2.mono ?_ _ d (safe2_nodeP' W WP p i hd))
      rintro nd d₁ ⟨hd₁, hg₁, hnd, hnew⟩
      have hr₁ := hr.grows hg₁ (fun _ _ h => h)
      refine SafeO2.bind _ _ d₁
        (SafeO2.mono ?_ _ d₁
          (safe2_proveLk W WP p hB hmL root.tree nd.tree i root.r nd.r hd₁ hr₁ hnd))
      rintro π d₂ ⟨hd₂, hg₂⟩
      refine SafeO2.bind _ _ d₂
        (SafeO2.mono ?_ _ d₂ (safe2_leavesC hmL i root n d₂ hd₂ (hr₁.grows hg₂ (fun _ _ h => h))))
      rintro rest d₃ ⟨hd₃, hg₃, hrest⟩
      have hg₀₂ := (hg₁.mono (Ch := NoTok) (R := TreeTok root.tree) (fun _ h => h.elim)
        (fun _ h => h.elim) (fun _ => le_rfl)
        (fun _ => le_rfl)).trans hg₂ (e := eNodeB W) (M := fun o => mNodeB W o + mProveB Tag.link L.link.shape _ W.Lk.sh 1 o) (fun _ h => h.elim)
        (fun v hv => by
          rcases hv with hv | hv
          · exact Or.inl hv
          · exact Or.inr (hnew v hv)) (fun _ => le_rfl) (fun _ => le_rfl)
      refine ⟨hd₃,
        hg₀₂.trans hg₃ (fun _ h => h.elim) (fun _ h => Or.inl h)
          (fun o => by rw [Nat.succ_mul, Nat.add_comm])
          (fun o => by rw [Nat.succ_mul, Nat.add_comm]),
        ?_⟩
      intro lf hlf
      rcases List.mem_cons.mp hlf with rfl | hlf
      · exact ⟨(hnd.grows hg₂ (fun _ _ h => h)).grows hg₃ (fun _ _ h => h), hnew⟩
      · exact ⟨(hrest lf hlf).1, fun v hv => le_trans hg₀₂.length_le ((hrest lf hlf).2 v hv)⟩

omit W WP p in
/-- The committer obeys the rules, under the hypotheses of `Spec.safeCB2`, if `hB`. -/
theorem safeCB2_of : Spec.safeCB2 := by
  intro I X lam L W WP p i d hd
  unfold Cp
  refine SafeO2.bind _ _ d (SafeO2.mono ?_ _ d (safe2_nodeP' W WP p i hd))
  rintro root d₁ ⟨hd₁, hg₁, hroot, hnew⟩
  refine SafeO2.bind _ _ d₁
    (SafeO2.mono ?_ _ d₁ (safe2_proveT W WP p hB (le_max_left _ _) root.tree i root.r hd₁ hroot))
  rintro πT d₂ ⟨hd₂, hg₂⟩
  have hroot₂ := hroot.grows hg₂ (fun _ _ h => h)
  refine SafeO2.bind _ _ d₂
    (SafeO2.mono ?_ _ d₂
      (safe2_leavesC W WP p hB (le_trans (le_max_left _ _) (le_max_right _ _)) i root
        (p.M + 1) d₂ hd₂ hroot₂))
  rintro ls d₃ ⟨hd₃, hg₃, hls⟩
  have hg₀₂ := hg₁.trans hg₂ (e := eNodeB W)
    (M := fun o => mNodeB W o + mProveB Tag.test L.offline.shape _ W.T.sh 1 o) (fun _ h => h.elim)
    (fun v hv => Or.inr (hnew v hv)) (fun _ => le_rfl) (fun _ => le_rfl)
  exact ⟨hd₃,
    ⟨hroot₂.grows hg₃ (fun _ _ h => h), fun lf hlf => (hls lf hlf).1⟩,
    hg₀₂.trans hg₃ (fun _ h => h.elim) (fun v hv => Or.inr (hnew v hv))
      (fun _ => le_rfl) (fun _ => le_rfl)⟩

omit W WP p in
/-- The prover obeys the rules, under the hypotheses of `Spec.safePB2`, if `hB`. -/
theorem safePB2_of : Spec.safePB2 := by
  intro I X lam L W WP p k fr xs d hN hd hk
  unfold Pp
  refine fun j => ?_
  refine SafeO2.bind _ _ d ?_
  refine fun rσ => ?_
  change SafeO2 _ _ _ (PpJ W WP p k fr xs j.val (WP.perm.e rσ)) d _
  unfold PpJ
  split
  · exact ⟨hd, hk, GrowsO.refl d⟩
  · rename_i lf hj
    have hmem : lf ∈ k.leaves := List.mem_of_getElem? hj
    have hlen : (slotsOfReq (WP.perm.e rσ) xs).length = L.maxBatchSize := by simp [slotsOfReq]
    refine SafeO2.bind _ _ d
      (SafeO2.mono ?_ _ d
        (hB I X lam W.K L p (maxMoreB W) Tag.onl _ _ L.onlineBatch _ L.honestOnlineBatchProver W.B WP.B _ id some W.depthReq
          [lf.node.tree] (k.i, lf.node.r) (slotFlags (WP.perm.e rσ) fr)
          (slotsOfReq (WP.perm.e rσ) xs) d hd
          (fun tr htr => by rw [List.mem_singleton.mp htr]; exact hk.2 lf hmem)
          (Or.inr (hlen.trans hN)) (le_trans (le_max_right _ _) (le_max_right _ _))))
    rintro πs d₁ ⟨hd₁, hg₁⟩
    rw [hlen] at hg₁
    exact ⟨hd₁,
      ⟨hk.1.grows hg₁ (fun _ _ h => h), fun lf' h' => (hk.2 lf' h').grows hg₁ (fun _ _ h => h)⟩,
      hg₁.mono (fun _ h => h.elim) (fun v ⟨tr, htr, hv⟩ => by
        rw [List.mem_singleton.mp htr] at hv
        exact Or.inl (Or.inr ⟨lf, hmem, hv⟩)) (fun _ => le_rfl) (fun _ => le_rfl)⟩


end Compile.Batch.Disc
