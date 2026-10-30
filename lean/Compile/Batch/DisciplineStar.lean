-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/DisciplineStar.lean: that committer and prover of the compiled scheme obey the rules
of deferred programming (`Spec.safeCB`, `Spec.safePB`) follows from `Spec.safeProveB` (words of this
library: lean/GLOSSARY.md).

The two statements are in Compile/Batch/SpecDiscipline.lean; `Spec.safeProveB`, on one execution of
the compiled prover, is below. Also used: the lemmas on the trees over encoded indices
(Compile/Batch/DisciplineE.lean).

Main names:
  `safe_proveT`, `safe_proveLk`  the compiled provers of Test and of Link
  `safe_leavesC`  the copies
  `safeCB_of`, `safePB_of`  the committer, one batch of the prover
-/
import Compile.Batch.DisciplineE

namespace Compile.Batch.Disc
open Iop Rom
open Compile.Disc (Rules TreeTok TreeNew)

/-- One execution of the compiled prover obeys the rules, from every orderly state in which the
handles of the trees over the external strings can be revealed, if no round is shared (`joins` = 0)
or there are 2^depthReq slots. Its marked queries hold only tokens that it has made; it shows only
such tokens and handles of the given trees; it makes no ordinary query. -/
def Spec.safeProveB : Prop :=
  ∀ (I X : Type) (lam K : ℕ) (L : BatchProtocol I X) (p : Params) (t : Tag) (Y : Type) (E : ExtSpec)
    (Q : BatchInteractiveOracleProof Y E) (Wt : Type) (H : BatchHonestProver Q Wt)
    (wq : ProtocolQueryLayout lam K Q) (wp : WirePB Q H)
    (embS : (q : OPos Q.loc.shape) → OSym Q.loc.shape q → Body L)
    (embP : PlainPart Q.loc.shape Q.ann → PlainPart (shapeOf L t) (annOf L t))
    (xin : Y → Option X) (depthReq : ℕ) (trees : List (TreeH lam)) (w : Wt)
    (fl : ℕ → Bool) (xs : List (Option Y)) (d : DSt (spec lam K L)),
    TidyO (rulesB K L lam p) d → (∀ tr ∈ trees, TreeOKB d tr) →
    (joins Q.loc.shape Q.ann = 0 ∨ xs.length = 2 ^ depthReq) →
    SafeO (rulesB K L lam p) (proveB p.sMT p.sFS t Q H wq wp embS embP xin depthReq trees w fl xs) d fun _ d' =>
      TidyO (rulesB K L lam p) d' ∧
      GrowsO (fun _ => False) (fun u => ∃ tr ∈ trees, TreeTok tr u) (fun _ => 0)
        (mProveB t Q.loc.shape Q.ann wq.sh xs.length) d d'

theorem Star.joins_allLocal : ∀ s : Shape, joins s (RoundSplits.allLocal s) = 0
  | [] => rfl
  | _ :: s => Star.joins_allLocal s

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

/-- One encoded index with its tree. -/
theorem safe_nodeP' (i : I) {d : DSt (spec lam W.K L)} (hd : TidyO (rulesB W.K L lam p) d) :
    SafeO (rulesB W.K L lam p) (nodeP' W WP p i) d fun nd d' =>
      TidyO (rulesB W.K L lam p) d' ∧
      GrowsO NoTok NoTok (eNodeB W) (mNodeB W) d d' ∧
      TreeOKB d' nd.tree ∧
      TreeNew d.vals.length nd.tree := by
  unfold nodeP'
  refine SafeO.bind _ _ d ?_
  refine fun rr => ?_
  have hfun : (fun j =>
        ((if h : j < L.wordLength then (some (.inl (L.encodeIndex i (WP.ri.e rr) ⟨j, h⟩)), true)
          else (none, false) : Body L × Bool)).2) =
      fun j => decide (j < L.wordLength) := funext fun j => by
    by_cases h : j < L.wordLength
    · rw [dif_pos h, decide_eq_true h]
    · rw [dif_neg h, decide_eq_false h]
  change SafeO _ (Step.bind _ _) d _
  refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_commitE W.depth _ hd))
  rintro t d₁ ⟨hd₁, hg₁, h3, h4⟩
  rw [hfun] at hg₁
  exact ⟨hd₁, hg₁, h3, h4⟩

variable (hB : Spec.safeProveB)
include hB

/-- The compiled prover of Test. -/
theorem safe_proveT (tree : TreeH lam) (i : I) (r : L.EncodingRandomness) {d : DSt (spec lam W.K L)}
    (hd : TidyO (rulesB W.K L lam p) d) (ht : TreeOKB d tree) :
    SafeO (rulesB W.K L lam p) (proveT W WP p tree i r) d fun _ d' =>
      TidyO (rulesB W.K L lam p) d' ∧
      GrowsO NoTok (TreeTok tree) zr (mProveB Tag.test L.offline.shape _ W.T.sh 1) d d' := by
  unfold proveT
  refine SafeO.bind _ _ d
    (SafeO.mono ?_ _ d
      (hB I X lam W.K L p Tag.test _ _ (BatchInteractiveOracleProof.ofProto L.offline) _ (BatchHonestProver.ofHonest L.honestOfflineProver)
        W.T WP.T _ id (fun _ => none) W.depthReq [tree] (i, r) (fun _ => true) [some ()] d hd
        (fun tr htr => by rw [List.mem_singleton.mp htr]; exact ht)
        (Or.inl (Star.joins_allLocal _))))
  rintro l d₁ ⟨hd₁, hg₁⟩
  exact ⟨hd₁,
    hg₁.mono (fun _ h => Or.inl h)
      (fun u ⟨tr, htr, hu⟩ => Or.inl (by rw [List.mem_singleton.mp htr] at hu; exact hu))
      (fun _ => le_rfl) (fun _ => le_rfl)⟩

/-- The compiled prover of Link. -/
theorem safe_proveLk (root tree : TreeH lam) (i : I) (r₀ r : L.EncodingRandomness) {d : DSt (spec lam W.K L)}
    (hd : TidyO (rulesB W.K L lam p) d) (hr : TreeOKB d root) (ht : TreeOKB d tree) :
    SafeO (rulesB W.K L lam p) (proveLk W WP p root tree i r₀ r) d fun _ d' =>
      TidyO (rulesB W.K L lam p) d' ∧
      GrowsO NoTok (fun u => TreeTok root u ∨ TreeTok tree u) zr
          (mProveB Tag.link L.link.shape _ W.Lk.sh 1) d d' := by
  unfold proveLk
  refine SafeO.bind _ _ d
    (SafeO.mono ?_ _ d
      (hB I X lam W.K L p Tag.link _ _ (BatchInteractiveOracleProof.ofProto L.link) _
        (BatchHonestProver.ofHonest L.honestLinkProver) W.Lk WP.Lk _ id
    (fun _ => none) W.depthReq [root, tree] (i, r₀, r) (fun _ => true)
    [some ()] d hd (fun tr htr => by
      rcases List.mem_cons.mp htr with rfl | htr
      · exact hr
      · rw [List.mem_singleton.mp htr]; exact ht)
    (Or.inl (Star.joins_allLocal _))))
  rintro l d₁ ⟨hd₁, hg₁⟩
  refine ⟨hd₁,
    hg₁.mono (fun _ h => Or.inl h) (fun u ⟨tr, htr, hu⟩ => Or.inl ?_)
      (fun _ => le_rfl) (fun _ => le_rfl)⟩
  rcases List.mem_cons.mp htr with rfl | htr
  · exact Or.inl hu
  · rw [List.mem_singleton.mp htr] at hu
    exact Or.inr hu

/-- The copies, each with its Link to the root. -/
theorem safe_leavesC (i : I) (root : Node lam L) :
    ∀ (n : ℕ) (d : DSt (spec lam W.K L)), TidyO (rulesB W.K L lam p) d → TreeOKB d root.tree →
    SafeO (rulesB W.K L lam p) (leavesC W WP p i root n) d fun out d' =>
      TidyO (rulesB W.K L lam p) d' ∧
      GrowsO NoTok (TreeTok root.tree) (fun o => n * eNodeB W o)
        (fun o => n * (mNodeB W o + mProveB Tag.link L.link.shape _ W.Lk.sh 1 o)) d d' ∧
      ∀ lf ∈ out, TreeOKB d' lf.node.tree ∧ TreeNew d.vals.length lf.node.tree
  | 0, d, hd, _ => ⟨hd, GrowsO.refl d, fun _ h => absurd h (List.not_mem_nil)⟩
  | n + 1, d, hd, hr => by
      rw [leavesC]
      refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_nodeP' W WP p i hd))
      rintro nd d₁ ⟨hd₁, hg₁, hnd, hnew⟩
      have hr₁ := hr.grows hg₁ (fun _ _ h => h)
      refine SafeO.bind _ _ d₁
        (SafeO.mono ?_ _ d₁ (safe_proveLk W WP p hB root.tree nd.tree i root.r nd.r hd₁ hr₁ hnd))
      rintro π d₂ ⟨hd₂, hg₂⟩
      refine SafeO.bind _ _ d₂
        (SafeO.mono ?_ _ d₂ (safe_leavesC i root n d₂ hd₂ (hr₁.grows hg₂ (fun _ _ h => h))))
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
/-- From `Spec.safeProveB`: `Spec.safeCB`. -/
theorem safeCB_of : Spec.safeCB := by
  intro I X lam L W WP p i d hd
  unfold Cp
  refine SafeO.bind _ _ d (SafeO.mono ?_ _ d (safe_nodeP' W WP p i hd))
  rintro root d₁ ⟨hd₁, hg₁, hroot, hnew⟩
  refine SafeO.bind _ _ d₁ (SafeO.mono ?_ _ d₁ (safe_proveT W WP p hB root.tree i root.r hd₁ hroot))
  rintro πT d₂ ⟨hd₂, hg₂⟩
  have hroot₂ := hroot.grows hg₂ (fun _ _ h => h)
  refine SafeO.bind _ _ d₂
    (SafeO.mono ?_ _ d₂ (safe_leavesC W WP p hB i root (p.M + 1) d₂ hd₂ hroot₂))
  rintro ls d₃ ⟨hd₃, hg₃, hls⟩
  have hg₀₂ := hg₁.trans hg₂ (e := eNodeB W)
    (M := fun o => mNodeB W o + mProveB Tag.test L.offline.shape _ W.T.sh 1 o) (fun _ h => h.elim)
    (fun v hv => Or.inr (hnew v hv)) (fun _ => le_rfl) (fun _ => le_rfl)
  exact ⟨hd₃,
    ⟨hroot₂.grows hg₃ (fun _ _ h => h), fun lf hlf => (hls lf hlf).1⟩,
    hg₀₂.trans hg₃ (fun _ h => h.elim) (fun v hv => Or.inr (hnew v hv))
      (fun _ => le_rfl) (fun _ => le_rfl)⟩

omit W WP p in
/-- From `Spec.safeProveB`: `Spec.safePB`. -/
theorem safePB_of : Spec.safePB := by
  intro I X lam L W WP p k fr xs d hN hd hk
  unfold Pp
  refine fun j => ?_
  refine SafeO.bind _ _ d ?_
  refine fun rσ => ?_
  change SafeO _ (PpJ W WP p k fr xs j.val (WP.perm.e rσ)) d _
  unfold PpJ
  split
  · exact ⟨hd, hk, GrowsO.refl d⟩
  · rename_i lf hj
    have hmem : lf ∈ k.leaves := List.mem_of_getElem? hj
    have hlen : (slotsOfReq (WP.perm.e rσ) xs).length = L.maxBatchSize := by simp [slotsOfReq]
    refine SafeO.bind _ _ d
      (SafeO.mono ?_ _ d
        (hB I X lam W.K L p Tag.onl _ _ L.onlineBatch _ L.honestOnlineBatchProver W.B WP.B _ id some W.depthReq [lf.node.tree]
          (k.i, lf.node.r) (slotFlags (WP.perm.e rσ) fr) (slotsOfReq (WP.perm.e rσ) xs) d hd
          (fun tr htr => by rw [List.mem_singleton.mp htr]; exact hk.2 lf hmem)
          (Or.inr (hlen.trans hN))))
    rintro πs d₁ ⟨hd₁, hg₁⟩
    rw [hlen] at hg₁
    exact ⟨hd₁,
      ⟨hk.1.grows hg₁ (fun _ _ h => h), fun lf' h' => (hk.2 lf' h').grows hg₁ (fun _ _ h => h)⟩,
      hg₁.mono (fun _ h => h.elim) (fun v ⟨tr, htr, hv⟩ => by
        rw [List.mem_singleton.mp htr] at hv
        exact Or.inl (Or.inr ⟨lf, hmem, hv⟩)) (fun _ => le_rfl) (fun _ => le_rfl)⟩

end Compile.Batch.Disc
