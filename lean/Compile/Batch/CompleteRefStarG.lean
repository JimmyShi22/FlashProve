-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteRefStarG.lean: for every fixed family of oracle functions that answers the
ghost names as `fb t` (`RealFam`, Compile/Batch/CompleteChain.lean), in a run of the honest
committer's program of the compiled scheme whose rounds may have proof-of-work bits (`CpX`,
Compile/Batch/StarX.lean), the events that Test is bad and that the Link of copy number j ≤ `p.M` is
bad have the distributions of their small experiments `Ref.RT`, `Ref.RL`. Here bad means: the proof
string is `none`, or a search over nonces of the transcript has failed (words of this library:
lean/GLOSSARY.md). Towards completeness of the compiled scheme.

An event "bad" is a function of the hash blocks and of w, x, n (`Ref.badAt`), and, under the
hypotheses of its statement, the hash blocks of one execution have the distribution of `proveO`
(`lawS_proveBX`, Compile/Batch/CompleteRefChain.lean): so nothing has to be known of the proof
strings.

  Part 1  `mkX`: the output of the instrumented run (the run that also outputs, among other things,
          the hash blocks), from the outputs of the committer and the prover
  Part 2  Test, Links, copies, the committer: `law_proveTX`, `law_proveLkX`, `law_leavesCX_link`,
          `law_leavesCX_node`, `law_CpX_test`, `law_CpX_link`, `law_CpX_node`
  Part 3  `badL_congr`: the Link's event depends on the proving key, the hash blocks of the Links
          and the sampled copy only

Limits: this file does not prove these distributions for the honest run of committer and prover
together or for every family, and it says nothing on the event "the slot of a request is bad".
-/
import Compile.Batch.CompleteRefChain
import Compile.Batch.SpecCompleteG
import Compile.Batch.LoopEager
import Compile.Batch.CompleteRefNoGhost

noncomputable section

namespace Compile.Batch.RefStarG
open Iop Rom Prob Compile.Batch.Cmpl Compile.Batch.Ref

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (f : Fam (spec lam W.K L)) (i : I)

/-! ## Part 1. The instrumented run -/

/-- the output of the instrumented run, from the outputs of the committer and the prover -/
def mkX (o : (IVK lam L × IskH lam L) × XC lam W.K) (πs : List (Prf lam L) × XP lam W.K L.maxBatchSize) :
    (IVK lam L × List (Prf lam L)) × RunX lam W.K L :=
  ((o.1.1, πs.1), ⟨o.1.2, o.2.1, o.2.2, πs.2.1, πs.2.2.1, πs.2.2.2⟩)



/-! ## Part 2. Test, Links, copies, the committer -/

variable (hf : RealFam f)
include hf

/-- under `RealFam`: Test is bad with the distribution of testO -/
theorem law_proveTX (nd : Node lam L) (vs : List Bits) :
    LawS f (proveTX W WP p nd.tree i nd.r) vs
      (fun o _ =>
        badAt (BatchInteractiveOracleProof.ofProto L.offline) (BatchHonestProver.ofHonest L.honestOfflineProver) W.T WP.T (i, nd.r) () 0 o.2)
      ((testO W WP p i (nd.r, nd.tree.root)).runEager f) := by
  unfold proveTX testO
  rw [OComp.runEager_bind]
  exact LawS.bind
    (lawS_proveBX f p.sMT p.sFS Tag.test (BatchInteractiveOracleProof.ofProto L.offline) (BatchHonestProver.ofHonest L.honestOfflineProver) W.T
      WP.T (fun q a => some (.inr ⟨Tag.test, ⟨q, a⟩⟩)) id (fun _ => none) W.depthReq [nd.tree]
      (i, nd.r) hf (RoundSplits.fmt_allLocal _) (fun _ => true) [some ()] (Or.inr (allLo_allLocal _)) vs)
    (tri_true' _ vs) fun o vs1 _ => lawS_pure _ _ _

/-- under `RealFam`: a Link is bad with the distribution of linkO -/
theorem law_proveLkX (root nd : Node lam L) (vs : List Bits) :
    LawS f (proveLkX W WP p root.tree nd.tree i root.r nd.r) vs
      (fun o _ =>
        badAt (BatchInteractiveOracleProof.ofProto L.link) (BatchHonestProver.ofHonest L.honestLinkProver) W.Lk WP.Lk
          (i, root.r, nd.r) () 0 o.2)
      ((linkO W WP p i (root.r, root.tree.root) (nd.r, nd.tree.root)).runEager f) := by
  unfold proveLkX linkO
  rw [OComp.runEager_bind]
  exact LawS.bind
    (lawS_proveBX f p.sMT p.sFS Tag.link (BatchInteractiveOracleProof.ofProto L.link) (BatchHonestProver.ofHonest L.honestLinkProver)
      W.Lk WP.Lk (fun q a => some (.inr ⟨Tag.link, ⟨q, a⟩⟩)) id (fun _ => none) W.depthReq
      [root.tree, nd.tree] (i, root.r, nd.r) hf (RoundSplits.fmt_allLocal _) (fun _ => true) [some ()]
      (Or.inr (allLo_allLocal _)) vs)
    (tri_true' _ vs) fun o vs1 _ => lawS_pure _ _ _

omit hf in
theorem law_nodeP' (vs : List Bits) :
    LawS f (nodeP' W WP p i) vs (fun nd _ => (nd.r, nd.tree.root))
      ((nodeO W WP p i).runEager f) := by
  unfold nodeP' nodeO
  rw [runEager_drawO_bind]
  refine lawS_drawT_bind f WP.ri _ vs _ _ fun rr => ?_
  rw [OComp.runEager_bind]
  exact LawS.bind (lawS_commitE f p.sMT W.depth (Ref.encLeaf i (WP.ri.e rr)) vs)
    (tri_true' _ vs) fun t vs1 _ => lawS_pure _ _ _

/-- a run of which only the index, the root, the copies, the hash blocks of the Links and the
sampled copy matter -/
def runL (root : Node lam L)
    (ls : List (LeafRec lam L) × List (List (List (Blk lam W.K)))) (j : ℕ) : RunX lam W.K L :=
  ⟨⟨i, root, ls.1⟩, [], ls.2, j, 1, []⟩

/-- under `RealFam`: the Link of copy number j < n is bad with the distribution of a fresh node and
its Link -/
theorem law_leavesCX_link (root : Node lam L) :
    ∀ (n : ℕ) (vs : List Bits) (j : ℕ), j < n →
      LawS f (leavesCX W WP p i root n) vs (fun ls _ => (runL W i root ls j).badL WP)
        (((nodeO W WP p i).bind (linkO W WP p i (root.r, root.tree.root))).runEager f)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, vs, 0, _ => by
      rw [OComp.runEager_bind]
      refine LawS.bind (law_nodeP' W WP p f i vs) (tri_true' _ vs) fun nd vs1 _ => ?_
      have h := LawS.bind
        (ψ := fun (ls : List (LeafRec lam L) × List (List (List (Blk lam W.K)))) (_ : List Bits) =>
            (runL W i root ls 0).badL WP)
        (ν := PMF.pure)
        (g := fun π =>
            (leavesCX W WP p i root n).bind fun rest =>
              (Step.pure (⟨nd, π.1⟩ :: rest.1, π.2 :: rest.2) : St lam W.K L _))
        (law_proveLkX W WP p f i hf root nd vs1) (tri_true' _ vs1) fun π vs2 _ =>
          lawS_const (Tri.bind (tri_true' _ vs2) fun rest vs3 _ => tri_pure_iff.2 rfl)
      rw [PMF.bind_pure] at h
      exact h
  | n + 1, vs, j + 1, hj => by
      refine LawS.bind_drop (tri_true' _ vs) fun nd vs1 _ =>
        LawS.bind_drop (tri_true' _ vs1) fun π vs2 _ => ?_
      have h := LawS.bind
        (ψ := fun (ls : List (LeafRec lam L) × List (List (List (Blk lam W.K)))) (_ : List Bits) =>
            (runL W i root ls (j + 1)).badL WP)
        (ν := PMF.pure)
        (g := fun rest => (Step.pure (⟨nd, π.1⟩ :: rest.1, π.2 :: rest.2) : St lam W.K L _))
        (law_leavesCX_link root n vs2 j (Nat.lt_of_succ_lt_succ hj))
        (tri_true' _ vs2) fun rest vs3 _ => lawS_pure _ _ _
      rw [PMF.bind_pure] at h
      exact h

omit hf in
/-- the node of copy number j < n has the distribution of a fresh node -/
theorem law_leavesCX_node (root : Node lam L) :
    ∀ (n : ℕ) (vs : List Bits) (j : ℕ), j < n →
      LawS f (leavesCX W WP p i root n) vs
        (fun ls _ => ls.1[j]?.map fun lf => (lf.node.r, lf.node.tree.root))
        (((nodeO W WP p i).runEager f).map some)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, vs, 0, _ => by
      rw [← PMF.bind_pure_comp]
      refine LawS.bind (law_nodeP' W WP p f i vs) (tri_true' _ vs) fun nd vs1 _ => ?_
      exact lawS_const
        (Tri.bind (tri_true' _ vs1) fun π vs2 _ =>
          Tri.bind (tri_true' _ vs2) fun rest vs3 _ => tri_pure_iff.2 rfl)
  | n + 1, vs, j + 1, hj => by
      refine LawS.bind_drop (tri_true' _ vs) fun nd vs1 _ =>
        LawS.bind_drop (tri_true' _ vs1) fun π vs2 _ => ?_
      have h := LawS.bind
        (ψ := fun (ls : List (LeafRec lam L) × List (List (List (Blk lam W.K)))) (_ : List Bits) =>
            ls.1[j + 1]?.map fun lf => (lf.node.r, lf.node.tree.root))
        (ν := PMF.pure)
        (g := fun rest => (Step.pure (⟨nd, π.1⟩ :: rest.1, π.2 :: rest.2) : St lam W.K L _))
        (law_leavesCX_node root n vs2 j (Nat.lt_of_succ_lt_succ hj))
        (tri_true' _ vs2) fun rest vs3 _ => lawS_pure _ _ _
      rw [PMF.bind_pure] at h
      exact h

/-- a run of which only the committer's output and the sampled copy matter -/
def runC (o : (IVK lam L × IskH lam L) × XC lam W.K) (j : ℕ) : RunX lam W.K L :=
  ⟨o.1.2, o.2.1, o.2.2, j, 1, []⟩

theorem law_CpX_test (vs : List Bits) :
    LawS f (CpX W WP p i) vs (fun o _ => (runC W o 0).badT WP) ((Ref.RT W WP p i).runEager f) := by
  unfold CpX Ref.RT
  rw [OComp.runEager_bind]
  refine LawS.bind (law_nodeP' W WP p f i vs) (tri_true' _ vs) fun root vs1 _ => ?_
  have h := LawS.bind
    (ψ := fun (o : (IVK lam L × IskH lam L) × XC lam W.K) (_ : List Bits) => (runC W o 0).badT WP)
    (ν := PMF.pure)
    (g := fun πT =>
        (leavesCX W WP p i root (p.M + 1)).bind fun ls =>
          (Step.pure ((⟨root.tree.root, πT.1⟩, ⟨i, root, ls.1⟩), (πT.2, ls.2)) :
            St lam W.K L ((IVK lam L × IskH lam L) × XC lam W.K)))
    (law_proveTX W WP p f i hf root vs1) (tri_true' _ vs1)
    fun πT vs2 _ => lawS_const (Tri.bind (tri_true' _ vs2) fun ls vs3 _ => tri_pure_iff.2 rfl)
  rw [PMF.bind_pure] at h
  exact h

theorem law_CpX_link (vs : List Bits) {j : ℕ} (hj : j < p.M + 1) :
    LawS f (CpX W WP p i) vs (fun o _ => (runC W o j).badL WP) ((Ref.RL W WP p i).runEager f) := by
  unfold CpX Ref.RL
  rw [OComp.runEager_bind]
  refine LawS.bind (law_nodeP' W WP p f i vs) (tri_true' _ vs) fun root vs1 _ =>
    LawS.bind_drop (tri_true' _ vs1) fun πT vs2 _ => ?_
  have h := LawS.bind
    (ψ := fun (o : (IVK lam L × IskH lam L) × XC lam W.K) (_ : List Bits) => (runC W o j).badL WP)
    (ν := PMF.pure)
    (g := fun ls =>
        (Step.pure ((⟨root.tree.root, πT.1⟩, ⟨i, root, ls.1⟩), (πT.2, ls.2)) :
          St lam W.K L ((IVK lam L × IskH lam L) × XC lam W.K)))
    (law_leavesCX_link W WP p f i hf root (p.M + 1) vs2 j hj)
    (tri_true' _ vs2) fun ls vs3 _ => lawS_pure _ _ _
  rw [PMF.bind_pure] at h
  exact h

omit hf in
theorem law_CpX_node (vs : List Bits) {j : ℕ} (hj : j < p.M + 1) :
    LawS f (CpX W WP p i) vs
      (fun o _ => o.1.2.leaves[j]?.map fun lf => (lf.node.r, lf.node.tree.root))
      (((nodeO W WP p i).runEager f).map some) := by
  unfold CpX
  refine LawS.bind_drop (tri_true' _ vs) fun root vs1 _ =>
    LawS.bind_drop (tri_true' _ vs1) fun πT vs2 _ => ?_
  have h := LawS.bind
    (ψ := fun (o : (IVK lam L × IskH lam L) × XC lam W.K) (_ : List Bits) =>
        o.1.2.leaves[j]?.map fun lf => (lf.node.r, lf.node.tree.root))
    (ν := PMF.pure)
    (g := fun ls =>
        (Step.pure ((⟨root.tree.root, πT.1⟩, ⟨i, root, ls.1⟩), (πT.2, ls.2)) :
          St lam W.K L ((IVK lam L × IskH lam L) × XC lam W.K)))
    (law_leavesCX_node W WP p f i root (p.M + 1) vs2 j hj)
    (tri_true' _ vs2) fun ls vs3 _ => lawS_pure _ _ _
  rw [PMF.bind_pure] at h
  exact h

omit hf in
theorem tri_CpX_idx (vs : List Bits) : Tri f (CpX W WP p i) vs fun o _ => o.1.2.i = i :=
  Tri.bind (tri_true' _ vs) fun _ vs1 _ =>
    Tri.bind (tri_true' _ vs1) fun _ vs2 _ =>
      Tri.bind (tri_true' _ vs2) fun _ _ _ => tri_pure_iff.2 rfl

/-! ## Part 3. The Link's event -/

omit hf in
/-- the Link's event depends on the proving key, the hash blocks of the Links and the sampled copy
only -/
theorem badL_congr {z z' : RunX lam W.K L} (h1 : z.isk = z'.isk)
    (h2 : z.bL = z'.bL) (h3 : z.leaf = z'.leaf) : z.badL WP = z'.badL WP := by
  unfold RunX.badL
  rw [h1, h2, h3]



end Compile.Batch.RefStarG
