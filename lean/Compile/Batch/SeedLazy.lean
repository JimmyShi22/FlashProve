-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedLazy.lean: the scheme with the lazy prover has the output distributions of the
scheme whose proving key is (i, seed), if `W.OKG` and ℓ ≤ W.depth. (Words of this library:
lean/GLOSSARY.md.)

Definitions: Compile/Batch/SeedLazyDefs.lean (the steps are numbered in its header). `PL` keeps for
each copy the root and one level ℓ of its Merkle tree, and recomputes, of the `Node` of the sampled
copy, the randomness of the encoding and the blocks of 2^ℓ leaves that hold a shown position.

  `bat_eq`   under the hypotheses of its statement, one batch of `argP` on a `Node` and its store
             is: a placement; `proveBUG` (Compile/Batch/SeedLazyFin.lean) on the empty store, on the
             root of its tree and the openings read from its store
  `runEager_PLrun`   under fixed oracle functions g, steps 4 to 6 of the lazy prover, on what the
                     committer has kept of copy j, have the output distribution of that program for
                     the `Node` of copy j as it is derived under g; `runEager_PLat`, `runEager_PL`:
                     the same, on the committer's cache, for the batch on copy j and for the prover
  `sameRunVia_lazy`, `isZKCPArgWith_lazy`
      `argP` and `argPL` are in the relation `SameRunVia Prod.fst` of ZKCP/GenSameRun.lean; so each
      has the three properties if the other has, with the same relations, extractor, simulator and
      bounds

Proof-of-work bits. The forms with the suffix Gr assume `W.OKG` (`lazyGr` proves `Spec.lazyGr`);
`sameRunVia_lazy` and `isZKCPArgWith_lazy` follow by `QueryLayout.OK.toG`. All attempts are in the chains
(step 4), which both provers run alike, with the ghost names written back (`eraseR`,
Compile/Batch/RealQ.lean); the programs that make the proof strings query no ghost name
(Compile/Batch/SeedLazyFin.lean: `nog_finishAllG`).

Hypotheses. ℓ ≤ W.depth, and of `W.OK`, or `W.OKG` (Iop/BatchWire.lean), three fields: `slots`
(there are 2^depthReq slots), `fits` (the encoding has at most 2^depth symbols), `extB` (position p
of the encoding is leaf p of the one tree).

Limits: what the head of Rom/Cache.lean lists as not said is not said here either. What the header
of Compile/Batch/SeedLazyDefs.lean lists: no cost; nothing on a cache that the committer has not
written. And what Rom/Cache.lean lists: a bound on the queries of the honest prover does not carry
over from `argP` to `argPL`, and none is proved here for `argPL` (a block is derived once for each
read position in it, so the number of its queries depends on how many positions are read).

Difference from the implementation that it removes: the prover derives the whole `Node` of the
sampled copy (the head of Compile/Batch/SeedLazyDefs.lean).
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Compile.Batch.SeedLazyFin
import Compile.Batch.SeedLazyLeaf

noncomputable section

open Rom Iop ZKCP
open scoped ENNReal

namespace Compile.Batch
namespace Seed

open Compile.Seed (SaltsLt All)

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L))

theorem noCoin_rD (k : I × Fin (σ.sd + 1)) (j : ℕ) : (rD W WP p bk σ k j).NoCoin :=
  OComp.noCoin_derive _ _ _ _

theorem noCoin_opL (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) (j : ℕ) (r : L.EncodingRandomness) (lvl : List (Dig lam))
    (hi : List (List (Dig lam))) (q : ℕ) :
    (opL W WP p bk σ ℓ k j r lvl hi q).NoCoin :=
  OComp.NoCoin.bind (OComp.noCoin_derive _ _ _ _) fun a =>
    OComp.NoCoin.bind (noCoin_levelsV ℓ a.1.1) fun _ => trivial

/-- the program with which both provers are compared, as `erase` makes it of a token program: a
placement; proveBUG on the empty store, on a root and on openings that are given; a proof (j, piB)
for each request -/
def batG0 (i : I) (r : L.EncodingRandomness) (cm : Dig lam) (ext : (Fin L.wordLength → Bool) → ExtF lam (oneExternalString L.wordLength L.Symbol))
    (j : ℕ) (b : List (X × Unit)) :
    TypedOracleComputation lam W.K L (Gen.Slots (PrfK lam L) b) :=
  .sample WP.perm.n fun z =>
  (erase (proveBUG p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B
        (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩)) id some W.depthReq (i, r) [cm] ext
        (slotFlags (WP.perm.e z) fun _ => true) (slotsOfReq (WP.perm.e z) (b.map Prod.fst)))
      []).bind fun o =>
  .pure (fitLen ⟨0, none⟩ b.length (prfsK j (b.map Prod.fst).length (WP.perm.e z) o.1))

/-- `batG0` with `eraseR` for `erase` (the ghost names written back): what the scheme runs -/
def batG (i : I) (r : L.EncodingRandomness) (cm : Dig lam) (ext : (Fin L.wordLength → Bool) → ExtF lam (oneExternalString L.wordLength L.Symbol))
    (j : ℕ) (b : List (X × Unit)) :
    TypedOracleComputation lam W.K L (Gen.Slots (PrfK lam L) b) :=
  .sample WP.perm.n fun z =>
  (eraseR (proveBUG p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B
        (fun q a => some (.inr ⟨Tag.onl, ⟨q, a⟩⟩)) id some W.depthReq (i, r) [cm] ext
        (slotFlags (WP.perm.e z) fun _ => true) (slotsOfReq (WP.perm.e z) (b.map Prod.fst)))
      []).bind fun o =>
  .pure (fitLen ⟨0, none⟩ b.length (prfsK j (b.map Prod.fst).length (WP.perm.e z) o.1))

theorem realQ_batG0 (i : I) (r : L.EncodingRandomness) (cm : Dig lam)
    (ext : (Fin L.wordLength → Bool) → ExtF lam (oneExternalString L.wordLength L.Symbol)) (j : ℕ) (b : List (X × Unit)) :
    realQ (batG0 W WP p i r cm ext j b) = batG W WP p i r cm ext j b := by
  unfold batG0 batG
  rw [realQ_sample]
  refine congrArg _ (funext fun z => ?_)
  rw [realQ_bind]
  rfl

/-- one batch of the token program, on a `Node` and its store (hypotheses below) -/
theorem bat_eq0 (hN : L.maxBatchSize = 2 ^ W.depthReq) (i : I) (j : ℕ) (nd : Node lam L) (b : List (X × Unit))
    (vs : List Bits) (hl : SaltsLt vs.length nd.tree.salts) :
    ((erase (batOf WP (runBU W WP p) i j (some nd) b) vs).bind fun o => .pure o.1) =
      batG0 W WP p i nd.r nd.tree.root (extOf W.B.ext (L.honestOnlineBatchProver.ext (i, nd.r)) [nd.tree] vs) j b := by
  show (Rom.OComp.sample WP.perm.n fun z =>
      (erase ((runBU W WP p [nd.tree] (i, nd.r) (slotFlags (WP.perm.e z) fun _ => true)
            (slotsOfReq (WP.perm.e z) (b.map Prod.fst))).bind fun πs =>
              Step.pure
                (fitLen ⟨0, none⟩ b.length (prfsK j (b.map Prod.fst).length (WP.perm.e z) πs)))
          vs).bind
        fun o => .pure o.1) = _
  unfold batG0
  refine congrArg _ (funext fun z => ?_)
  rw [erase_bind, OComp.bind_assoc]
  unfold runBU
  rw [erase_proveBU p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ id some W.depthReq [nd.tree] (i, nd.r)
      _ _ (fun t ht => by rw [List.mem_singleton.1 ht]; exact hl)]
  exact proveBUG_empty p.sMT p.sFS Tag.onl L.onlineBatch L.honestOnlineBatchProver W.B WP.B _ id some W.depthReq (i, nd.r) _
    [nd.tree.root] _ _ ((length_slotsOfReq _ _).trans hN) vs
    fun πs => .pure (fitLen ⟨0, none⟩ b.length (prfsK j (b.map Prod.fst).length (WP.perm.e z) πs))

/-- One batch of argP, on a `Node` and its store (hypotheses below). -/
theorem bat_eq (hN : L.maxBatchSize = 2 ^ W.depthReq) (i : I) (j : ℕ) (nd : Node lam L) (b : List (X × Unit))
    (vs : List Bits) (hl : SaltsLt vs.length nd.tree.salts) :
    ((eraseR (batOf WP (runBU W WP p) i j (some nd) b) vs).bind fun o => .pure o.1) =
      batG W WP p i nd.r nd.tree.root (extOf W.B.ext (L.honestOnlineBatchProver.ext (i, nd.r)) [nd.tree] vs) j b := by
  rw [← realQ_batG0, ← bat_eq0 W WP p hN i j nd b vs hl, realQ_bind]
  rfl

variable {W}

/-- Steps 4 to 6 of the lazy prover (`PLrun`), on what the committer has kept of copy j: under the
hypotheses below and fixed oracle functions g, they have the output distribution of `batG` for the
`Node` of copy j as it is derived under g. -/
theorem runEager_PLrun (hW : W.OKG) {ℓ : ℕ} (hℓ : ℓ ≤ W.depth)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b) (g : Fam (spec lam W.K L))
    (k : I × Fin (σ.sd + 1)) (b : List (X × Unit)) (j : ℕ) (cm : Dig lam) :
    (PLrun W WP p bk σ ℓ no k b j (cm, (lowF (hNode g) ℓ ((frontD W WP p bk σ k j).det g).1.2.1).2)
        (levelsF (hNode g) (W.depth - ℓ)
          (lowF (hNode g) ℓ ((frontD W WP p bk σ k j).det g).1.2.1).2)
        ((frontD W WP p bk σ k j).det g).1.1).runEager g =
      (batG W WP p k.1 ((frontD W WP p bk σ k j).det g).1.1 cm
        (extOf W.B.ext (L.honestOnlineBatchProver.ext (k.1, ((frontD W WP p bk σ k j).det g).1.1))
          [⟨levelsF (hNode g) W.depth ((frontD W WP p bk σ k j).det g).1.2.1,
            ((frontD W WP p bk σ k j).det g).1.2.2⟩]
          ((frontD W WP p bk σ k j).det g).2)
        j b).runEager g := by
  have ho := fun q : Fin L.wordLength =>
    det_opL W WP p bk σ g k j hℓ (q := (W.B.ext.leaf q))
      (by rw [(hW.extB q).2]; exact lt_of_lt_of_le q.2 hW.fits)
  generalize (frontD W WP p bk σ k j).det g = y at ho ⊢
  unfold PLrun batG
  show (PMF.uniformOfFintype (Fin (WP.perm.n + 1))).bind _ =
    (PMF.uniformOfFintype (Fin (WP.perm.n + 1))).bind _
  refine congrArg _ (funext fun z => ?_)
  dsimp only
  rw [eraseR_proveBUG, OComp.bind_assoc, OComp.runEager_bind, OComp.runEager_bind]
  refine congrArg _ (funext fun o => ?_)
  rw [(noCoin_finishAllL L.onlineBatch L.honestOnlineBatchProver W.B WP.B (k.1, y.1.1) _ (noCoin_opL W WP p bk σ ℓ k j y.1.1 _ _)
      _ _ _ 0 _ _).runEager_bind,
    (noCoin_finishAllG L.onlineBatch L.honestOnlineBatchProver W.B WP.B (k.1, y.1.1) _ _ _ _ 0 _ _).runEager_bind,
    det_finishAllL L.onlineBatch L.honestOnlineBatchProver W.B WP.B (k.1, y.1.1) _ g
      (opnOf W.B.ext (L.honestOnlineBatchProver.ext (k.1, y.1.1)) [⟨levelsF (hNode g) W.depth y.1.2.1, y.1.2.2⟩] y.2)
      (fun q => ?_) (fun _ => rfl)]
  · rfl
  · rw [ho q]
    unfold opnOf
    rw [(hW.extB q).1]
    rfl

theorem getElem?_det_cacheOf
    (g : Fam (spec lam W.K L)) (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) (j : Fin (p.M + 1)) :
    ((cacheOf W WP p bk σ ℓ k).det g)[j.val]? =
      some (keep ℓ ((nodeD W WP p bk σ k j.val).det g).1) := by
  unfold cacheOf
  rw [det_cacheFrom]
  simp [j.2]

/-- all tokens of the derived `Node` are below the length of its store -/
theorem saltsLt_nodeD (g : Fam (spec lam W.K L)) (k : I × Fin (σ.sd + 1)) (j : ℕ) :
    SaltsLt ((nodeD W WP p bk σ k j).det g).2.length ((nodeD W WP p bk σ k j).det g).1.tree.salts :=
  all_det (Q := fun o : Node lam L × List Bits => SaltsLt o.2.length o.1.tree.salts)
    g (all_derive σ k.2 ((all_nodeP' W WP p k.1 []).blocks bk) _)

/-- The batch on copy j, on the committer's cache (hypotheses below). -/
theorem runEager_PLat (hW : W.OKG) {ℓ : ℕ} (hℓ : ℓ ≤ W.depth)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b) (g : Fam (spec lam W.K L))
    (k : I × Fin (σ.sd + 1)) (b : List (X × Unit)) (j : Fin (p.M + 1)) :
    (PLat W WP p bk σ ℓ no (k, (cacheOf W WP p bk σ ℓ k).det g) b j.val).runEager g =
      ((nodeD W WP p bk σ k j.val).bind fun a =>
        (eraseR (batOf WP (runBU W WP p) k.1 j.val (some a.1) b) a.2).bind fun o =>
            .pure o.1).runEager g := by
  rw [(noCoin_nodeD W WP p bk σ k j.val).runEager_bind,
    bat_eq W WP p hW.slots k.1 j.val _ b _ (saltsLt_nodeD WP p bk σ g k j.val)]
  unfold PLat
  dsimp only
  rw [getElem?_det_cacheOf, det_nodeD]
  dsimp only
  have hst : keep ℓ
        (⟨((frontD W WP p bk σ k j.val).det g).1.1,
          ⟨levelsF (hNode g) W.depth ((frontD W WP p bk σ k j.val).det g).1.2.1,
            ((frontD W WP p bk σ k j.val).det g).1.2.2⟩⟩ : Node lam L) =
      (rootOf (levelsF (hNode g) W.depth ((frontD W WP p bk σ k j.val).det g).1.2.1),
        (lowF (hNode g) ℓ ((frontD W WP p bk σ k j.val).det g).1.2.1).2) := by
    rw [← getD_levelsF (hNode g) hℓ]
    rfl
  rw [hst]
  dsimp only
  rw [(noCoin_levelsV _ _).runEager_bind, det_levelsV,
    if_pos (by
        rw [levelsF_cut (hNode g) hℓ ((frontD W WP p bk σ k j.val).det g).1.2.1,
          rootOf_append_levelsF]),
    (noCoin_rD W WP p bk σ k j.val).runEager_bind, det_rD, runEager_PLrun WP p bk σ hW hℓ]
  rfl

/-- Under `W.OKG`, ℓ ≤ W.depth: on the cache that the committer computes, the lazy prover has the
output distribution of the prover of argP. -/
theorem runEager_PL (hW : W.OKG) {ℓ : ℕ} (hℓ : ℓ ≤ W.depth)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b) (g : Fam (spec lam W.K L))
    (k : I × Fin (σ.sd + 1)) (b : List (X × Unit)) :
    (PL W WP p bk σ ℓ no (k, (cacheOf W WP p bk σ ℓ k).det g) b).runEager g =
      ((argP W WP p bk σ).P k b).runEager g := by
  rw [argP_P]
  show (PMF.uniformOfFintype (Fin (p.M + 1))).bind
      (fun j => (PLat W WP p bk σ ℓ no (k, (cacheOf W WP p bk σ ℓ k).det g) b j.val).runEager g) =
    (PMF.uniformOfFintype (Fin (p.M + 1))).bind fun j =>
      ((nodeD W WP p bk σ k j.val).bind fun a =>
        (eraseR (batOf WP (runBU W WP p) k.1 j.val (some a.1) b) a.2).bind fun o =>
          .pure o.1).runEager g
  exact congrArg _ (funext fun j => runEager_PLat WP p bk σ hW hℓ no g k b j)

/-- Under `W.OKG` (rounds may have proof-of-work bits) and ℓ ≤ W.depth: the scheme with the lazy
prover has the output distributions of argP, for every choice of the oracle functions (the prover:
on every key that the committer of `argPL` can return under them). -/
theorem sameRunVia_lazyGr (hW : W.OKG) {ℓ : ℕ} (hℓ : ℓ ≤ W.depth)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b) :
    (argP W WP p bk σ).SameRunVia Prod.fst (argPL W WP p bk σ ℓ no) :=
  sameRunVia_withCache_det (noCoin_cacheOf W WP p bk σ ℓ) fun g k b =>
    runEager_PL WP p bk σ hW hℓ no g k b

/-- `sameRunVia_lazyGr` under `W.OK` (no proof-of-work bits) -/
theorem sameRunVia_lazy (hW : W.OK) {ℓ : ℕ} (hℓ : ℓ ≤ W.depth)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b) :
    (argP W WP p bk σ).SameRunVia Prod.fst (argPL W WP p bk σ ℓ no) :=
  sameRunVia_lazyGr WP p bk σ hW.toG hℓ no

/-- Under `W.OKG` and ℓ ≤ W.depth: argPL has the three properties if and only if argP has them: same
relations, extractor, simulator and bounds. -/
theorem isZKCPArgWith_lazyGr {PP : Type} (hW : W.OKG) {ℓ : ℕ} (hℓ : ℓ ≤ W.depth)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b) (R : Gen.RelPair I X Unit PP)
    (B : ℕ) (E : Gen.Extractor (spec lam W.K L) I X Unit (IVKK lam L) (PrfK lam L))
    (Sim : Gen.Simulator (spec lam W.K L) PP (IVKK lam L) X (PrfK lam L)) (α : ℝ≥0∞)
    (ε ζ : ℕ → ℕ → ℝ≥0∞) :
    Gen.IsZKCPArgWith R (argP W WP p bk σ) B E Sim α ε ζ ↔
    Gen.IsZKCPArgWith R (argPL W WP p bk σ ℓ no) B E Sim α ε ζ :=
  (sameRunVia_lazyGr WP p bk σ hW hℓ no).isZKCPArgWith_iff R B E Sim α ε ζ

/-- `isZKCPArgWith_lazyGr` under `W.OK` (no proof-of-work bits) -/
theorem isZKCPArgWith_lazy {PP : Type} (hW : W.OK) {ℓ : ℕ} (hℓ : ℓ ≤ W.depth)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b) (R : Gen.RelPair I X Unit PP)
    (B : ℕ) (E : Gen.Extractor (spec lam W.K L) I X Unit (IVKK lam L) (PrfK lam L))
    (Sim : Gen.Simulator (spec lam W.K L) PP (IVKK lam L) X (PrfK lam L)) (α : ℝ≥0∞)
    (ε ζ : ℕ → ℕ → ℝ≥0∞) :
    Gen.IsZKCPArgWith R (argP W WP p bk σ) B E Sim α ε ζ ↔
    Gen.IsZKCPArgWith R (argPL W WP p bk σ ℓ no) B E Sim α ε ζ :=
  (sameRunVia_lazy WP p bk σ hW hℓ no).isZKCPArgWith_iff R B E Sim α ε ζ

end Seed

theorem lazyGr : Spec.lazyGr := fun _ _ _ _ _ WP p bk σ _ no hW hℓ =>
  Seed.sameRunVia_lazyGr WP p bk σ hW hℓ no

end Compile.Batch
