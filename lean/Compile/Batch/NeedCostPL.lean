-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/NeedCostPL.lean: what the committer and the prover of `argP` (one seed) and `argPL`
(the lazy prover) cost over one hash function, if only the marked blocks (those that the table
`needOf nb m` names: Compile/Batch/NeedTable.lean) are queried (the second exit): upper bounds for
the pieces without a search. For every wire record, with or without proof-of-work bits; nb is a
parameter (words of this library: lean/GLOSSARY.md). Sums for the whole committers and provers at
the weight "marked blocks", and theorems on them, are not in this library.

The file goes piece by piece through what the steps from the committer with fresh coins and the
prover with no query for an empty slot to `argPL` add: coins derived from a seed (one query to the
oracle `other` for each small sample: bk.m v small samples make a sample among v + 1), the cache,
the openings of the lazy prover.
    In this file:
      `cOpL ℓ`     one opening, lazily: 2^ℓ + 2^ℓ · bk.m (2^sMT − 1) + (2^ℓ − 1): the leaves of the
                   block of leaves, the small samples of their salts (counted as if all were
                   salted), the nodes over them
      `cacheOf_len`   a bound on the lazy prover (`cav_P_argPL`) requires that each stored level of
                   the key has at most 2^(depth − ℓ) digests (a longer list would be hashed whole);
                   for ℓ ≤ depth the keys that the committer makes have exactly so many
      Tools, stated with `CA` (Compile/CostPost.lean), over the typed oracles, at the weight "marked
      blocks": `ca_realQ` .. `ca_opL`; `num_seed`: a query at a point of the seed oracle is at most
      one block
    The bounds. The sums for the committer of `argP`, for the committer of `argPL` and for the
    prover of `argP` are not in this library.
    Theorems on the whole committers and provers, at the weight "marked blocks" over the typed
    oracles and over the second exit to one hash function: not in this library.
    In their stead, in other files:
       Compile/Batch/SpecOneCallL.lean has the sums `cCPA`, `cCPLA`, `cPLA`, in which an attempt
       that fails and is not the last costs one;
       Compile/Batch/OneCallCostPL.lean has the sums `cCPW`, `cCPLW`, `cPLW` for any weight of an
       attempt:
                   cCPW = cCBW + off W WP p bk.m (M + 1) (off ..: the small samples of the
                   committer: Compile/Batch/SeedStar.lean); cCPLW = cCPW + (M + 1) · (tr depth +
                   cNode): for the cache each copy's node is derived a second time (tr d = 2^d + 2^d
                   − 1: leaves and inner nodes; cNode: the small samples of a node); cPLW ℓ nE n =
                   (2^(depth − ℓ) − 1) + bk.m ri.n + cPUW n + n · (nE · cOpL ℓ) (nE: a slot's
                   verifier reads at most so many positions of the encoded index)
       Compile/Batch/OneCallCostPL.lean has theorems on the whole committers and provers over the
       typed oracles, for a weight that may depend on the answer: `cav_C_argSeed`, `cav_C_argPL`,
       `cav_P_argPL`
Notation:
  `σ`: `SeedOracle` (Rom/SpecDerive.lean): an auxiliary oracle, used as a source of coins: seeds are
    the elements of Fin (sd + 1); pt s j is the query for the seed s and the counter j
  `bk`: `CoinPlan` (Rom/Blocks.lean): how a uniform sample is made from small ones; bk.m n: the
    number of small samples for a sample with n + 1 outcomes
  `k`: I × Fin (σ.sd + 1): (i, seed), the proving key of `argP` (Compile/Batch/SeedLazyDefs.lean)
  `M`: `p.M`: the number of copies is M + 1 (`Params`, Compile/Star.lean); a copy: a further
    encoding (lean/GLOSSARY.md); `j`: the number of a copy; `depth`: `W.depth`, depth of the tree
    over an encoded index (Iop/BatchWire.lean)
  `ℓ`: the number of the stored level (`keep`, Compile/Batch/SeedCache.lean); `r`: `L.EncodingRandomness`, the
    randomness of the encoding of copy j (`rD`); `u`: block u of 2^ℓ leaves (`blockD`); `q`, `lvl`,
    `hi`: leaf q, the stored level, the levels above it (`opL`): Compile/Batch/SeedLazyDefs.lean
Hypotheses: `Need.Std m`; σ reads the oracle `other`.
Limits: upper bounds on every path. No piece here holds a search. `ca_opL` makes the whole block of
leaves for one opening; a sum that counts it for each position that is read (`cPLA`, `cPLW`) makes a
block again also where two positions are in one block. Nothing on the mean. Numbers of queries, each
counted as one however long its string; nothing on time, memory or work in the fields. No lower
bound.
-/
import Compile.Batch.NeedCostChains
import Compile.Batch.SeedLazyLeaf
import Compile.Batch.SeedGhost
import Compile.Batch.StarO
import Compile.CostPost
import Rom.OverOneNGen

set_option autoImplicit false

open Rom Iop

namespace Compile.Batch
namespace Need
open Compile.CostP (SWA)
open Compile.Seed (Tosses Wt)
open Seed

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params) (nb : Tag → ℕ → ℕ) {m : OracleCoding (spec lam W.K L) lam} (hm : Std m)

local notation "T1" => fun _ => True
local notation "SWo" => SWA (S := spec lam W.K L) (sp := split lam W.K L) (Rom.Need.num (needOf nb m))
local notation "CAo" => OComp.CA (S := spec lam W.K L) (Rom.Need.num (needOf nb m))

/-! ## Part 1. Tools -/

include hm

omit WP p in
/-- For `Std m`: the bound and the property carry over to `realQ c` (Compile/Batch/Oracles.lean:
queries to `fbw` become queries to `fb`). -/
theorem ca_realQ {α : Type} {P : α → Prop} (c : TypedOracleComputation lam W.K L α) :
    ∀ t, CAo c t P → CAo (realQ c) t P := by
  induction c with
  | pure a => exact fun _ h => h
  | sample n k ih => exact fun t h r => ih r t (h r)
  | query o q k ih =>
    rintro t ⟨t', e, h⟩
    cases o with
    | fbw t₀ j =>
      exact ⟨t',
        le_trans (le_of_eq (congrArg (· + t') (num_fbw_eq W nb hm t₀ j q).symm)) e,
        fun r => ih r t' (h r)⟩
    | _ => exact ⟨t', e, fun r => ih r t' (h r)⟩

omit WP p in
/-- what a scheme runs of a program of the token language -/
theorem ca_eraseR {α : Type} {P : α → Prop} {c : St lam W.K L α} {n : ℕ}
    (h : SWo c n P) (vs : List Bits) :
    CAo (eraseR c vs) n fun o => P o.1 :=
  ca_realQ W nb hm _ _ (h.ca vs)

variable (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L)) (hσ : σ.o = OracleName.other)
include hσ

omit WP p in
/-- For `Std m`, if σ reads `other`: a query at a point of the seed oracle is at most one block. -/
theorem num_seed (s : Fin (σ.sd + 1)) (j : ℕ) : (needOf nb m).num σ.o (σ.pt s j) ≤ 1 :=
  (num_le_blk nb hm σ.o _).trans (le_of_eq (by rw [hσ]; rfl))

/-! ## Part 2. One seed: a copy's node, derived -/

/-- the node of a copy, derived -/
theorem ca_nodeD (k : I × Fin (σ.sd + 1)) (j : ℕ) :
    CAo (nodeD W WP p bk σ k j) (tr W.depth + cNode W WP p bk.m) T1 :=
  (OComp.CA.derive σ k.2 (num_seed W nb hm σ hσ k.2)
      ((wt_nodeP' W WP p bk.m k.1 []).tosses_blocks bk) _ _
      (OComp.CA.blocks bk _ _ ((swa_nodeP' W WP p nb hm k.1).ca []))).mono
    (fun _ _ => trivial) (by rw [Nat.mul_one])


variable {IVK' Pf' : Type} (F : Face W IVK' Pf')


/-! ## Part 3. The cache -/

theorem ca_cacheFrom (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) :
    ∀ js : List ℕ,
      CAo (cacheFrom W WP p bk σ ℓ k js) (js.length * (tr W.depth + cNode W WP p bk.m)) T1
  | [] => trivial
  | j :: js =>
    OComp.CA.bind' (ca_nodeD W WP p nb hm bk σ hσ k j)
      (fun _ _ => (ca_cacheFrom ℓ k js).map _ fun _ _ => trivial)
      (le_of_eq (by rw [List.length_cons, Nat.succ_mul]; omega))


/-! ## Part 4. The lazy prover -/

omit WP p hσ in
theorem ca_nodeV (a b : Dig lam) : CAo (hashTreeNode (K := W.K) (L := L) a b) 1 T1 :=
  ⟨0, num_le_blk nb hm OracleName.node _, fun _ => trivial⟩

omit WP p hσ in
theorem ca_pairUpV :
    ∀ l : List (Dig lam), CAo (pairUp (hashTreeNode (K := W.K) (L := L)) l)
      (l.length / 2) fun u => u.length = (l.length + 1) / 2
  | [] => show ([] : List (Dig lam)).length = (0 + 1) / 2 from rfl
  | [a] => show [a].length = (1 + 1) / 2 from rfl
  | a :: b :: t =>
      OComp.CA.bind' (ca_nodeV W nb hm a b) (m' := t.length / 2) (fun c _ => OComp.CA.bind' (ca_pairUpV t) (m' := 0) (fun r hr => by
        show (c :: r).length = ((a :: b :: t).length + 1) / 2
        simp only [List.length_cons]
        omega) (Nat.le_refl _)) (by simp only [List.length_cons]; omega)

omit WP p hσ in
/-- For `Std m`: the levels over n digests cost at most n − 1 -/
theorem ca_levelsV :
    ∀ (d : ℕ) (l : List (Dig lam)), CAo (levelsM (hashTreeNode (K := W.K) (L := L)) d l) (l.length - 1) T1
  | 0, _ => trivial
  | d + 1, l =>
      OComp.CA.bind' (ca_pairUpV W nb hm l) (m' := (l.length + 1) / 2 - 1)
        (fun u hu =>
          OComp.CA.bind' (hu ▸ ca_levelsV d u) (m' := 0) (fun _ _ => trivial) (Nat.le_refl _))
        (by omega)

/-- the randomness of the encoding, derived -/
theorem ca_rD (k : I × Fin (σ.sd + 1)) (j : ℕ) : CAo (rD W WP p bk σ k j) (bk.m WP.ri.n) T1 :=
  (OComp.CA.derive σ k.2 (num_seed W nb hm σ hσ k.2)
      (((sh_drawT (lam := lam) (K := W.K) (L := L) bk.m WP.ri).wt []).tosses_blocks bk) _ _
      (OComp.CA.blocks bk _ _ ((swa_drawT nb WP.ri).ca []))).mono
    (fun _ _ => trivial) (by rw [Nat.mul_one, Nat.zero_add])

/-- what one opening costs the lazy prover at most: the 2^ℓ leaves of the block, a query for each
small sample of their salts (counted as if all were salted), and the 2^ℓ − 1 inner nodes over
them -/
def cOpL (ℓ : ℕ) : ℕ := 2 ^ ℓ + 2 ^ ℓ * bk.m (2 ^ p.sMT - 1) + (2 ^ ℓ - 1)

/-- a block of leaves, derived -/
theorem ca_blockD (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) (j : ℕ) (r : L.EncodingRandomness) (u : ℕ) :
    CAo (blockD W WP p bk σ ℓ k j r u) (2 ^ ℓ + 2 ^ ℓ * bk.m (2 ^ p.sMT - 1)) fun a =>
      a.1.1.length = 2 ^ ℓ := by
  have hl : ((List.range (2 ^ ℓ)).map fun t => leafFn (L := L) k.1 r (u * 2 ^ ℓ + t)).length =
      2 ^ ℓ := by
    rw [List.length_map, List.length_range]
  have h := OComp.CA.derive σ k.2 (num_seed W nb hm σ hσ k.2)
    (tosses_leavesE (lam := lam) (K := W.K) p.sMT bk
      ((List.range (2 ^ ℓ)).map fun t => leafFn (L := L) k.1 r (u * 2 ^ ℓ + t)) [])
    _ (off W WP p bk.m j + bk.m WP.ri.n + min (u * 2 ^ ℓ) L.wordLength * bk.m (2 ^ p.sMT - 1))
    (OComp.CA.blocks bk _ _
      ((swa_leavesE nb hm p.sMT
        ((List.range (2 ^ ℓ)).map fun t => leafFn (L := L) k.1 r (u * 2 ^ ℓ + t))).ca []))
  refine h.mono (fun a ha => ha.trans hl) ?_
  rw [hl, Nat.mul_one]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (le_trans List.countP_le_length (le_of_eq hl))) _

/-- One opening. -/
theorem ca_opL (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) (j : ℕ) (r : L.EncodingRandomness) (lvl : List (Dig lam))
    (hi : List (List (Dig lam))) (q : ℕ) :
    CAo (opL W WP p bk σ ℓ k j r lvl hi q) (cOpL p bk ℓ) T1 :=
  OComp.CA.bind' (ca_blockD W WP p nb hm bk σ hσ ℓ k j r (q / 2 ^ ℓ)) (m' := 2 ^ ℓ - 1)
    (fun a ha =>
      OComp.CA.bind' (ha ▸ ca_levelsV W nb hm ℓ a.1.1) (m' := 0)
        (fun _ _ => trivial) (Nat.le_refl _)) (Nat.le_refl _)

variable {nE : ℕ} (hE : ∀ x ρ, (L.onlineBatch.loc.extReads x ρ).card ≤ nE) (hnd : W.B.ext.all.Nodup)
include hE hnd


omit hm hσ hE hnd in
/-- If ℓ ≤ W.depth: for every family of oracle functions each stored level of a key that the
committer makes has exactly 2^(depth − ℓ) digests. -/
theorem cacheOf_len (g : Fam (spec lam W.K L)) {ℓ : ℕ} (hℓ : ℓ ≤ W.depth) (k : I × Fin (σ.sd + 1)) :
    ∀ st ∈ (cacheOf W WP p bk σ ℓ k).det g, st.2.length = 2 ^ (W.depth - ℓ) := by
  intro st hst
  unfold cacheOf at hst
  rw [det_cacheFrom] at hst
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hst
  exact length_keep W WP p bk σ g hℓ k j

end Need
end Compile.Batch
