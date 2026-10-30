-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SeedCache.lean: the compiled scheme whose proving key holds, beside (i, seed), for
each copy the root and one level of its Merkle tree. (Words of this library: lean/GLOSSARY.md.)

Why. In the implementation the prover's key holds, beside the index and one seed, for each copy a
record with the root of its tree and a file with the digests of one level of that tree. For each
batch the prover hashes the stored level up to a root and ends the batch without a proof if that
root is not the recorded one; what it recomputes below the stored level it compares with the stored
digests, and stops if they differ. In Compile/Batch/SeedStar.lean the proving key isk is (i, seed),
and the prover `PS` recomputes the whole `Node` of the sampled copy. This file defines the scheme
that stores these values and reads them, and shows that the output distributions do not change.

For which schemes. For every scheme given by a record `F : Face`, every decomposition bk into small
samples and every seed oracle σ, as in Compile/Batch/SeedStar.lean; for every level ℓ ≤ W.depth
(level 0: the digests of the leaves; level W.depth: the root); for every value `no` ("no proof", a
function of the copy's number and the batch); with the comparison (own = true) or without it (own =
false).

The scheme `argCache`.
* C is the committer of `argSeed`; then `cacheOf`: for each of the M + 1 copies its `Node` is
  derived under the seed, as `PS` derives it, and (root, level ℓ) is kept. This takes no sample.
* P is `PC`: a uniform copy j with a fresh coin; then `nodeC`: (1) the stored level of copy j is
  hashed up to a root; if that is not the stored root: "no proof"; (2) the randomness of the
  encoding and all leaves with their salts are derived under the seed; (3) the levels below ℓ are
  hashed from the leaves; (4) own = false: level ℓ is not hashed but read; own = true: it is also
  hashed from level ℓ - 1 (ℓ = 0: it is the leaves' digests themselves) and compared with the stored
  level; if they differ: "no proof"; (5) the tree of the `Node` has, from level ℓ on, the stored
  level and what step (1) hashed from it. Then the batch on that `Node`, with fresh coins, as in
  `PS`.
* V does not change.

What is proved.
  `sameRunVia_cache`   For every choice of the oracle functions, C, P and V of `argCache` have the
                       output distributions of those of `argSeed` (`Arg.SameRunVia Prod.fst` of
                       ZKCP/GenSameRun.lean; for P: on every key that C can return).
  `isZKCPArgWith_cache`   So `argCache` has the three properties if and only if `argSeed` has them:
                          same relations, extractor, simulator and bounds.
  `runEager_PC_own`   With the comparison, on any cache, also one that C cannot return (damaged, or
                      written by somebody else): for each copy, `PC` either returns "no proof" or
                      does what `PS` does on that copy. So a wrong cache can cost proofs; it cannot
                      change one. Without the comparison this is not claimed (a wrong level with a
                      root that matches it yields a tree whose levels do not match its leaves).

What a program may store, exactly: Rom/Cache.lean. This file is the instance "root and one level of
each copy's tree".

Notation: `L`: an `BatchProtocol I X`: the record of protocols (Test, Link, Batch; Iop/Batch.lean); `W`: a
`QueryLayout lam L`, the wire record (Iop/BatchWire.lean); `WP`: a `WireBP L`: the prover's data for the
three protocols, and the enumeration of the encoding randomness (Iop/BatchWireP.lean); `p`: a
`Params` (Compile/Star.lean); `p.sMT`, `p.sFS`: the length of the salt of a leaf, and of the salt of
a chain (Compile/Batch/Verifier.lean); the number of copies is `p.M` + 1; `Node`: one encoding as
the prover keeps it (Compile/Batch/Star.lean); `off j`: the weighted number of samples of C before
copy j; `cNode`: the weighted number of samples of a `Node` (both: Compile/Batch/SeedStar.lean);
`Unit` in `List (X × Unit)`: the type argument `W` of `Gen.Arg` (ZKCP/Gen.lean); `.sample n k`: k
takes an element of `Fin (n + 1)` (`OComp`, Rom/OComp.lean); `Prod.fst` in
`Arg.SameRunVia Prod.fst`: the map φ, which reads a prover's key of A' as one of A
(ZKCP/GenSameRun.lean).

Limits: what the Lean definition does not save, and what is not proved.
* `PC` still derives all leaves of the sampled copy and hashes all levels below ℓ. The
  implementation makes only the shown columns and the subtrees above them, and compares only the
  stored nodes above those. That a program which computes only what is read computes the same
  function is not proved here: the prover that recomputes the randomness of the encoding and the
  blocks of leaves that hold a shown position, and its theorem, are in
  Compile/Batch/SeedLazyDefs.lean and Compile/Batch/SeedLazy.lean.
* With own = false `PC` saves the hashing of one level (ℓ from ℓ - 1; at ℓ = 0 it saves nothing);
  with own = true it hashes as much as `PS`. Nothing on running time or on the number of queries is
  stated.
* The `Node` of the first encoding ("anchor" in the implementation, whose stored level only C reads)
  has no entry in the cache: `PS` and `PC` never make it.
* In the implementation a stored value that does not match also stops the service; here each call of
  P is independent of the others and returns "no proof".
* The implementation keeps the level in a file of its own format; nothing is said about formats.
  That the cache is a part of the secret key, and what it would tell a reader, is not treated: the
  key goes to no one.

Of the differences from the implementation that the header of Compile/Batch/SeedStar.lean lists,
this file removes one in part: that isk is (i, seed) and nothing else. The others remain.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Compile.Batch.SeedShape
import Compile.MerkleList
import Rom.Cache

noncomputable section

open Rom Iop ZKCP
open scoped ENNReal

namespace Compile.Batch
namespace Seed

open Compile.Seed (Sh Wt Tosses derive_bind)

/-! ## Part 1. General tools -/

section Gen
variable {S : OSpec} {sp : Split S} {α β : Type}

theorem noCoin_of_tosses {c : OComp S α} (h : Tosses 0 c) : c.NoCoin := by
  generalize hn : (0 : ℕ) = n at h
  induction h with
  | pure a => trivial
  | query o q _ ih => exact fun r => ih r hn
  | sample m _ _ => omega

/-- an algorithm without coins is not changed by the decomposition into small samples -/
theorem blocks_eq_of_noCoin (bk : CoinPlan) {c : OComp S α} (hc : c.NoCoin) : c.blocks bk = c := by
  induction c with
  | pure a => rfl
  | query o q f ih => exact congrArg _ (funext fun r => ih r (hc r))
  | sample n f _ => exact hc.elim

/-- a token program with `Sh o₀ (fun _ => 1) 0` (0 samples, every sample counted as 1; the oracle o₀
never queried) gives an oracle algorithm without coins (`erase`) -/
theorem noCoin_erase {o₀ : S.ι} {c : Step S sp α} (h : Sh o₀ (fun _ => 1) 0 c) (vs : List Bits) :
    (erase c vs).NoCoin :=
  noCoin_of_tosses (h.wt vs).tosses

/-- "evaluates to", for oracle algorithms under fixed oracle functions -/
theorem evalO (g : Fam S) : Evaluates (OComp S) (fun x a => x.det g = a) where
  pure _ := rfl
  bind {_ _ x f a b} hx hf := by
    show (x.bind f).det g = b
    rw [OComp.det_bind, hx, hf]

/-- Evaluates to a value, and leaves the store as it is: for token programs under
fixed oracle functions. -/
theorem evalS (g : Fam S) :
    Evaluates (Step S sp) (fun x a => ∀ vs, (erase x vs).det g = (a, vs)) where
  pure _ _ := rfl
  bind {_ _ x f a b} hx hf vs := by
    show (erase (x.bind f) vs).det g = (b, vs)
    rw [erase_bind, OComp.det_bind, hx vs]
    exact hf vs

open Compile.Seed (All) in
theorem all_true (c : OComp S α) : All (fun _ => True) c := by
  induction c with
  | pure a => trivial
  | query o q k ih => exact ih
  | sample n k ih => exact ih

open Compile.Seed (All) in
theorem all_derive {Q : α → Prop} (σ : SeedOracle S) (s : Fin (σ.sd + 1))
    {c : OComp S α} (h : All Q c) :
    ∀ j, All Q (c.derive σ s j) := by
  induction c with
  | pure a => exact fun _ => h
  | query o q k ih => exact fun j r => ih r (h r) j
  | sample n k ih => exact fun j d => ih _ (h _) (j + 1)

open Compile.Seed (All) in
theorem all_det {Q : α → Prop} (g : Fam S) {c : OComp S α} (h : All Q c) : Q (c.det g) := by
  induction c with
  | pure a => exact h
  | query o q k ih => exact ih _ (h _)
  | sample n k ih => exact ih _ (h _)

end Gen

/-! ## Part 2. The levels of a tree, split at a level -/

section Levels
variable {D : Type} (h : D → D → D)

theorem length_levelsF : ∀ (d : ℕ) (l : List D), (levelsF h d l).length = d + 1
  | 0, _ => rfl
  | d + 1, l => by rw [levelsF_succ, List.length_cons, length_levelsF d]

theorem getLastD_append_cons {β : Type} (A : List β) (b : β) (B : List β) (x : β) :
    (A ++ b :: B).getLastD x = (b :: B).getLastD x := by
  simp [List.getLastD_eq_getLast?, List.getLast?_append, List.getLast?_cons]

/-- The levels of a tree: the levels up to ℓ, and the levels of the tree over level ℓ + 1. -/
theorem levelsF_split :
    ∀ (ℓ e : ℕ) (l : List D), levelsF h (ℓ + 1 + e) l =
      levelsF h ℓ l ++ levelsF h e (pairUpF h ((levelsF h ℓ l).getLastD []))
  | 0, e, l => by
      rw [show 0 + 1 + e = e + 1 by omega, levelsF_succ]
      rfl
  | ℓ + 1, e, l => by
      rw [show ℓ + 1 + 1 + e = (ℓ + 1 + e) + 1 by omega, levelsF_succ,
        levelsF_split ℓ e, levelsF_succ]
      obtain ⟨ls, hls⟩ := exists_levelsF_eq_cons h ℓ (pairUpF h l)
      rw [hls]
      rfl

/-- the levels below level ℓ, and level ℓ as it is hashed from the level below it (level 0: the
leaves themselves) -/
def lowF : ℕ → List D → List (List D) × List D
  | 0, l => ([], l)
  | ℓ + 1, l => (levelsF h ℓ l, pairUpF h ((levelsF h ℓ l).getLastD []))

theorem length_lowF : ∀ (ℓ : ℕ) (l : List D), (lowF h ℓ l).1.length = ℓ
  | 0, _ => rfl
  | ℓ + 1, l => length_levelsF h ℓ l

/-- The levels of a tree, split at level ℓ ≤ d: the levels below, and the levels of the tree over
level ℓ. -/
theorem levelsF_cut {ℓ d : ℕ} (hℓ : ℓ ≤ d) (l : List D) :
    levelsF h d l = (lowF h ℓ l).1 ++ levelsF h (d - ℓ) (lowF h ℓ l).2 := by
  cases ℓ with
  | zero => rfl
  | succ ℓ =>
    obtain ⟨e, rfl⟩ : ∃ e, d = ℓ + 1 + e := ⟨d - (ℓ + 1), by omega⟩
    rw [levelsF_split, show ℓ + 1 + e - (ℓ + 1) = e by omega]
    rfl

theorem getD_levelsF {ℓ d : ℕ} (hℓ : ℓ ≤ d) (l : List D) :
    (levelsF h d l).getD ℓ [] = (lowF h ℓ l).2 := by
  obtain ⟨ls, hls⟩ := exists_levelsF_eq_cons h (d - ℓ) (lowF h ℓ l).2
  rw [levelsF_cut h hℓ l, hls, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (length_lowF h ℓ l).le, length_lowF, Nat.sub_self]
  rfl

theorem rootOf_append_levelsF [Inhabited D] (A : List (List D)) (e : ℕ) (u : List D) :
    rootOf (A ++ levelsF h e u) = rootOf (levelsF h e u) := by
  obtain ⟨ls, hls⟩ := exists_levelsF_eq_cons h e u
  unfold rootOf
  rw [hls, getLastD_append_cons]

/-- level ℓ of a tree with 2 ^ (ℓ + e) leaves has 2 ^ e nodes -/
theorem length_getD_levelsF :
    ∀ (ℓ e : ℕ) (l : List D),
      l.length = 2 ^ (ℓ + e) → ((levelsF h (ℓ + e) l).getD ℓ []).length = 2 ^ e
  | 0, e, l, hl => by
      obtain ⟨ls, hls⟩ := exists_levelsF_eq_cons h (0 + e) l
      rw [hls, List.getD_cons_zero, hl, Nat.zero_add]
  | ℓ + 1, e, l, hl => by
      rw [show ℓ + 1 + e = (ℓ + e) + 1 by omega, levelsF_succ, List.getD_cons_succ]
      exact length_getD_levelsF ℓ e _
        (length_pairUpF h (2 ^ (ℓ + e)) l
          (by rw [hl, show ℓ + 1 + e = (ℓ + e) + 1 by omega, pow_succ]; omega))

theorem length_getD_levelsF' {ℓ d : ℕ} (hℓ : ℓ ≤ d) (l : List D) (hl : l.length = 2 ^ d) :
    ((levelsF h d l).getD ℓ []).length = 2 ^ (d - ℓ) := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hℓ
  rw [Nat.add_sub_cancel_left]
  exact length_getD_levelsF h ℓ e l hl

end Levels

/-! ## Part 3. The derived `Node` of a copy: its leaves, then its levels -/

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- the node function of the trees over encoded indices under fixed oracle functions -/
def hNode {K : ℕ} (g : Fam (spec lam K L)) (a b : Dig lam) : Dig lam :=
  g OracleName.node ((List.ofFn a, List.ofFn b) : Bits × Bits)

theorem noCoin_pairUpV {K : ℕ} : ∀ l : List (Dig lam), (pairUp (hashTreeNode (K := K) (L := L)) l).NoCoin
  | [] => trivial
  | [_] => trivial
  | a :: b :: t =>
    OComp.NoCoin.bind (c := hashTreeNode a b) (fun _ => trivial) fun _ =>
      OComp.NoCoin.bind (noCoin_pairUpV t) fun _ => trivial

theorem noCoin_levelsV {K : ℕ} :
    ∀ (d : ℕ) (l : List (Dig lam)), (levelsM (hashTreeNode (K := K) (L := L)) d l).NoCoin
  | 0, _ => trivial
  | d + 1, l =>
    OComp.NoCoin.bind (noCoin_pairUpV l) fun u =>
      OComp.NoCoin.bind (noCoin_levelsV d u) fun _ => trivial

theorem det_pairUpV {K : ℕ} (g : Fam (spec lam K L)) (l : List (Dig lam)) :
    (pairUp (hashTreeNode (K := K) (L := L)) l).det g = pairUpF (hNode g) l :=
  (evalO g).pairUp (hN := hNode g) (fun _ _ => rfl) l

theorem det_levelsV {K : ℕ} (g : Fam (spec lam K L)) (d : ℕ) (l : List (Dig lam)) :
    (levelsM (hashTreeNode (K := K) (L := L)) d l).det g = levelsF (hNode g) d l :=
  (evalO g).levelsM (hN := hNode g) (fun _ _ => rfl) d l

theorem det_levelsE {K : ℕ} (g : Fam (spec lam K L)) (d : ℕ) (l : List (Dig lam)) (vs : List Bits) :
    (erase (levelsM (nodeE (K := K) (L := L)) d l) vs).det g = (levelsF (hNode g) d l, vs) :=
  (evalS g).levelsM (hN := hNode g) (fun _ _ _ => rfl) d l vs

variable (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

/-- what a `Node` is made of before its tree is hashed up: the randomness of the encoding, the
digests of the leaves, the tokens of their salts -/
abbrev Front (lam : ℕ) (L : BatchProtocol I X) : Type := L.EncodingRandomness × (List (Dig lam) × List (Option (Tok × Tok)))

/-- the first part of nodeP' of Compile/Batch/Star.lean: the randomness, and the leaves with their
salts. All coins of a `Node` are sampled here. -/
def frontP (i : I) : St lam W.K L (Front lam L) :=
  (drawT WP.ri).bind fun r =>
  (leavesE p.sMT
      ((List.range (2 ^ W.depth)).map fun j =>
        if h : j < L.wordLength then (some (.inl (L.encodeIndex i r ⟨j, h⟩)), true)
        else (none, false))).bind fun x =>
  Step.pure (r, x)

/-- the second part: the levels of the tree -/
def upP (y : Front lam L) : St lam W.K L (Node lam L) :=
  (levelsM nodeE W.depth y.2.1).bind fun lv => Step.pure ⟨y.1, ⟨lv, y.2.2⟩⟩

theorem erase_nodeP' (i : I) (vs : List Bits) :
    erase (nodeP' W WP p i) vs =
      (erase (frontP W WP p i) vs).bind fun a => erase (upP W a.1) a.2 := by
  have e : nodeP' W WP p i = (drawT WP.ri).bind fun r =>
      ((leavesE p.sMT
          ((List.range (2 ^ W.depth)).map fun j =>
            if h : j < L.wordLength then (some (.inl (L.encodeIndex i r ⟨j, h⟩)), true)
            else (none, false))).bind fun x =>
              (levelsM nodeE W.depth x.1).bind fun lv => Step.pure (⟨lv, x.2⟩ : TreeH lam)).bind
        fun t => Step.pure ⟨r, t⟩ := rfl
  rw [e]
  unfold frontP upP
  simp only [erase_bind, OComp.bind_assoc]
  rfl

theorem sh_frontP (μ : ℕ → ℕ) (i : I) :
    Sh (S := spec lam W.K L) (sp := split lam W.K L) OracleName.other μ
      (cNode W WP p μ) (frontP W WP p i) := by
  unfold frontP cNode
  refine (sh_drawT μ WP.ri).bind fun r => ?_
  have h := sh_leavesE (lam := lam) (K := W.K) (L := L) μ p.sMT
    ((List.range (2 ^ W.depth)).map fun j =>
      if h : j < L.wordLength then (some (.inl (L.encodeIndex i r ⟨j, h⟩)), true) else (none, false))
  have e := cTree_node W fun j => some (.inl (L.encodeIndex i r j))
  unfold Compile.Seed.cTree at e
  rw [e] at h
  exact h.bind0 fun _ => .pure _

theorem noCoin_upP (y : Front lam L) (vs : List Bits) : (erase (upP W y) vs).NoCoin :=
  noCoin_erase (o₀ := OracleName.other)
    ((sh_levelsM _ (sh_nodeE _) W.depth y.2.1).bind0 fun _ => .pure _) vs

theorem det_upP (g : Fam (spec lam W.K L)) (y : Front lam L) (vs : List Bits) :
    (erase (upP W y) vs).det g = (⟨y.1, ⟨levelsF (hNode g) W.depth y.2.1, y.2.2⟩⟩, vs) := by
  unfold upP
  rw [erase_bind, OComp.det_bind, det_levelsE]
  rfl

variable (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L))

/-- the `Node` of copy j, derived under the seed on an empty store: the term in the
prover PS of Compile/Batch/SeedStar.lean -/
def nodeD (k : I × Fin (σ.sd + 1)) (j : ℕ) : TypedOracleComputation lam W.K L (Node lam L × List Bits) :=
  ((erase (nodeP' W WP p k.1) []).blocks bk).derive σ k.2 (off W WP p bk.m j)

/-- the first part of `nodeD` -/
def frontD (k : I × Fin (σ.sd + 1)) (j : ℕ) : TypedOracleComputation lam W.K L (Front lam L × List Bits) :=
  ((erase (frontP W WP p k.1) []).blocks bk).derive σ k.2 (off W WP p bk.m j)

/-- the derived `Node` is its derived first part, followed by the levels of the tree, in which there
is nothing to derive -/
theorem nodeD_eq (k : I × Fin (σ.sd + 1)) (j : ℕ) :
    nodeD W WP p bk σ k j = (frontD W WP p bk σ k j).bind fun a => erase (upP W a.1) a.2 := by
  have hn := sh_frontP W WP p bk.m k.1
  unfold nodeD frontD
  rw [erase_nodeP', OComp.blocks_bind, derive_bind σ k.2 ((hn.wt []).tosses_blocks bk)]
  refine congrArg _ (funext fun a => ?_)
  rw [blocks_eq_of_noCoin bk (noCoin_upP W a.1 a.2), (noCoin_upP W a.1 a.2).derive_eq]

theorem noCoin_nodeD (k : I × Fin (σ.sd + 1)) (j : ℕ) : (nodeD W WP p bk σ k j).NoCoin :=
  OComp.noCoin_derive _ _ _ _

theorem noCoin_frontD (k : I × Fin (σ.sd + 1)) (j : ℕ) : (frontD W WP p bk σ k j).NoCoin :=
  OComp.noCoin_derive _ _ _ _

/-- the value of the derived `Node` under fixed oracle functions -/
theorem det_nodeD (g : Fam (spec lam W.K L)) (k : I × Fin (σ.sd + 1)) (j : ℕ) :
    (nodeD W WP p bk σ k j).det g =
      (⟨((frontD W WP p bk σ k j).det g).1.1,
          ⟨levelsF (hNode g) W.depth ((frontD W WP p bk σ k j).det g).1.2.1,
            ((frontD W WP p bk σ k j).det g).1.2.2⟩⟩,
        ((frontD W WP p bk σ k j).det g).2) := by
  rw [nodeD_eq, OComp.det_bind, det_upP]

/-! ## Part 4. The cache, and the prover that reads it -/

/-- The cache: for each copy the root of its tree and the digests of one level. -/
abbrev Ca (lam : ℕ) : Type := List (Dig lam × List (Dig lam))

/-- what is kept of a `Node` -/
def keep (ℓ : ℕ) (nd : Node lam L) : Dig lam × List (Dig lam) :=
  (nd.tree.root, nd.tree.levels.getD ℓ [])

def cacheFrom (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) : List ℕ → TypedOracleComputation lam W.K L (Ca lam)
  | [] => .pure []
  | j :: js =>
    (nodeD W WP p bk σ k j).bind fun a => (cacheFrom ℓ k js).bind fun r => .pure (keep ℓ a.1 :: r)

/-- How the cache is computed from (i, seed): for each of the M + 1 copies its `Node` is derived, as
the prover PS derives it, and its root and its level ℓ are kept. -/
def cacheOf (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) : TypedOracleComputation lam W.K L (Ca lam) :=
  cacheFrom W WP p bk σ ℓ k (List.range (p.M + 1))

theorem noCoin_cacheFrom (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) :
    ∀ js, (cacheFrom W WP p bk σ ℓ k js).NoCoin
  | [] => trivial
  | j :: js =>
    OComp.NoCoin.bind (noCoin_nodeD W WP p bk σ k j) fun _ =>
      OComp.NoCoin.bind (noCoin_cacheFrom ℓ k js) fun _ => trivial

theorem noCoin_cacheOf (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) : (cacheOf W WP p bk σ ℓ k).NoCoin :=
  noCoin_cacheFrom W WP p bk σ ℓ k _

theorem det_cacheFrom (g : Fam (spec lam W.K L)) (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) :
    ∀ js, (cacheFrom W WP p bk σ ℓ k js).det g =
      js.map fun j => keep ℓ ((nodeD W WP p bk σ k j).det g).1
  | [] => rfl
  | j :: js => by
      show ((nodeD W WP p bk σ k j).bind fun a =>
          (cacheFrom W WP p bk σ ℓ k js).bind fun r => .pure (keep ℓ a.1 :: r)).det g = _
      rw [OComp.det_bind, OComp.det_bind, det_cacheFrom g ℓ k js]
      rfl

/-- the cache's entry for copy j -/
theorem getD_det_cacheOf (g : Fam (spec lam W.K L)) (ℓ : ℕ)
    (k : I × Fin (σ.sd + 1)) (j : Fin (p.M + 1)) :
    ((cacheOf W WP p bk σ ℓ k).det g).getD j.val default =
      keep ℓ ((nodeD W WP p bk σ k j.val).det g).1 := by
  unfold cacheOf
  rw [det_cacheFrom]
  simp [List.getD_eq_getElem?_getD, j.2]

/-- The levels below the stored level. They are hashed from the leaves l. own = false: level ℓ
itself is not hashed. own = true: it is (level 0: the leaves l themselves), and is compared with the
stored level lv; none if they differ. -/
def lowV {K : ℕ} (own : Bool) :
    ℕ → List (Dig lam) → List (Dig lam) → TypedOracleComputation lam K L (Option (List (List (Dig lam))))
  | 0, l, lv => .pure (if own && !decide (l = lv) then none else some [])
  | ℓ + 1, l, lv => (levelsM hashTreeNode ℓ l).bind fun lo =>
      if own then
        (pairUp hashTreeNode (lo.getLastD [])).bind fun u => .pure (if u = lv then some lo else none)
      else .pure (some lo)

theorem noCoin_lowV {K : ℕ} (own : Bool) :
    ∀ (ℓ : ℕ) (l lv : List (Dig lam)), (lowV (K := K) (L := L) own ℓ l lv).NoCoin
  | 0, _, _ => trivial
  | ℓ + 1, l, lv => OComp.NoCoin.bind (noCoin_levelsV ℓ l) fun lo => by
      cases own
      · exact trivial
      · exact OComp.NoCoin.bind (noCoin_pairUpV _) fun _ => trivial

/-- if the stored level is the true one, the comparison passes -/
theorem det_lowV {K : ℕ} (g : Fam (spec lam K L)) (own : Bool) :
    ∀ (ℓ : ℕ) (l : List (Dig lam)),
      (lowV own ℓ l (lowF (hNode g) ℓ l).2).det g = some (lowF (hNode g) ℓ l).1
  | 0, l => by
      show (if own && !decide (l = l) then none else some []) = some []
      simp
  | ℓ + 1, l => by
      show ((levelsM hashTreeNode ℓ l).bind fun lo =>
          if own then
            (pairUp hashTreeNode (lo.getLastD [])).bind fun u =>
              .pure (if u = (lowF (hNode g) (ℓ + 1) l).2 then some lo else none)
              else .pure (some lo)).det g = _
      rw [OComp.det_bind, det_levelsV]
      cases own
      · rfl
      · show ((pairUp hashTreeNode ((levelsF (hNode g) ℓ l).getLastD [])).bind fun u =>
            .pure (if u = (lowF (hNode g) (ℓ + 1) l).2 then some (levelsF (hNode g) ℓ l)
                else none)).det g = _
        rw [OComp.det_bind, det_pairUpV]
        exact if_pos rfl

/-- The `Node` of copy j, made with the stored root and level st. First the stored level is hashed
up to a root; none if that root is not the stored one. Then the randomness of the encoding and the
leaves with their salts are derived under the seed, and the levels below the stored one are hashed.
The tree that is returned has the stored level, and what was hashed from it, from level ℓ on. -/
def nodeC (own : Bool) (ℓ : ℕ) (k : I × Fin (σ.sd + 1)) (j : ℕ) (st : Dig lam × List (Dig lam)) :
    TypedOracleComputation lam W.K L (Option (Node lam L × List Bits)) :=
  (levelsM hashTreeNode (W.depth - ℓ) st.2).bind fun hi =>
  if rootOf hi = st.1 then
    (frontD W WP p bk σ k j).bind fun a =>
      (lowV own ℓ a.1.2.1 st.2).bind fun lo =>
        .pure (lo.map fun lo => (⟨a.1.1, ⟨lo ++ hi, a.1.2.2⟩⟩, a.2))
  else .pure none

theorem noCoin_nodeC (own : Bool) (ℓ : ℕ) (k : I × Fin (σ.sd + 1))
    (j : ℕ) (st : Dig lam × List (Dig lam)) :
    (nodeC W WP p bk σ own ℓ k j st).NoCoin :=
  OComp.NoCoin.bind (noCoin_levelsV _ _) fun hi => by
    split_ifs
    · exact OComp.NoCoin.bind (noCoin_frontD W WP p bk σ k j) fun a =>
        OComp.NoCoin.bind (noCoin_lowV own ℓ _ _) fun _ => trivial
    · exact trivial

/-- For ℓ ≤ W.depth: with what the committer has kept of copy j, the `Node` made with the stored
level is the `Node` made without. -/
theorem det_nodeC (g : Fam (spec lam W.K L)) (own : Bool) {ℓ : ℕ} (hℓ : ℓ ≤ W.depth)
    (k : I × Fin (σ.sd + 1)) (j : ℕ) :
    (nodeC W WP p bk σ own ℓ k j (keep ℓ ((nodeD W WP p bk σ k j).det g).1)).det g =
      some ((nodeD W WP p bk σ k j).det g) := by
  rw [det_nodeD]
  generalize hy : (frontD W WP p bk σ k j).det g = y
  have hst : keep ℓ (⟨y.1.1, ⟨levelsF (hNode g) W.depth y.1.2.1, y.1.2.2⟩⟩ : Node lam L) =
      (rootOf (levelsF (hNode g) W.depth y.1.2.1), (lowF (hNode g) ℓ y.1.2.1).2) := by
    rw [← getD_levelsF (hNode g) hℓ y.1.2.1]
    rfl
  show (nodeC W WP p bk σ own ℓ k j
      (keep ℓ (⟨y.1.1, ⟨levelsF (hNode g) W.depth y.1.2.1, y.1.2.2⟩⟩ : Node lam L))).det g = _
  rw [hst]
  unfold nodeC
  rw [OComp.det_bind, det_levelsV]
  dsimp only
  rw [if_pos (by rw [levelsF_cut (hNode g) hℓ y.1.2.1, rootOf_append_levelsF]), OComp.det_bind, hy,
    OComp.det_bind, det_lowV]
  show some ((⟨y.1.1,
          ⟨(lowF (hNode g) ℓ y.1.2.1).1 ++
              levelsF (hNode g) (W.depth - ℓ) (lowF (hNode g) ℓ y.1.2.1).2,
            y.1.2.2⟩⟩ : Node lam L),
        y.2) = _
  rw [← levelsF_cut (hNode g) hℓ y.1.2.1]

variable {W} {IVK' Pf' : Type} (F : Face W IVK' Pf')

/-- The prover that reads the cache:
* a uniform copy j with a fresh coin;
* the `Node` of copy j, made with the stored root and level of that copy;
* "no proof" if a stored value does not match (own = false: only the stored root is compared, with
  what the stored level hashes to);
* else the batch on that `Node`, with fresh coins.

The batch is `eraseR` of its program (Compile/Batch/RealQ.lean: queries to `fbw` go to `fb`), as in
the prover with the seed.

That no algorithm of the scheme asks a ghost name (`fbw t k`, Compile/Batch/Oracles.lean) is proved
of this prover, where the seed's oracle is no ghost name (Compile/Batch/SeedGhost.lean: ng_PC), not
of the whole scheme `argCache`: guard_argCache is not in this library. -/
def PC (own : Bool) (ℓ : ℕ) (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots Pf' b)
    (kc : (I × Fin (σ.sd + 1)) × Ca lam) (b : List (X × Unit)) :
    TypedOracleComputation lam W.K L (Gen.Slots Pf' b) :=
  .sample p.M fun j =>
  (nodeC W WP p bk σ own ℓ kc.1 j.val (kc.2.getD j.val default)).bind fun oa =>
  match oa with
  | none => .pure (no j.val b)
  | some a => (eraseR (F.bat kc.1.1 j.val (some a.1) b) a.2).bind fun o => .pure o.1

/-- The scheme given by F with the proving key (i, seed, for each copy its root and one level of its
tree). -/
def argCache (own : Bool) (ℓ : ℕ) (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots Pf' b) :
    Gen.Arg (spec lam W.K L) I X Unit IVK' ((I × Fin (σ.sd + 1)) × Ca lam) Pf' :=
  withCache (argSeed WP p F bk σ) (cacheOf W WP p bk σ ℓ) (PC WP p bk σ F own ℓ no)

/-- for ℓ ≤ W.depth, on the cache that the committer computes, the prover that reads it has the
output distribution of the prover with the seed -/
theorem runEager_PC (own : Bool) {ℓ : ℕ} (hℓ : ℓ ≤ W.depth)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots Pf' b) (g : Fam (spec lam W.K L))
    (k : I × Fin (σ.sd + 1)) (b : List (X × Unit)) :
    (PC WP p bk σ F own ℓ no (k, (cacheOf W WP p bk σ ℓ k).det g) b).runEager g =
      (PS WP p F bk σ k b).runEager g := by
  show (PMF.uniformOfFintype (Fin (p.M + 1))).bind (fun j =>
      ((nodeC W WP p bk σ own ℓ k j.val (((cacheOf W WP p bk σ ℓ k).det g).getD j.val default)).bind
        _).runEager g) =
    (PMF.uniformOfFintype (Fin (p.M + 1))).bind fun j =>
      ((nodeD W WP p bk σ k j.val).bind _).runEager g
  refine congrArg _ (funext fun j => ?_)
  rw [(noCoin_nodeC W WP p bk σ own ℓ k j.val _).runEager_bind,
    (noCoin_nodeD W WP p bk σ k j.val).runEager_bind,
    getD_det_cacheOf, det_nodeC W WP p bk σ g own hℓ]

/-- For ℓ ≤ W.depth, the scheme with the stored level has the output distributions of the scheme
with the proving key (i, seed), for every choice of the oracle functions (the prover: on every key
that the committer of `argCache` can return under them). -/
theorem sameRunVia_cache (own : Bool) {ℓ : ℕ} (hℓ : ℓ ≤ W.depth)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots Pf' b) :
    (argSeed WP p F bk σ).SameRunVia Prod.fst (argCache WP p bk σ F own ℓ no) :=
  sameRunVia_withCache_det (noCoin_cacheOf W WP p bk σ ℓ) fun g k b =>
    runEager_PC WP p bk σ F own hℓ no g k b

/-- For ℓ ≤ W.depth, `argCache` has the three properties if and only if the scheme with the proving
key (i, seed) has them: same relations, extractor, simulator and bounds. -/
theorem isZKCPArgWith_cache {PP : Type} (own : Bool) {ℓ : ℕ} (hℓ : ℓ ≤ W.depth)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots Pf' b) (R : Gen.RelPair I X Unit PP) (B : ℕ)
    (E : Gen.Extractor (spec lam W.K L) I X Unit IVK' Pf')
    (Sim : Gen.Simulator (spec lam W.K L) PP IVK' X Pf') (α : ℝ≥0∞) (ε ζ : ℕ → ℕ → ℝ≥0∞) :
    Gen.IsZKCPArgWith R (argSeed WP p F bk σ) B E Sim α ε ζ ↔
    Gen.IsZKCPArgWith R (argCache WP p bk σ F own ℓ no) B E Sim α ε ζ :=
  (sameRunVia_cache WP p bk σ F own hℓ no).isZKCPArgWith_iff R B E Sim α ε ζ

/-! ## Part 5. A cache that the committer has not written; the size of the cache -/

section Any
variable (W)

theorem det_lowV_own {K : ℕ} (g : Fam (spec lam K L)) :
    ∀ (ℓ : ℕ) (l lv : List (Dig lam)), (lowV true ℓ l lv).det g =
      if (lowF (hNode g) ℓ l).2 = lv then some (lowF (hNode g) ℓ l).1 else none
  | 0, l, lv => by
      show (if true && !decide (l = lv) then none else some []) = if l = lv then some [] else none
      by_cases h : l = lv <;> simp [h]
  | ℓ + 1, l, lv => by
      show ((levelsM hashTreeNode ℓ l).bind fun lo =>
          (pairUp hashTreeNode (lo.getLastD [])).bind fun u =>
            .pure (if u = lv then some lo else none)).det g = _
      rw [OComp.det_bind, det_levelsV, OComp.det_bind, det_pairUpV]
      rfl

/-- With the comparison (own = true) and ℓ ≤ W.depth, whatever is in the cache: the `Node` made with
the stored values is the `Node` made without them, or there is none. -/
theorem det_nodeC_own (g : Fam (spec lam W.K L)) {ℓ : ℕ} (hℓ : ℓ ≤ W.depth) (k : I × Fin (σ.sd + 1))
    (j : ℕ) (st : Dig lam × List (Dig lam)) :
    (nodeC W WP p bk σ true ℓ k j st).det g = none ∨
    (nodeC W WP p bk σ true ℓ k j st).det g = some ((nodeD W WP p bk σ k j).det g) := by
  rw [det_nodeD]
  unfold nodeC
  rw [OComp.det_bind, det_levelsV]
  split_ifs with h1
  · rw [OComp.det_bind, OComp.det_bind, det_lowV_own]
    split_ifs with h2
    · right
      show some ((⟨_, ⟨(lowF (hNode g) ℓ _).1 ++ levelsF (hNode g) (W.depth - ℓ) st.2,
                _⟩⟩ : Node lam L),
            _) = _
      rw [← h2, ← levelsF_cut (hNode g) hℓ]
    · exact Or.inl rfl
  · exact Or.inl rfl

end Any

/-- With the comparison and ℓ ≤ W.depth, on any cache, for every choice of the oracle functions and
every copy: the prover either returns "no proof" or does what the prover with the seed does on that
copy. -/
theorem runEager_PC_own {ℓ : ℕ} (hℓ : ℓ ≤ W.depth)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots Pf' b) (g : Fam (spec lam W.K L))
    (kc : (I × Fin (σ.sd + 1)) × Ca lam) (b : List (X × Unit)) :
    ∃ bad : Fin (p.M + 1) → Prop, (PC WP p bk σ F true ℓ no kc b).runEager g = (PMF.uniformOfFintype (Fin (p.M + 1))).bind fun j =>
      open Classical in if bad j then PMF.pure (no j.val b)
      else
          ((nodeD W WP p bk σ kc.1 j.val).bind fun a =>
              (eraseR (F.bat kc.1.1 j.val (some a.1) b) a.2).bind fun o =>
                  .pure o.1).runEager g := by
  refine ⟨fun j => (nodeC W WP p bk σ true ℓ kc.1 j.val (kc.2.getD j.val default)).det g = none, ?_⟩
  show (PMF.uniformOfFintype (Fin (p.M + 1))).bind (fun j =>
      ((nodeC W WP p bk σ true ℓ kc.1 j.val (kc.2.getD j.val default)).bind _).runEager g) = _
  refine congrArg _ (funext fun j => ?_)
  rw [(noCoin_nodeC W WP p bk σ true ℓ kc.1 j.val _).runEager_bind,
    (noCoin_nodeD W WP p bk σ kc.1 j.val).runEager_bind]
  rcases det_nodeC_own W WP p bk σ g hℓ kc.1 j.val (kc.2.getD j.val default) with h | h
  · rw [if_pos h, h]
    rfl
  · rw [if_neg (fun e :
          (nodeC W WP p bk σ true ℓ kc.1 j.val (kc.2.getD j.val default)).det g = none => by
            rw [h] at e; cases e), h]

section Size
variable (W)
open Compile.Seed (All)

theorem all_leavesE {K : ℕ} (sMT : ℕ) :
    ∀ (l : List (Body L × Bool)) (vs : List Bits),
      All (fun o => o.1.1.length = l.length) (erase (leavesE (lam := lam) (K := K) sMT l) vs)
  | [], _ => rfl
  | (b, bl) :: t, vs => by
      have e : leavesE (lam := lam) (K := K) sMT ((b, bl) :: t) =
          (leafE sMT b bl).bind fun x =>
            (leavesE sMT t).bind fun r => Step.pure (x.1 :: r.1, x.2 :: r.2) := rfl
      rw [e, erase_bind]
      refine All.bind (all_true _) fun a _ => ?_
      rw [erase_bind]
      exact All.bind (all_leavesE sMT t a.2) fun r hr => by
        show (a.1.1 :: r.1.1).length = _
        rw [List.length_cons, List.length_cons, hr]

theorem all_frontP (i : I) (vs : List Bits) :
    All (fun o => o.1.2.1.length = 2 ^ W.depth) (erase (frontP W WP p i) vs) := by
  unfold frontP
  rw [erase_bind]
  refine All.bind (all_true _) fun a _ => ?_
  rw [erase_bind]
  exact All.bind (all_leavesE p.sMT _ a.2) fun x hx => by
    show x.1.1.length = _
    rw [hx, List.length_map, List.length_range]

/-- a derived `Node` has 2 ^ depth leaves -/
theorem length_frontD (g : Fam (spec lam W.K L)) (k : I × Fin (σ.sd + 1)) (j : ℕ) :
    ((frontD W WP p bk σ k j).det g).1.2.1.length = 2 ^ W.depth :=
  all_det (Q := fun o : Front lam L × List Bits => o.1.2.1.length = 2 ^ W.depth)
    g (all_derive σ k.2 ((all_frontP W WP p k.1 []).blocks bk) _)

theorem length_keep (g : Fam (spec lam W.K L)) {ℓ : ℕ} (hℓ : ℓ ≤ W.depth)
    (k : I × Fin (σ.sd + 1)) (j : ℕ) :
    (keep ℓ ((nodeD W WP p bk σ k j).det g).1).2.length = 2 ^ (W.depth - ℓ) := by
  rw [det_nodeD]
  exact length_getD_levelsF' (hNode g) hℓ _ (length_frontD W WP p bk σ g k j)

end Size

/-- The size of the cache that the committer returns, for ℓ ≤ W.depth: an entry for each of the M +
1 copies; each entry is a root and 2 ^ (depth - ℓ) digests. -/
theorem size_cache (own : Bool) {ℓ : ℕ} (hℓ : ℓ ≤ W.depth)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots Pf' b) (i : I) (g : Fam (spec lam W.K L))
    (key : IVK' × ((I × Fin (σ.sd + 1)) × Ca lam))
    (hkey : key ∈ (((argCache WP p bk σ F own ℓ no).C i).runEager g).support) :
    key.2.2.length = p.M + 1 ∧ ∀ e ∈ key.2.2, e.2.length = 2 ^ (W.depth - ℓ) := by
  unfold argCache at hkey
  rw [runEager_withCache_C (noCoin_cacheOf W WP p bk σ ℓ), PMF.support_map] at hkey
  obtain ⟨o, -, rfl⟩ := hkey
  show ((cacheOf W WP p bk σ ℓ o.2).det g).length = _ ∧ ∀ e ∈ (cacheOf W WP p bk σ ℓ o.2).det g, _
  unfold cacheOf
  rw [det_cacheFrom]
  refine ⟨by rw [List.length_map, List.length_range], fun e he => ?_⟩
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 he
  exact length_keep W WP p bk σ g hℓ o.2 j

/-- The number of digests kept, for ℓ ≤ W.depth: (M + 1) (1 + 2 ^ (depth - ℓ)). -/
theorem digests_cache (own : Bool) {ℓ : ℕ} (hℓ : ℓ ≤ W.depth)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots Pf' b) (i : I) (g : Fam (spec lam W.K L))
    (key : IVK' × ((I × Fin (σ.sd + 1)) × Ca lam))
    (hkey : key ∈ (((argCache WP p bk σ F own ℓ no).C i).runEager g).support) :
    (key.2.2.map fun e => 1 + e.2.length).sum = (p.M + 1) * (1 + 2 ^ (W.depth - ℓ)) := by
  obtain ⟨h1, h2⟩ := size_cache WP p bk σ F own hℓ no i g key hkey
  rw [List.map_congr_left (g := fun _ => 1 + 2 ^ (W.depth - ℓ)) fun e he => by rw [h2 e he],
    List.map_const', List.sum_replicate, h1]
  rfl

end Seed
end Compile.Batch
