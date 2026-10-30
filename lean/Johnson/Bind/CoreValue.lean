-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/CoreValue.lean: THE WRITTEN COMMITTER's KEY AS A PURE FUNCTION OF THE TYPED ORACLES.
At letters: any object with OOD samples, any wire, any wire of the seed, any family of oracle
functions. No size, no coding of queries, no hash function on strings, no program.

Why. `committerAtFixedCoins` (Johnson/TypedOracleCompiler/RecCompile/CommitOverTypedOracles.lean) is an algorithm: a term that asks typed
oracles. To compare its key with what another committer computes one wants the key's value under
given oracle functions, written without any algorithm. That value falls into three parts, and each
is a definition of its own here:
  the hash tree    `rootF`: the library's pure tree (`Compile.levelsF`, `Compile.rootOf`,
                   Compile/MerkleList.lean, Compile/MerkleM.lean) over the leaves' answers, with
                   the nodes' answers as its node function. It reads the word through `committerLeafInput`.
  the OOD seed     `seedF`: the seed's map at the answer to the second of two chained queries, the
                   first at the root.
  the OOD answers  `L.recOf i r` at that seed: no oracle is asked.
The encoder (`L.encodeIndex`) and the answers (`L.recOf`) stay letters: what hashes stands apart from what
encodes.

Main names (namespace `Bind.Core`).
  `det_pairUp`, `det_levelsM`   general in the family of oracles: the value of the tree's levels as
    an algorithm is the pure levels at the node algorithm's values.
  `leafF`, `nodeF`, `leavesF`, `rootF`, `seedF`, `keyF`   the pure parts.
  `det_committerLeafHashes`, `det_committerNodeHash`, `det_committerTreeRoot`   the parts' values.
  **`committerAtFixedCoins_det`**   the first part of `committerAtFixedCoins`'s value under F is `keyF`; `committerAtFixedCoins_det_text`
    is the same with every definition of this file written out.
  `keyAtCoins_value`, `commitAtCoins_value`   so the written committer over a told structure
    (Johnson/Top/ToldCommitPlain.lean), at a hash function: general in the told structure.

Limits. Values under fixed oracle functions ("every coin toss yields 0", Rom/Cache.lean; `committerAtFixedCoins`
tosses none): nothing on a count of queries, a log or a probability. No binding of the commitment
(the opening form, BindsWith), no correctness of extraction, no index privacy (hiding of the
weights). Nothing says that any program computes these values. As in Compile/MerkleM.lean nothing
asks that the word is as long as the tree is wide: beyond the word's length the filling stands.
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Top.ToldCommitPlain
import Run.DetOverOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Core
open Rom
open _root_.Compile (pairUp pairUpF levelsM levelsF)

variable {S : OSpec} {D : Type}

/-- One level up, as an algorithm: its value is the pure step at the node algorithm's values. -/
theorem det_pairUp (g : Fam S) (hN : D → D → OComp S D) :
    ∀ l : List D, (pairUp hN l).det g = pairUpF (fun a b => (hN a b).det g) l
  | [] => rfl
  | [_] => rfl
  | a :: b :: t => by
      show ((hN a b).bind fun c => (pairUp hN t).bind fun r => OComp.pure (c :: r)).det g = _
      rw [OComp.det_bind, OComp.det_bind, det_pairUp g hN t]
      rfl

/-- All levels, as an algorithm: their value is the pure levels at the node algorithm's values. -/
theorem det_levelsM (g : Fam S) (hN : D → D → OComp S D) :
    ∀ (d : ℕ) (l : List D), (levelsM hN d l).det g = levelsF (fun a b => (hN a b).det g) d l
  | 0, _ => rfl
  | d + 1, l => by
      show ((pairUp hN l).bind fun u => (levelsM hN d u).bind fun r => OComp.pure (l :: r)).det g
        = _
      rw [OComp.det_bind, OComp.det_bind, det_pairUp, det_levelsM g hN d]
      rfl

end Bind.Core

noncomputable section

namespace Bind.Core
open Rom
open _root_.Compile (levelsF rootOf)
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (F : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))

/-! ### The pure parts -/

/-- The leaves' oracle function, its answer read as a digest. -/
def leafF (x : LeafIn (typedOracleCarrier L Bd aT aL)) : Dig lam := F OracleName.leaf x

/-- The nodes' oracle function at two digests. -/
def nodeF (a b : Dig lam) : Dig lam := F OracleName.node (List.ofFn a, List.ofFn b)

/-- The 2 ^ depth leaves' digests over a word: leaf j at `committerLeafInput`'s input (the symbol at j as the
wire writes it, or the filling; the salt of j). -/
def leavesF (b₀ : Bd) (y : Fin L.wordLength → L.Symbol) (σ : ℕ → Bits) : List (Dig lam) :=
  (List.range (2 ^ W.depth)).map fun j => leafF W F (committerLeafInput W b₀ y σ j)

/-- **The pure tree's root**: the library's pure levels over the leaves' digests. -/
def rootF (b₀ : Bd) (y : Fin L.wordLength → L.Symbol) (σ : ℕ → Bits) : Dig lam :=
  rootOf (levelsF (nodeF W F) W.depth (leavesF W F b₀ y σ))

/-- **The OOD seed at a root**: the first query at the root; the second at the chain value of the
first answer; the seed's map at the second answer's blocks. -/
def seedF (root : Dig lam) : L.OutOfDomainSeed :=
  S.seed (show FsAns lam W.K from F (OracleName.fb S.t)
    (seedQ1 W S (link (show FsAns lam W.K from F (OracleName.fb S.t) (seedQ0 W S root))))).1

/-- **The key**: the root over the encoded index, with the honest OOD sample at the root's seed. -/
def keyF (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (σ : ℕ → Bits) : KeyRoot lam L :=
  ⟨rootF W F b₀ (L.encodeIndex i r) σ, L.recOf i r (seedF W S F (rootF W F b₀ (L.encodeIndex i r) σ))⟩

/-! ### The algorithms' values -/

/-- The leaves' queries: their value is the oracle function along the list. -/
theorem det_committerLeafHashes : ∀ xs : List (LeafIn (typedOracleCarrier L Bd aT aL)),
    (committerLeafHashes W xs).det F = xs.map (leafF W F)
  | [] => rfl
  | x :: xs => by
      show ((OComp.ask (S := typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)) OracleName.leaf x).bind fun u =>
        (committerLeafHashes W xs).bind fun us => .pure ((show Dig lam from u) :: us)).det F = _
      rw [OComp.det_bind, OComp.det_bind, det_committerLeafHashes xs]
      rfl

/-- A node's query. -/
theorem det_committerNodeHash (a b : Dig lam) : (committerNodeHash W a b).det F = nodeF W F a b := rfl

/-- **The tree's value is the pure tree's root.** -/
theorem det_committerTreeRoot (b₀ : Bd) (y : Fin L.wordLength → L.Symbol) (σ : ℕ → Bits) :
    (committerTreeRoot W b₀ y σ).det F = rootF W F b₀ y σ := by
  unfold committerTreeRoot
  rw [OComp.det_bind, OComp.det_bind, det_committerLeafHashes, det_levelsM, List.map_map]
  rfl

/-- **THE WRITTEN COMMITTER's KEY UNDER GIVEN ORACLE FUNCTIONS.** -/
theorem committerAtFixedCoins_det (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (σ : ℕ → Bits) :
    ((committerAtFixedCoins W S b₀ i r σ).det F).1 = keyF W S F b₀ i r σ := by
  unfold committerAtFixedCoins
  rw [OComp.det_bind, det_committerTreeRoot]
  rfl

/-- The same with this file's definitions written out. -/
theorem committerAtFixedCoins_det_text (b₀ : Bd) (i : I) (r : L.EncodingRandomness) (σ : ℕ → Bits) (root : Dig lam)
    (hroot : root = rootOf (levelsF
      (fun a b => (show Dig lam from F OracleName.node (List.ofFn a, List.ofFn b))) W.depth
      ((List.range (2 ^ W.depth)).map fun j =>
        (show Dig lam from F OracleName.leaf (committerLeafInput W b₀ (L.encodeIndex i r) σ j))))) :
    ((committerAtFixedCoins W S b₀ i r σ).det F).1 =
      ⟨root, L.recOf i r (S.seed (show FsAns lam W.K from F (OracleName.fb S.t)
        (seedQ1 W S (link (show FsAns lam W.K from F (OracleName.fb S.t) (seedQ0 W S root))))).1)⟩ := by
  subst hroot
  exact committerAtFixedCoins_det W S F b₀ i r σ

end Bind.Core

namespace Bind.Core
open Rom ZKCP VerifiableInference VerifiableInference.OnPublicFiles
open TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop (Dig)

variable {R : InnerCompilerInput} (T : LayoutsByPublicReading R) (b₀ : R.LeafBody)

/-- **The written committer's key at given coins, at a family g over one oracle**: d the public
reading's value; the told part of d; `keyF` at the typed oracle functions that are read out of g
through the coding at d. -/
theorem keyAtCoins_value (g : Fam (rom 256)) (i : R.Index) (r : R.protocol.EncodingRandomness) (σ : ℕ → Bits) :
    (T.keyAtCoins b₀ i r σ).det g =
      (T.part (T.Pub.det g),
        keyF R.queryLayout (T.Sd (T.Pub.det g)) (readBlocks (T.m (T.Pub.det g)) g) b₀ i r σ) := by
  unfold LayoutsByPublicReading.keyAtCoins
  rw [Rom.OComp.det_bind, Rom.OComp.det_bind, Rom.det_overOne, committerAtFixedCoins_det]
  rfl

/-- **The written committer's commitment at given coins, at a hash function**: that function's
answer at the told code of that key. No algorithm stands on the right. -/
theorem commitAtCoins_value (hash : Hash) (i : R.Index) (r : R.protocol.EncodingRandomness) (σ : ℕ → Bits) :
    (T.commitAtCoins b₀ i r σ).evaluate hash =
      ZKCP.digestUnder hash T.encT
        (T.part (T.Pub.det (_root_.Run.famOne hash)),
          keyF R.queryLayout (T.Sd (T.Pub.det (_root_.Run.famOne hash)))
            (readBlocks (T.m (T.Pub.det (_root_.Run.famOne hash))) (_root_.Run.famOne hash))
            b₀ i r σ) := by
  rw [evaluate_commitAtCoins, keyAtCoins_value]

end Bind.Core

end

#print axioms Bind.Core.det_pairUp
#print axioms Bind.Core.det_levelsM
#print axioms Bind.Core.det_committerLeafHashes
#print axioms Bind.Core.det_committerNodeHash
#print axioms Bind.Core.det_committerTreeRoot
#print axioms Bind.Core.committerAtFixedCoins_det
#print axioms Bind.Core.committerAtFixedCoins_det_text
#print axioms Bind.Core.keyAtCoins_value
#print axioms Bind.Core.commitAtCoins_value
