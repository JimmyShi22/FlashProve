-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/CoreJoin.lean: THE WRITTEN COMMITTER's KEY, SPELLED, IS WHAT THE RUNNING COMMITTER
COMPUTES, UNDER NAMED EQUATIONS ON SINGLE QUERIES, ON THE ENCODER AND ON THE ANSWERS. At letters:
any object with OOD samples, any wire, any family of typed oracle functions, any hash on bytes, any
shape of a committed table, any way of spelling digests, seeds and answers.

Why. Two committers are written. One asks typed oracles (`committerAtFixedCoins`,
Johnson/TypedOracleCompiler/RecCompile/CommitOverTypedOracles.lean); its key under given oracle functions is the pure function
`keyF` (Johnson/Bind/CoreValue.lean). The other runs on bytes (`Bind.Twin.coreW`,
Johnson/Bind/Twin.lean). Both build a hash tree over the columns of an encoded table, sample OOD
seeds from the root, and answer them. This file is the joint. It takes as premises what is said of
ONE query or of NO query, and concludes on the whole. The passage between a tree of digests and a
tree of byte strings is `Bind.Twin.rootOf_levelsF_map`, and the running committer's tree as the
library's pure tree is `Bind.Twin.rootW_id` (both Johnson/Bind/TwinTree.lean).
  What hashes:
    `TreeSpells`  the two trees have one depth; a leaf's typed answer, spelled, is the running
                  committer's leaf at that position; a node's typed answer, spelled, is the format's
                  vertex at the spelled children.
    `SeedSpells`  at every root: the typed seed, spelled, is what the running committer samples
                  from the table's name at the spelled root.
  What does not hash:
    `AnsSpells`   at every seed: the written answers, spelled, are the running committer's answers
                  at the spelled seed.
  (That the written encoder's symbols are the running committer's columns enters through
  `TreeSpells.leaf`: the premise names the word and the columns.)

Main names (namespace `Bind.Core`).
  `coreW_id`   the running committer at the identity monad, field by field.
  `root_spelled`   from `TreeSpells`: the root.
  **`key_spelled`**   from the three: root, seeds and answers; with them the name and the ID's text.
  `id_spelled`   so a function of the typed key that is the format's ID at every spelled key is the
    running committer's ID.

Limits. Every premise is owed by whoever calls these: NOTHING HERE SAYS THAT ANY OF THEM HOLDS AT
ANY SIZE, and where one cannot hold the statements say nothing. Values alone: nothing on a count of
queries, a log or a probability; no binding of the commitment (the opening form, BindsWith), no
correctness of extraction, no index privacy (hiding of the weights); nothing on any program.
Terms: lean/GLOSSARY.md, and "Words" in the head of Johnson/Bind/Cpp/Defs.lean.

-/
import Johnson.Bind.CoreValue
import Johnson.Bind.TwinTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Core
open Bind.Twin
open Fmt (Ext)

/-! ### The running committer at the identity monad -/

section Runs
variable (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → Id ByteArray) (sh : Shape) (cfg : ByteArray)

/-- The OOD seeds that the running committer samples at a root. -/
def seedsId (root : ByteArray) : List (List Ext × Ext) := Id.run (seedsW h sh (nameOf sh root cfg))

/-- The commitment ID's text at a root, seeds and answers. -/
def idId (root : ByteArray) (seeds : List (List Ext × Ext)) (given : List Ext) : ByteArray :=
  Id.run (Fmt.publishedIDW h cfg (nameOf sh root cfg) (Fmt.flatSeeds seeds) given [])

/-- The running committer's root. -/
def rootId (col : ℕ → List UInt64) (salt : ℕ → ByteArray) : ByteArray :=
  Id.run (rootW h sh cfg (fun _ => cfg) col salt)

/-- **The running committer behind cfg, field by field.** -/
theorem coreW_id (col : ℕ → List UInt64) (T : Table) :
    Id.run (coreW h sh cfg col T) =
      ⟨rootId h sh cfg col T.salt, nameOf sh (rootId h sh cfg col T.salt) cfg,
        seedsId h sh cfg (rootId h sh cfg col T.salt),
        answers sh T (seedsId h sh cfg (rootId h sh cfg col T.salt)),
        idId h sh cfg (rootId h sh cfg col T.salt) (seedsId h sh cfg (rootId h sh cfg col T.salt))
          (answers sh T (seedsId h sh cfg (rootId h sh cfg col T.salt)))⟩ := rfl

end Runs

end Bind.Core

noncomputable section

namespace Bind.Core
open Rom Bind.Twin
open Fmt (Ext)
open _root_.Compile (levelsF rootOf)
open TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (F : Fam (typedOracleFamily lam W.K (typedOracleCarrier L Bd aT aL)))
  (h : ℕ → ℕ → ℕ → ByteArray → ByteArray → Id ByteArray) (sh : Bind.Twin.Shape) (cfg : ByteArray)
  (sp : Dig lam → ByteArray) (spS : L.OutOfDomainSeed → List (List Ext × Ext)) (spA : L.OutOfDomainAnswer → List Ext)

/-! ### The premises -/

/-- **What is owed of the tree's single queries**, at a word y with salts σ on the typed side and at
columns col with salts salt on the running side. -/
structure TreeSpells (b₀ : Bd) (y : Fin L.wordLength → L.Symbol) (σ : ℕ → Bits) (col : ℕ → List UInt64)
    (salt : ℕ → ByteArray) : Prop where
  /-- The two trees have one depth. -/
  depth : W.depth = sh.a
  /-- A leaf's typed answer, spelled, is the running committer's leaf at that position. -/
  leaf : ∀ j, j < 2 ^ sh.a →
    sp (leafF W F (committerLeafInput W b₀ y σ j)) = leafId h sh (fun _ => cfg) col salt j
  /-- A node's typed answer, spelled, is the format's vertex at the spelled children. -/
  node : ∀ a b, sp (nodeF W F a b) = vertexId h cfg (sp a) (sp b)

/-- **What is owed of the seed's two queries**: at every root the typed seed, spelled, is what
the running committer samples from the table's name at the spelled root. -/
def SeedSpells : Prop := ∀ root : Dig lam, spS (seedF W S F root) = seedsId h sh cfg (sp root)

/-- **What is owed of the answers**, at an index, its encoding randomness and a table: at every seed
the written answers, spelled, are the running committer's at the spelled seed. No hash function, no
query and no string is named. -/
def AnsSpells (i : I) (r : L.EncodingRandomness) (T : Table) : Prop :=
  ∀ sd : L.OutOfDomainSeed, spA (L.honestOutOfDomainAnswer i r sd) = answers sh T (spS sd)

/-! ### The joint -/

variable {W F h sh cfg sp}

/-- **The root.** -/
theorem root_spelled {b₀ : Bd} {y : Fin L.wordLength → L.Symbol} {σ : ℕ → Bits} {col : ℕ → List UInt64}
    {salt : ℕ → ByteArray} (H : TreeSpells W F h sh cfg sp b₀ y σ col salt) :
    sp (rootF W F b₀ y σ) = rootId h sh cfg col salt := by
  have hne : leavesF W F b₀ y σ ≠ [] := by
    intro e
    have hl := congrArg List.length e
    unfold leavesF at hl
    rw [List.length_map, List.length_range, List.length_nil] at hl
    exact absurd hl (Nat.pos_iff_ne_zero.1 (Nat.pow_pos (by decide)))
  unfold rootF rootId
  rw [rootW_id, ← rootOf_levelsF_map (nodeF W F) (vertexId h cfg) sp H.node W.depth _ hne, H.depth]
  unfold leavesF
  rw [List.map_map, H.depth]
  refine congrArg (fun l => rootOf (levelsF (vertexId h cfg) sh.a l)) ?_
  exact List.map_congr_left fun j hj => H.leaf j (List.mem_range.1 hj)

variable {S spS spA}

/-- **THE KEY, SPELLED, IS WHAT THE RUNNING COMMITTER COMPUTES**: the root, the OOD seeds and the
OOD answers. -/
theorem key_spelled {b₀ : Bd} {i : I} {r : L.EncodingRandomness} {σ : ℕ → Bits} {col : ℕ → List UInt64} {T : Table}
    (Ht : TreeSpells W F h sh cfg sp b₀ (L.encodeIndex i r) σ col T.salt)
    (Hs : SeedSpells W S F h sh cfg sp spS) (Ha : AnsSpells sh spS spA i r T) :
    sp (keyF W S F b₀ i r σ).cm = (Id.run (coreW h sh cfg col T)).root ∧
      spS (keyF W S F b₀ i r σ).rcd.1 = (Id.run (coreW h sh cfg col T)).seeds ∧
      spA (keyF W S F b₀ i r σ).rcd.2 = (Id.run (coreW h sh cfg col T)).answers := by
  have h1 : sp (keyF W S F b₀ i r σ).cm = rootId h sh cfg col T.salt := root_spelled Ht
  have h2 : spS (keyF W S F b₀ i r σ).rcd.1 = seedsId h sh cfg (rootId h sh cfg col T.salt) := by
    rw [← h1]
    exact Hs _
  have h3 : spA (keyF W S F b₀ i r σ).rcd.2 =
      answers sh T (seedsId h sh cfg (rootId h sh cfg col T.salt)) := by
    rw [← h2]
    exact Ha _
  rw [coreW_id]
  exact ⟨h1, h2, h3⟩

/-- **THE ID.** A function of the typed key that at every key is a reading `rd` of the format's ID
at the spelled key gives, at the written committer's key, that reading of the running committer's
ID. -/
theorem id_spelled {C : Type} {b₀ : Bd} {i : I} {r : L.EncodingRandomness} {σ : ℕ → Bits} {col : ℕ → List UInt64}
    {T : Table} (Ht : TreeSpells W F h sh cfg sp b₀ (L.encodeIndex i r) σ col T.salt)
    (Hs : SeedSpells W S F h sh cfg sp spS) (Ha : AnsSpells sh spS spA i r T)
    (idOf : KeyRoot lam L → C) (rd : ByteArray → C)
    (Hi : ∀ k : KeyRoot lam L, idOf k = rd (idId h sh cfg (sp k.cm) (spS k.rcd.1) (spA k.rcd.2))) :
    idOf (keyF W S F b₀ i r σ) = rd (Id.run (coreW h sh cfg col T)).id := by
  obtain ⟨h1, h2, h3⟩ := key_spelled Ht Hs Ha
  rw [Hi, h1, h2, h3]
  rfl

end Bind.Core

end

#print axioms Bind.Core.coreW_id
#print axioms Bind.Core.root_spelled
#print axioms Bind.Core.key_spelled
#print axioms Bind.Core.id_spelled
